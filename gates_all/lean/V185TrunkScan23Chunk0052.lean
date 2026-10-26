import V185TrunkScan23Chunk0051

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_307507 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 4]
def baseStart_307507 : Nat := 118140960795 + 307507 * 2 ^ 59
def prefixEnd_307507 : Nat := 4983230072969 + 3 ^ 40 * 307507 * 2
def baseEnd_307507 : Nat := 157898895622233611148307

theorem tailTrace_307507 : CollatzResearch.WordTrace tailWord_307507 prefixEnd_307507 157898895622233611148307 := by
  unfold tailWord_307507
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215701696962131859536775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7477134464641421239691183 11215701696962131859536775)
  ·
    refine ⟨16823552545443197789305163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11215701696962131859536775 16823552545443197789305163)
    ·
      refine ⟨25235328818164796683957745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823552545443197789305163 25235328818164796683957745)
      ·
        refine ⟨18926496613623597512968309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25235328818164796683957745 18926496613623597512968309)
        ·
          refine ⟨1774359057527212266840779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18926496613623597512968309 1774359057527212266840779)
          ·
            refine ⟨2661538586290818400261169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774359057527212266840779 2661538586290818400261169)
            ·
              refine ⟨1996153939718113800195877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661538586290818400261169 1996153939718113800195877)
              ·
                refine ⟨374278863697146337536727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1996153939718113800195877 374278863697146337536727)
                ·
                  refine ⟨561418295545719506305091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374278863697146337536727 561418295545719506305091)
                  ·
                    refine ⟨842127443318579259457637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 561418295545719506305091 842127443318579259457637)
                    ·
                      refine ⟨157898895622233611148307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 842127443318579259457637 157898895622233611148307)
                      ·
                        rfl

theorem cell23_307507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_307507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307507 prefixEnd_307507 := by exact prefixLift 307507
  have htrace : WordTrace (prefixWord ++ tailWord_307507) baseStart_307507 baseEnd_307507 := by
    simpa [prefixWord, tailWord_307507, baseEnd_307507] using wordTrace_append hprefix tailTrace_307507
  have hstable : (prefixWord ++ tailWord_307507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307507).length < 2 ^ (prefixWord ++ tailWord_307507).sum := by decide
  have hdescent : baseEnd_307507 < baseStart_307507 := by decide
  rcases family_descends (prefixWord ++ tailWord_307507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307518 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_307518 : Nat := 118140960795 + 307518 * 2 ^ 59
def prefixEnd_307518 : Nat := 4983230072969 + 3 ^ 40 * 307518 * 2
def baseEnd_307518 : Nat := 157904543909433068110757

theorem tailTrace_307518 : CollatzResearch.WordTrace tailWord_307518 prefixEnd_307518 157904543909433068110757 := by
  unfold tailWord_307518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402012862490285092273401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7477401933281520492124805 1402012862490285092273401)
  ·
    refine ⟨1051509646867713819205051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1402012862490285092273401 1051509646867713819205051)
    ·
      refine ⟨1577264470301570728807577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051509646867713819205051 1577264470301570728807577)
      ·
        refine ⟨1182948352726178046605683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577264470301570728807577 1182948352726178046605683)
        ·
          refine ⟨1774422529089267069908525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182948352726178046605683 1774422529089267069908525)
          ·
            refine ⟨665408448408475151215697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1774422529089267069908525 665408448408475151215697)
            ·
              refine ⟨499056336306356363411773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665408448408475151215697 499056336306356363411773)
              ·
                refine ⟨187146126114883636279415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499056336306356363411773 187146126114883636279415)
                ·
                  refine ⟨280719189172325454419123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187146126114883636279415 280719189172325454419123)
                  ·
                    refine ⟨421078783758488181628685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280719189172325454419123 421078783758488181628685)
                    ·
                      refine ⟨157904543909433068110757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421078783758488181628685 157904543909433068110757)
                      ·
                        rfl

theorem cell23_307518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_307518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307518 prefixEnd_307518 := by exact prefixLift 307518
  have htrace : WordTrace (prefixWord ++ tailWord_307518) baseStart_307518 baseEnd_307518 := by
    simpa [prefixWord, tailWord_307518, baseEnd_307518] using wordTrace_append hprefix tailTrace_307518
  have hstable : (prefixWord ++ tailWord_307518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307518).length < 2 ^ (prefixWord ++ tailWord_307518).sum := by decide
  have hdescent : baseEnd_307518 < baseStart_307518 := by decide
  rcases family_descends (prefixWord ++ tailWord_307518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307520 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_307520 : Nat := 118140960795 + 307520 * 2 ^ 59
def prefixEnd_307520 : Nat := 4983230072969 + 3 ^ 40 * 307520 * 2
def baseEnd_307520 : Nat := 157905570870742060285747

theorem tailTrace_307520 : CollatzResearch.WordTrace tailWord_307520 prefixEnd_307520 157905570870742060285747 := by
  unfold tailWord_307520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608087922957517539880007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7477450563943356719840009 5608087922957517539880007)
  ·
    refine ⟨8412131884436276309820011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5608087922957517539880007 8412131884436276309820011)
    ·
      refine ⟨12618197826654414464730017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8412131884436276309820011 12618197826654414464730017)
      ·
        refine ⟨9463648369990810848547513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12618197826654414464730017 9463648369990810848547513)
        ·
          refine ⟨7097736277493108136410635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9463648369990810848547513 7097736277493108136410635)
          ·
            refine ⟨10646604416239662204615953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097736277493108136410635 10646604416239662204615953)
            ·
              refine ⟨7984953312179746653461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10646604416239662204615953 7984953312179746653461965)
              ·
                refine ⟨2994357492067404995048237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7984953312179746653461965 2994357492067404995048237)
                ·
                  refine ⟨1122884059525276873143089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2994357492067404995048237 1122884059525276873143089)
                  ·
                    refine ⟨842163044643957654857317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122884059525276873143089 842163044643957654857317)
                    ·
                      refine ⟨157905570870742060285747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 842163044643957654857317 157905570870742060285747)
                      ·
                        rfl

theorem cell23_307520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_307520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307520 prefixEnd_307520 := by exact prefixLift 307520
  have htrace : WordTrace (prefixWord ++ tailWord_307520) baseStart_307520 baseEnd_307520 := by
    simpa [prefixWord, tailWord_307520, baseEnd_307520] using wordTrace_append hprefix tailTrace_307520
  have hstable : (prefixWord ++ tailWord_307520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307520).length < 2 ^ (prefixWord ++ tailWord_307520).sum := by decide
  have hdescent : baseEnd_307520 < baseStart_307520 := by decide
  rcases family_descends (prefixWord ++ tailWord_307520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307554 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_307554 : Nat := 118140960795 + 307554 * 2 ^ 59
def prefixEnd_307554 : Nat := 4983230072969 + 3 ^ 40 * 307554 * 2
def baseEnd_307554 : Nat := 157923029212994927260591

theorem tailTrace_307554 : CollatzResearch.WordTrace tailWord_307554 prefixEnd_307554 157923029212994927260591 := by
  unfold tailWord_307554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804353981947964721624429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7478277285194572590998477 2804353981947964721624429)
  ·
    refine ⟨1051632743230486770609161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2804353981947964721624429 1051632743230486770609161)
    ·
      refine ⟨788724557422865077956871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1051632743230486770609161 788724557422865077956871)
      ·
        refine ⟨1183086836134297616935307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788724557422865077956871 1183086836134297616935307)
        ·
          refine ⟨1774630254201446425402961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183086836134297616935307 1774630254201446425402961)
          ·
            refine ⟨1330972690651084819052221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1774630254201446425402961 1330972690651084819052221)
            ·
              refine ⟨499114758994156807144583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1330972690651084819052221 499114758994156807144583)
              ·
                refine ⟨748672138491235210716875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499114758994156807144583 748672138491235210716875)
                ·
                  refine ⟨1123008207736852816075313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748672138491235210716875 1123008207736852816075313)
                  ·
                    refine ⟨842256155802639612056485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1123008207736852816075313 842256155802639612056485)
                    ·
                      refine ⟨157923029212994927260591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 842256155802639612056485 157923029212994927260591)
                      ·
                        rfl

theorem cell23_307554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_307554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307554 prefixEnd_307554 := by exact prefixLift 307554
  have htrace : WordTrace (prefixWord ++ tailWord_307554) baseStart_307554 baseEnd_307554 := by
    simpa [prefixWord, tailWord_307554, baseEnd_307554] using wordTrace_append hprefix tailTrace_307554
  have hstable : (prefixWord ++ tailWord_307554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307554).length < 2 ^ (prefixWord ++ tailWord_307554).sum := by decide
  have hdescent : baseEnd_307554 < baseStart_307554 := by decide
  rcases family_descends (prefixWord ++ tailWord_307554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307564 : List Nat := [2, 2, 1, 1, 6, 2, 2, 7]
def baseStart_307564 : Nat := 118140960795 + 307564 * 2 ^ 59
def prefixEnd_307564 : Nat := 4983230072969 + 3 ^ 40 * 307564 * 2
def baseEnd_307564 : Nat := 5849191259982958819835

theorem tailTrace_307564 : CollatzResearch.WordTrace tailWord_307564 prefixEnd_307564 5849191259982958819835 := by
  unfold tailWord_307564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608890328877815297180873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7478520438503753729574497 5608890328877815297180873)
  ·
    refine ⟨4206667746658361472885655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5608890328877815297180873 4206667746658361472885655)
    ·
      refine ⟨6310001619987542209328483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206667746658361472885655 6310001619987542209328483)
      ·
        refine ⟨9465002429981313313992725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310001619987542209328483 9465002429981313313992725)
        ·
          refine ⟨443671988905374061593409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9465002429981313313992725 443671988905374061593409)
          ·
            refine ⟨332753991679030546195057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443671988905374061593409 332753991679030546195057)
            ·
              refine ⟨249565493759272909646293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332753991679030546195057 249565493759272909646293)
              ·
                refine ⟨5849191259982958819835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249565493759272909646293 5849191259982958819835)
                ·
                  rfl

theorem cell23_307564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 7].length) (baseStart_307564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307564 prefixEnd_307564 := by exact prefixLift 307564
  have htrace : WordTrace (prefixWord ++ tailWord_307564) baseStart_307564 baseEnd_307564 := by
    simpa [prefixWord, tailWord_307564, baseEnd_307564] using wordTrace_append hprefix tailTrace_307564
  have hstable : (prefixWord ++ tailWord_307564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307564).length < 2 ^ (prefixWord ++ tailWord_307564).sum := by decide
  have hdescent : baseEnd_307564 < baseStart_307564 := by decide
  rcases family_descends (prefixWord ++ tailWord_307564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307608 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_307608 : Nat := 118140960795 + 307608 * 2 ^ 59
def prefixEnd_307608 : Nat := 4983230072969 + 3 ^ 40 * 307608 * 2
def baseEnd_307608 : Nat := 157950757168337715985343

theorem tailTrace_307608 : CollatzResearch.WordTrace tailWord_307608 prefixEnd_307608 157950757168337715985343 := by
  unfold tailWord_307608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609692734798113054481739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7479590313064150739308985 5609692734798113054481739)
  ·
    refine ⟨8414539102197169581722609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5609692734798113054481739 8414539102197169581722609)
    ·
      refine ⟨6310904326647877186291957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8414539102197169581722609 6310904326647877186291957)
      ·
        refine ⟨591647280623238486214871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6310904326647877186291957 591647280623238486214871)
        ·
          refine ⟨887470920934857729322307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591647280623238486214871 887470920934857729322307)
          ·
            refine ⟨1331206381402286593983461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887470920934857729322307 1331206381402286593983461)
            ·
              refine ⟨249601196512928736371899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1331206381402286593983461 249601196512928736371899)
              ·
                refine ⟨374401794769393104557849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249601196512928736371899 374401794769393104557849)
                ·
                  refine ⟨280801346077044828418387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374401794769393104557849 280801346077044828418387)
                  ·
                    refine ⟨421202019115567242627581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280801346077044828418387 421202019115567242627581)
                    ·
                      refine ⟨157950757168337715985343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421202019115567242627581 157950757168337715985343)
                      ·
                        rfl

theorem cell23_307608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_307608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307608 prefixEnd_307608 := by exact prefixLift 307608
  have htrace : WordTrace (prefixWord ++ tailWord_307608) baseStart_307608 baseEnd_307608 := by
    simpa [prefixWord, tailWord_307608, baseEnd_307608] using wordTrace_append hprefix tailTrace_307608
  have hstable : (prefixWord ++ tailWord_307608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307608).length < 2 ^ (prefixWord ++ tailWord_307608).sum := by decide
  have hdescent : baseEnd_307608 < baseStart_307608 := by decide
  rcases family_descends (prefixWord ++ tailWord_307608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307674 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_307674 : Nat := 118140960795 + 307674 * 2 ^ 59
def prefixEnd_307674 : Nat := 4983230072969 + 3 ^ 40 * 307674 * 2
def baseEnd_307674 : Nat := 157984646891534457760039

theorem tailTrace_307674 : CollatzResearch.WordTrace tailWord_307674 prefixEnd_307674 157984646891534457760039 := by
  unfold tailWord_307674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805448171839279845216519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7481195124904746253910717 2805448171839279845216519)
  ·
    refine ⟨4208172257758919767824779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805448171839279845216519 4208172257758919767824779)
    ·
      refine ⟨6312258386638379651737169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208172257758919767824779 6312258386638379651737169)
      ·
        refine ⟨4734193789978784738802877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6312258386638379651737169 4734193789978784738802877)
        ·
          refine ⟨1775322671242044277051079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4734193789978784738802877 1775322671242044277051079)
          ·
            refine ⟨2662984006863066415576619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775322671242044277051079 2662984006863066415576619)
            ·
              refine ⟨3994476010294599623364929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662984006863066415576619 3994476010294599623364929)
              ·
                refine ⟨2995857007720949717523697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994476010294599623364929 2995857007720949717523697)
                ·
                  refine ⟨2246892755790712288142773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2995857007720949717523697 2246892755790712288142773)
                  ·
                    refine ⟨210646195855379277013385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2246892755790712288142773 210646195855379277013385)
                    ·
                      refine ⟨157984646891534457760039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210646195855379277013385 157984646891534457760039)
                      ·
                        rfl

theorem cell23_307674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_307674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307674 prefixEnd_307674 := by exact prefixLift 307674
  have htrace : WordTrace (prefixWord ++ tailWord_307674) baseStart_307674 baseEnd_307674 := by
    simpa [prefixWord, tailWord_307674, baseEnd_307674] using wordTrace_append hprefix tailTrace_307674
  have hstable : (prefixWord ++ tailWord_307674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307674).length < 2 ^ (prefixWord ++ tailWord_307674).sum := by decide
  have hdescent : baseEnd_307674 < baseStart_307674 := by decide
  rcases family_descends (prefixWord ++ tailWord_307674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307704 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_307704 : Nat := 118140960795 + 307704 * 2 ^ 59
def prefixEnd_307704 : Nat := 4983230072969 + 3 ^ 40 * 307704 * 2
def baseEnd_307704 : Nat := 158000051311169340384901

theorem tailTrace_307704 : CollatzResearch.WordTrace tailWord_307704 prefixEnd_307704 158000051311169340384901 := by
  unfold tailWord_307704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611443438624217252229083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7481924584832289669638777 5611443438624217252229083)
  ·
    refine ⟨8417165157936325878343625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5611443438624217252229083 8417165157936325878343625)
    ·
      refine ⟨6312873868452244408757719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8417165157936325878343625 6312873868452244408757719)
      ·
        refine ⟨9469310802678366613136579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6312873868452244408757719 9469310802678366613136579)
        ·
          refine ⟨14203966204017549919704869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9469310802678366613136579 14203966204017549919704869)
          ·
            refine ⟨2663243663253290609944663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14203966204017549919704869 2663243663253290609944663)
            ·
              refine ⟨3994865494879935914916995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663243663253290609944663 3994865494879935914916995)
              ·
                refine ⟨5992298242319903872375493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994865494879935914916995 5992298242319903872375493)
                ·
                  refine ⟨1123555920434981976070405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5992298242319903872375493 1123555920434981976070405)
                  ·
                    refine ⟨210666735081559120513201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123555920434981976070405 210666735081559120513201)
                    ·
                      refine ⟨158000051311169340384901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210666735081559120513201 158000051311169340384901)
                      ·
                        rfl

theorem cell23_307704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_307704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307704 prefixEnd_307704 := by exact prefixLift 307704
  have htrace : WordTrace (prefixWord ++ tailWord_307704) baseStart_307704 baseEnd_307704 := by
    simpa [prefixWord, tailWord_307704, baseEnd_307704] using wordTrace_append hprefix tailTrace_307704
  have hstable : (prefixWord ++ tailWord_307704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307704).length < 2 ^ (prefixWord ++ tailWord_307704).sum := by decide
  have hdescent : baseEnd_307704 < baseStart_307704 := by decide
  rcases family_descends (prefixWord ++ tailWord_307704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307707 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3]
def baseStart_307707 : Nat := 118140960795 + 307707 * 2 ^ 59
def prefixEnd_307707 : Nat := 4983230072969 + 3 ^ 40 * 307707 * 2
def baseEnd_307707 : Nat := 158001591753132828647387

theorem tailTrace_307707 : CollatzResearch.WordTrace tailWord_307707 prefixEnd_307707 158001591753132828647387 := by
  unfold tailWord_307707
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222996296237566016817375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7481997530825044011211583 11222996296237566016817375)
  ·
    refine ⟨16834494444356349025226063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11222996296237566016817375 16834494444356349025226063)
    ·
      refine ⟨25251741666534523537839095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16834494444356349025226063 25251741666534523537839095)
      ·
        refine ⟨37877612499801785306758643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25251741666534523537839095 37877612499801785306758643)
        ·
          refine ⟨56816418749702677960137965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37877612499801785306758643 56816418749702677960137965)
          ·
            refine ⟨21306157031138504235051737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56816418749702677960137965 21306157031138504235051737)
            ·
              refine ⟨15979617773353878176288803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21306157031138504235051737 15979617773353878176288803)
              ·
                refine ⟨23969426660030817264433205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15979617773353878176288803 23969426660030817264433205)
                ·
                  refine ⟨2247133749377889118540613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23969426660030817264433205 2247133749377889118540613)
                  ·
                    refine ⟨421337578008354209726365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247133749377889118540613 421337578008354209726365)
                    ·
                      refine ⟨158001591753132828647387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421337578008354209726365 158001591753132828647387)
                      ·
                        rfl

theorem cell23_307707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3].length) (baseStart_307707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307707 prefixEnd_307707 := by exact prefixLift 307707
  have htrace : WordTrace (prefixWord ++ tailWord_307707) baseStart_307707 baseEnd_307707 := by
    simpa [prefixWord, tailWord_307707, baseEnd_307707] using wordTrace_append hprefix tailTrace_307707
  have hstable : (prefixWord ++ tailWord_307707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307707).length < 2 ^ (prefixWord ++ tailWord_307707).sum := by decide
  have hdescent : baseEnd_307707 < baseStart_307707 := by decide
  rcases family_descends (prefixWord ++ tailWord_307707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307718 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_307718 : Nat := 118140960795 + 307718 * 2 ^ 59
def prefixEnd_307718 : Nat := 4983230072969 + 3 ^ 40 * 307718 * 2
def baseEnd_307718 : Nat := 52669080013444095203279

theorem tailTrace_307718 : CollatzResearch.WordTrace tailWord_307718 prefixEnd_307718 52669080013444095203279 := by
  unfold tailWord_307718
  simp only [CollatzResearch.WordTrace]
  refine ⟨350731171849928590483369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7482264999465143263645205 350731171849928590483369)
  ·
    refine ⟨263048378887446442862527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350731171849928590483369 263048378887446442862527)
    ·
      refine ⟨394572568331169664293791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263048378887446442862527 394572568331169664293791)
      ·
        refine ⟨591858852496754496440687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394572568331169664293791 591858852496754496440687)
        ·
          refine ⟨887788278745131744661031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591858852496754496440687 887788278745131744661031)
          ·
            refine ⟨1331682418117697616991547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887788278745131744661031 1331682418117697616991547)
            ·
              refine ⟨1997523627176546425487321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331682418117697616991547 1997523627176546425487321)
              ·
                refine ⟨1498142720382409819115491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997523627176546425487321 1498142720382409819115491)
                ·
                  refine ⟨2247214080573614728673237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498142720382409819115491 2247214080573614728673237)
                  ·
                    refine ⟨52669080013444095203279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2247214080573614728673237 52669080013444095203279)
                    ·
                      rfl

theorem cell23_307718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_307718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307718 prefixEnd_307718 := by exact prefixLift 307718
  have htrace : WordTrace (prefixWord ++ tailWord_307718) baseStart_307718 baseEnd_307718 := by
    simpa [prefixWord, tailWord_307718, baseEnd_307718] using wordTrace_append hprefix tailTrace_307718
  have hstable : (prefixWord ++ tailWord_307718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307718).length < 2 ^ (prefixWord ++ tailWord_307718).sum := by decide
  have hdescent : baseEnd_307718 < baseStart_307718 := by decide
  rcases family_descends (prefixWord ++ tailWord_307718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307724 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_307724 : Nat := 118140960795 + 307724 * 2 ^ 59
def prefixEnd_307724 : Nat := 4983230072969 + 3 ^ 40 * 307724 * 2
def baseEnd_307724 : Nat := 158010320924259262134809

theorem tailTrace_307724 : CollatzResearch.WordTrace tailWord_307724 prefixEnd_307724 158010320924259262134809 := by
  unfold tailWord_307724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611808168587988960093113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7482410891450651946790817 5611808168587988960093113)
  ·
    refine ⟨4208856126440991720069835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5611808168587988960093113 4208856126440991720069835)
    ·
      refine ⟨6313284189661487580104753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208856126440991720069835 6313284189661487580104753)
      ·
        refine ⟨4734963142246115685078565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6313284189661487580104753 4734963142246115685078565)
        ·
          refine ⟨887805589171146690952231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4734963142246115685078565 887805589171146690952231)
          ·
            refine ⟨1331708383756720036428347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887805589171146690952231 1331708383756720036428347)
            ·
              refine ⟨1997562575635080054642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331708383756720036428347 1997562575635080054642521)
              ·
                refine ⟨1498171931726310040981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997562575635080054642521 1498171931726310040981891)
                ·
                  refine ⟨2247257897589465061472837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498171931726310040981891 2247257897589465061472837)
                  ·
                    refine ⟨421360855798024699026157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247257897589465061472837 421360855798024699026157)
                    ·
                      refine ⟨158010320924259262134809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421360855798024699026157 158010320924259262134809)
                      ·
                        rfl

theorem cell23_307724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_307724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307724 prefixEnd_307724 := by exact prefixLift 307724
  have htrace : WordTrace (prefixWord ++ tailWord_307724) baseStart_307724 baseEnd_307724 := by
    simpa [prefixWord, tailWord_307724, baseEnd_307724] using wordTrace_append hprefix tailTrace_307724
  have hstable : (prefixWord ++ tailWord_307724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307724).length < 2 ^ (prefixWord ++ tailWord_307724).sum := by decide
  have hdescent : baseEnd_307724 < baseStart_307724 := by decide
  rcases family_descends (prefixWord ++ tailWord_307724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307758 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_307758 : Nat := 118140960795 + 307758 * 2 ^ 59
def prefixEnd_307758 : Nat := 4983230072969 + 3 ^ 40 * 307758 * 2
def baseEnd_307758 : Nat := 158027779266512129109653

theorem tailTrace_307758 : CollatzResearch.WordTrace tailWord_307758 prefixEnd_307758 158027779266512129109653 := by
  unfold tailWord_307758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403107052381600215865491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7483237612701867817949285 1403107052381600215865491)
  ·
    refine ⟨2104660578572400323798237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403107052381600215865491 2104660578572400323798237)
    ·
      refine ⟨789247716964650121424339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2104660578572400323798237 789247716964650121424339)
      ·
        refine ⟨1183871575446975182136509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789247716964650121424339 1183871575446975182136509)
        ·
          refine ⟨443951840792615693301191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1183871575446975182136509 443951840792615693301191)
          ·
            refine ⟨665927761188923539951787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443951840792615693301191 665927761188923539951787)
            ·
              refine ⟨998891641783385309927681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665927761188923539951787 998891641783385309927681)
              ·
                refine ⟨749168731337538982445761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998891641783385309927681 749168731337538982445761)
                ·
                  refine ⟨561876548503154236834321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749168731337538982445761 561876548503154236834321)
                  ·
                    refine ⟨421407411377365677625741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 561876548503154236834321 421407411377365677625741)
                    ·
                      refine ⟨158027779266512129109653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421407411377365677625741 158027779266512129109653)
                      ·
                        rfl

theorem cell23_307758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_307758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307758 prefixEnd_307758 := by exact prefixLift 307758
  have htrace : WordTrace (prefixWord ++ tailWord_307758) baseStart_307758 baseEnd_307758 := by
    simpa [prefixWord, tailWord_307758, baseEnd_307758] using wordTrace_append hprefix tailTrace_307758
  have hstable : (prefixWord ++ tailWord_307758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307758).length < 2 ^ (prefixWord ++ tailWord_307758).sum := by decide
  have hdescent : baseEnd_307758 < baseStart_307758 := by decide
  rcases family_descends (prefixWord ++ tailWord_307758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307822 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_307822 : Nat := 118140960795 + 307822 * 2 ^ 59
def prefixEnd_307822 : Nat := 4983230072969 + 3 ^ 40 * 307822 * 2
def baseEnd_307822 : Nat := 158060642028399878709359

theorem tailTrace_307822 : CollatzResearch.WordTrace tailWord_307822 prefixEnd_307822 158060642028399878709359 := by
  unfold tailWord_307822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403398836352617582156715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7484793793880627104835813 1403398836352617582156715)
  ·
    refine ⟨2105098254528926373235073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403398836352617582156715 2105098254528926373235073)
    ·
      refine ⟨1578823690896694779926305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105098254528926373235073 1578823690896694779926305)
      ·
        refine ⟨1184117768172521084944729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1578823690896694779926305 1184117768172521084944729)
        ·
          refine ⟨888088326129390813708547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184117768172521084944729 888088326129390813708547)
          ·
            refine ⟨1332132489194086220562821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888088326129390813708547 1332132489194086220562821)
            ·
              refine ⟨249774841723891166355529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1332132489194086220562821 249774841723891166355529)
              ·
                refine ⟨187331131292918374766647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249774841723891166355529 187331131292918374766647)
                ·
                  refine ⟨280996696939377562149971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187331131292918374766647 280996696939377562149971)
                  ·
                    refine ⟨421495045409066343224957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280996696939377562149971 421495045409066343224957)
                    ·
                      refine ⟨158060642028399878709359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421495045409066343224957 158060642028399878709359)
                      ·
                        rfl

theorem cell23_307822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_307822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307822 prefixEnd_307822 := by exact prefixLift 307822
  have htrace : WordTrace (prefixWord ++ tailWord_307822) baseStart_307822 baseEnd_307822 := by
    simpa [prefixWord, tailWord_307822, baseEnd_307822] using wordTrace_append hprefix tailTrace_307822
  have hstable : (prefixWord ++ tailWord_307822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307822).length < 2 ^ (prefixWord ++ tailWord_307822).sum := by decide
  have hdescent : baseEnd_307822 < baseStart_307822 := by decide
  rcases family_descends (prefixWord ++ tailWord_307822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307827 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_307827 : Nat := 118140960795 + 307827 * 2 ^ 59
def prefixEnd_307827 : Nat := 4983230072969 + 3 ^ 40 * 307827 * 2
def baseEnd_307827 : Nat := 158063209431672359146835

theorem tailTrace_307827 : CollatzResearch.WordTrace tailWord_307827 prefixEnd_307827 158063209431672359146835 := by
  unfold tailWord_307827
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227373055802826511185735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7484915370535217674123823 11227373055802826511185735)
  ·
    refine ⟨16841059583704239766778603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11227373055802826511185735 16841059583704239766778603)
    ·
      refine ⟨25261589375556359650167905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16841059583704239766778603 25261589375556359650167905)
      ·
        refine ⟨18946192031667269737625929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25261589375556359650167905 18946192031667269737625929)
        ·
          refine ⟨14209644023750452303219447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18946192031667269737625929 14209644023750452303219447)
          ·
            refine ⟨21314466035625678454829171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209644023750452303219447 21314466035625678454829171)
            ·
              refine ⟨31971699053438517682243757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21314466035625678454829171 31971699053438517682243757)
              ·
                refine ⟨11989387145039444130841409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31971699053438517682243757 11989387145039444130841409)
                ·
                  refine ⟨8992040358779583098131057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11989387145039444130841409 8992040358779583098131057)
                  ·
                    refine ⟨6744030269084687323598293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8992040358779583098131057 6744030269084687323598293)
                    ·
                      refine ⟨158063209431672359146835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6744030269084687323598293 158063209431672359146835)
                      ·
                        rfl

theorem cell23_307827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_307827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307827 prefixEnd_307827 := by exact prefixLift 307827
  have htrace : WordTrace (prefixWord ++ tailWord_307827) baseStart_307827 baseEnd_307827 := by
    simpa [prefixWord, tailWord_307827, baseEnd_307827] using wordTrace_append hprefix tailTrace_307827
  have hstable : (prefixWord ++ tailWord_307827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307827).length < 2 ^ (prefixWord ++ tailWord_307827).sum := by decide
  have hdescent : baseEnd_307827 < baseStart_307827 := by decide
  rcases family_descends (prefixWord ++ tailWord_307827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307841 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_307841 : Nat := 118140960795 + 307841 * 2 ^ 59
def prefixEnd_307841 : Nat := 4983230072969 + 3 ^ 40 * 307841 * 2
def baseEnd_307841 : Nat := 158070398160835304371771

theorem tailTrace_307841 : CollatzResearch.WordTrace tailWord_307841 prefixEnd_307841 158070398160835304371771 := by
  unfold tailWord_307841
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227883677752106902195377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7485255785168071268130251 11227883677752106902195377)
  ·
    refine ⟨8420912758314080176646533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11227883677752106902195377 8420912758314080176646533)
    ·
      refine ⟨1578921142183890033121225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8420912758314080176646533 1578921142183890033121225)
      ·
        refine ⟨1184190856637917524840919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1578921142183890033121225 1184190856637917524840919)
        ·
          refine ⟨1776286284956876287261379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184190856637917524840919 1776286284956876287261379)
          ·
            refine ⟨2664429427435314430892069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776286284956876287261379 2664429427435314430892069)
            ·
              refine ⟨499580517644121455792263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2664429427435314430892069 499580517644121455792263)
              ·
                refine ⟨749370776466182183688395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499580517644121455792263 749370776466182183688395)
                ·
                  refine ⟨1124056164699273275532593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749370776466182183688395 1124056164699273275532593)
                  ·
                    refine ⟨843042123524454956649445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1124056164699273275532593 843042123524454956649445)
                    ·
                      refine ⟨158070398160835304371771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 843042123524454956649445 158070398160835304371771)
                      ·
                        rfl

theorem cell23_307841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_307841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307841 prefixEnd_307841 := by exact prefixLift 307841
  have htrace : WordTrace (prefixWord ++ tailWord_307841) baseStart_307841 baseEnd_307841 := by
    simpa [prefixWord, tailWord_307841, baseEnd_307841] using wordTrace_append hprefix tailTrace_307841
  have hstable : (prefixWord ++ tailWord_307841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307841).length < 2 ^ (prefixWord ++ tailWord_307841).sum := by decide
  have hdescent : baseEnd_307841 < baseStart_307841 := by decide
  rcases family_descends (prefixWord ++ tailWord_307841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307895 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_307895 : Nat := 118140960795 + 307895 * 2 ^ 59
def prefixEnd_307895 : Nat := 4983230072969 + 3 ^ 40 * 307895 * 2
def baseEnd_307895 : Nat := 158098126116178093096523

theorem tailTrace_307895 : CollatzResearch.WordTrace tailWord_307895 prefixEnd_307895 158098126116178093096523 := by
  unfold tailWord_307895
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229853219556474124661139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7486568813037649416440759 11229853219556474124661139)
  ·
    refine ⟨16844779829334711186991709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11229853219556474124661139 16844779829334711186991709)
    ·
      refine ⟨6316792436000516695121891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16844779829334711186991709 6316792436000516695121891)
      ·
        refine ⟨9475188654000775042682837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6316792436000516695121891 9475188654000775042682837)
        ·
          refine ⟨222074734078143165062879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9475188654000775042682837 222074734078143165062879)
          ·
            refine ⟨333112101117214747594319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222074734078143165062879 333112101117214747594319)
            ·
              refine ⟨499668151675822121391479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333112101117214747594319 499668151675822121391479)
              ·
                refine ⟨749502227513733182087219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499668151675822121391479 749502227513733182087219)
                ·
                  refine ⟨1124253341270599773130829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749502227513733182087219 1124253341270599773130829)
                  ·
                    refine ⟨421595002976474914924061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124253341270599773130829 421595002976474914924061)
                    ·
                      refine ⟨158098126116178093096523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421595002976474914924061 158098126116178093096523)
                      ·
                        rfl

theorem cell23_307895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_307895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307895 prefixEnd_307895 := by exact prefixLift 307895
  have htrace : WordTrace (prefixWord ++ tailWord_307895) baseStart_307895 baseEnd_307895 := by
    simpa [prefixWord, tailWord_307895, baseEnd_307895] using wordTrace_append hprefix tailTrace_307895
  have hstable : (prefixWord ++ tailWord_307895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307895).length < 2 ^ (prefixWord ++ tailWord_307895).sum := by decide
  have hdescent : baseEnd_307895 < baseStart_307895 := by decide
  rcases family_descends (prefixWord ++ tailWord_307895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307941 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 7]
def baseStart_307941 : Nat := 118140960795 + 307941 * 2 ^ 59
def prefixEnd_307941 : Nat := 4983230072969 + 3 ^ 40 * 307941 * 2
def baseEnd_307941 : Nat := 17569082914031657013479

theorem tailTrace_307941 : CollatzResearch.WordTrace tailWord_307941 prefixEnd_307941 17569082914031657013479 := by
  unfold tailWord_307941
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231530977389823980835677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7487687318259882653890451 11231530977389823980835677)
  ·
    refine ⟨4211824116521183992813379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11231530977389823980835677 4211824116521183992813379)
    ·
      refine ⟨6317736174781775989220069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211824116521183992813379 6317736174781775989220069)
      ·
        refine ⟨1184575532771582997978763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6317736174781775989220069 1184575532771582997978763)
        ·
          refine ⟨1776863299157374496968145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184575532771582997978763 1776863299157374496968145)
          ·
            refine ⟨1332647474368030872726109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776863299157374496968145 1332647474368030872726109)
            ·
              refine ⟨499742802888011577272291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1332647474368030872726109 499742802888011577272291)
              ·
                refine ⟨749614204332017365908437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499742802888011577272291 749614204332017365908437)
                ·
                  refine ⟨17569082914031657013479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 749614204332017365908437 17569082914031657013479)
                  ·
                    rfl

theorem cell23_307941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_307941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307941 prefixEnd_307941 := by exact prefixLift 307941
  have htrace : WordTrace (prefixWord ++ tailWord_307941) baseStart_307941 baseEnd_307941 := by
    simpa [prefixWord, tailWord_307941, baseEnd_307941] using wordTrace_append hprefix tailTrace_307941
  have hstable : (prefixWord ++ tailWord_307941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307941).length < 2 ^ (prefixWord ++ tailWord_307941).sum := by decide
  have hdescent : baseEnd_307941 < baseStart_307941 := by decide
  rcases family_descends (prefixWord ++ tailWord_307941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307956 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_307956 : Nat := 118140960795 + 307956 * 2 ^ 59
def prefixEnd_307956 : Nat := 4983230072969 + 3 ^ 40 * 307956 * 2
def baseEnd_307956 : Nat := 158129448436102354433743

theorem tailTrace_307956 : CollatzResearch.WordTrace tailWord_307956 prefixEnd_307956 158129448436102354433743 := by
  unfold tailWord_307956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616039036167740771315861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7488052048223654361754481 5616039036167740771315861)
  ·
    refine ⟨263251829820362848655431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5616039036167740771315861 263251829820362848655431)
    ·
      refine ⟨394877744730544272983147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263251829820362848655431 394877744730544272983147)
      ·
        refine ⟨592316617095816409474721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394877744730544272983147 592316617095816409474721)
        ·
          refine ⟨444237462821862307106041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592316617095816409474721 444237462821862307106041)
          ·
            refine ⟨333178097116396730329531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444237462821862307106041 333178097116396730329531)
            ·
              refine ⟨499767145674595095494297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333178097116396730329531 499767145674595095494297)
              ·
                refine ⟨374825359255946321620723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499767145674595095494297 374825359255946321620723)
                ·
                  refine ⟨562238038883919482431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374825359255946321620723 562238038883919482431085)
                  ·
                    refine ⟨210839264581469805911657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562238038883919482431085 210839264581469805911657)
                    ·
                      refine ⟨158129448436102354433743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210839264581469805911657 158129448436102354433743)
                      ·
                        rfl

theorem cell23_307956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_307956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_307956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_307956 prefixEnd_307956 := by exact prefixLift 307956
  have htrace : WordTrace (prefixWord ++ tailWord_307956) baseStart_307956 baseEnd_307956 := by
    simpa [prefixWord, tailWord_307956, baseEnd_307956] using wordTrace_append hprefix tailTrace_307956
  have hstable : (prefixWord ++ tailWord_307956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307956).length < 2 ^ (prefixWord ++ tailWord_307956).sum := by decide
  have hdescent : baseEnd_307956 < baseStart_307956 := by decide
  rcases family_descends (prefixWord ++ tailWord_307956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308011 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3]
def baseStart_308011 : Nat := 118140960795 + 308011 * 2 ^ 59
def prefixEnd_308011 : Nat := 4983230072969 + 3 ^ 40 * 308011 * 2
def baseEnd_308011 : Nat := 158157689872099639245989

theorem tailTrace_308011 : CollatzResearch.WordTrace tailWord_308011 prefixEnd_308011 158157689872099639245989 := by
  unfold tailWord_308011
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234084087136225935883887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7489389391424150623922591 11234084087136225935883887)
  ·
    refine ⟨16851126130704338903825831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11234084087136225935883887 16851126130704338903825831)
    ·
      refine ⟨25276689196056508355738747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16851126130704338903825831 25276689196056508355738747)
      ·
        refine ⟨37915033794084762533608121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25276689196056508355738747 37915033794084762533608121)
        ·
          refine ⟨28436275345563571900206091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37915033794084762533608121 28436275345563571900206091)
          ·
            refine ⟨42654413018345357850309137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28436275345563571900206091 42654413018345357850309137)
            ·
              refine ⟨31990809763759018387731853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42654413018345357850309137 31990809763759018387731853)
              ·
                refine ⟨11996553661409631895399445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31990809763759018387731853 11996553661409631895399445)
                ·
                  refine ⟨562338452878576495096849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11996553661409631895399445 562338452878576495096849)
                  ·
                    refine ⟨421753839658932371322637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 562338452878576495096849 421753839658932371322637)
                    ·
                      refine ⟨158157689872099639245989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421753839658932371322637 158157689872099639245989)
                      ·
                        rfl

theorem cell23_308011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3].length) (baseStart_308011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308011 prefixEnd_308011 := by exact prefixLift 308011
  have htrace : WordTrace (prefixWord ++ tailWord_308011) baseStart_308011 baseEnd_308011 := by
    simpa [prefixWord, tailWord_308011, baseEnd_308011] using wordTrace_append hprefix tailTrace_308011
  have hstable : (prefixWord ++ tailWord_308011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308011).length < 2 ^ (prefixWord ++ tailWord_308011).sum := by decide
  have hdescent : baseEnd_308011 < baseStart_308011 := by decide
  rcases family_descends (prefixWord ++ tailWord_308011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308018 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_308018 : Nat := 118140960795 + 308018 * 2 ^ 59
def prefixEnd_308018 : Nat := 4983230072969 + 3 ^ 40 * 308018 * 2
def baseEnd_308018 : Nat := 52720428078893703952819

theorem tailTrace_308018 : CollatzResearch.WordTrace tailWord_308018 prefixEnd_308018 52720428078893703952819 := by
  unfold tailWord_308018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808584849527716532847177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7489559598740577420925805 2808584849527716532847177)
  ·
    refine ⟨2106438637145787399635383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2808584849527716532847177 2106438637145787399635383)
    ·
      refine ⟨3159657955718681099453075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2106438637145787399635383 3159657955718681099453075)
      ·
        refine ⟨4739486933578021649179613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159657955718681099453075 4739486933578021649179613)
        ·
          refine ⟨1777307600091758118442355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4739486933578021649179613 1777307600091758118442355)
          ·
            refine ⟨2665961400137637177663533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777307600091758118442355 2665961400137637177663533)
            ·
              refine ⟨999735525051613941623825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2665961400137637177663533 999735525051613941623825)
              ·
                refine ⟨749801643788710456217869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999735525051613941623825 749801643788710456217869)
                ·
                  refine ⟨281175616420766421081701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749801643788710456217869 281175616420766421081701)
                  ·
                    refine ⟨52720428078893703952819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281175616420766421081701 52720428078893703952819)
                    ·
                      rfl

theorem cell23_308018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_308018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308018 prefixEnd_308018 := by exact prefixLift 308018
  have htrace : WordTrace (prefixWord ++ tailWord_308018) baseStart_308018 baseEnd_308018 := by
    simpa [prefixWord, tailWord_308018, baseEnd_308018] using wordTrace_append hprefix tailTrace_308018
  have hstable : (prefixWord ++ tailWord_308018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308018).length < 2 ^ (prefixWord ++ tailWord_308018).sum := by decide
  have hdescent : baseEnd_308018 < baseStart_308018 := by decide
  rcases family_descends (prefixWord ++ tailWord_308018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308022 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_308022 : Nat := 118140960795 + 308022 * 2 ^ 59
def prefixEnd_308022 : Nat := 4983230072969 + 3 ^ 40 * 308022 * 2
def baseEnd_308022 : Nat := 52721112719766365402813

theorem tailTrace_308022 : CollatzResearch.WordTrace tailWord_308022 prefixEnd_308022 52721112719766365402813 := by
  unfold tailWord_308022
  simp only [CollatzResearch.WordTrace]
  refine ⟨702155330631023425908395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7489656860064249876356213 702155330631023425908395)
  ·
    refine ⟨1053232995946535138862593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702155330631023425908395 1053232995946535138862593)
    ·
      refine ⟨789924746959901354146945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053232995946535138862593 789924746959901354146945)
      ·
        refine ⟨592443560219926015610209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 789924746959901354146945 592443560219926015610209)
        ·
          refine ⟨444332670164944511707657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592443560219926015610209 444332670164944511707657)
          ·
            refine ⟨333249502623708383780743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444332670164944511707657 333249502623708383780743)
            ·
              refine ⟨499874253935562575671115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333249502623708383780743 499874253935562575671115)
              ·
                refine ⟨749811380903343863506673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499874253935562575671115 749811380903343863506673)
                ·
                  refine ⟨562358535677507897630005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749811380903343863506673 562358535677507897630005)
                  ·
                    refine ⟨52721112719766365402813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 562358535677507897630005 52721112719766365402813)
                    ·
                      rfl

theorem cell23_308022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_308022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308022 prefixEnd_308022 := by exact prefixLift 308022
  have htrace : WordTrace (prefixWord ++ tailWord_308022) baseStart_308022 baseEnd_308022 := by
    simpa [prefixWord, tailWord_308022, baseEnd_308022] using wordTrace_append hprefix tailTrace_308022
  have hstable : (prefixWord ++ tailWord_308022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308022).length < 2 ^ (prefixWord ++ tailWord_308022).sum := by decide
  have hdescent : baseEnd_308022 < baseStart_308022 := by decide
  rcases family_descends (prefixWord ++ tailWord_308022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308035 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 1, 4]
def baseStart_308035 : Nat := 118140960795 + 308035 * 2 ^ 59
def prefixEnd_308035 : Nat := 4983230072969 + 3 ^ 40 * 308035 * 2
def baseEnd_308035 : Nat := 52723337802602515115293

theorem tailTrace_308035 : CollatzResearch.WordTrace tailWord_308035 prefixEnd_308035 52723337802602515115293 := by
  unfold tailWord_308035
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234959439049278034757559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7489972959366185356505039 11234959439049278034757559)
  ·
    refine ⟨16852439158573917052136339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11234959439049278034757559 16852439158573917052136339)
    ·
      refine ⟨25278658737860875578204509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16852439158573917052136339 25278658737860875578204509)
      ·
        refine ⟨9479497026697828341826691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25278658737860875578204509 9479497026697828341826691)
        ·
          refine ⟨14219245540046742512740037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9479497026697828341826691 14219245540046742512740037)
          ·
            refine ⟨2666108538758764221138757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14219245540046742512740037 2666108538758764221138757)
            ·
              refine ⟨499895351017268291463517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2666108538758764221138757 499895351017268291463517)
              ·
                refine ⟨187460756631475609298819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499895351017268291463517 187460756631475609298819)
                ·
                  refine ⟨281191134947213413948229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187460756631475609298819 281191134947213413948229)
                  ·
                    refine ⟨52723337802602515115293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281191134947213413948229 52723337802602515115293)
                    ·
                      rfl

theorem cell23_308035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 4].length) (baseStart_308035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308035 prefixEnd_308035 := by exact prefixLift 308035
  have htrace : WordTrace (prefixWord ++ tailWord_308035) baseStart_308035 baseEnd_308035 := by
    simpa [prefixWord, tailWord_308035, baseEnd_308035] using wordTrace_append hprefix tailTrace_308035
  have hstable : (prefixWord ++ tailWord_308035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308035).length < 2 ^ (prefixWord ++ tailWord_308035).sum := by decide
  have hdescent : baseEnd_308035 < baseStart_308035 := by decide
  rcases family_descends (prefixWord ++ tailWord_308035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308085 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_308085 : Nat := 118140960795 + 308085 * 2 ^ 59
def prefixEnd_308085 : Nat := 4983230072969 + 3 ^ 40 * 308085 * 2
def baseEnd_308085 : Nat := 158195687440532349720649

theorem tailTrace_308085 : CollatzResearch.WordTrace tailWord_308085 prefixEnd_308085 158195687440532349720649 := by
  unfold tailWord_308085
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236783088868136574077709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7491188725912091049385139 11236783088868136574077709)
  ·
    refine ⟨4213793658325551215279141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11236783088868136574077709 4213793658325551215279141)
    ·
      refine ⟨790086310936040852864839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4213793658325551215279141 790086310936040852864839)
      ·
        refine ⟨1185129466404061279297259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790086310936040852864839 1185129466404061279297259)
        ·
          refine ⟨1777694199606091918945889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185129466404061279297259 1777694199606091918945889)
          ·
            refine ⟨1333270649704568939209417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777694199606091918945889 1333270649704568939209417)
            ·
              refine ⟨999952987278426704407063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333270649704568939209417 999952987278426704407063)
              ·
                refine ⟨1499929480917640056610595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999952987278426704407063 1499929480917640056610595)
                ·
                  refine ⟨2249894221376460084915893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499929480917640056610595 2249894221376460084915893)
                  ·
                    refine ⟨210927583254043132960865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2249894221376460084915893 210927583254043132960865)
                    ·
                      refine ⟨158195687440532349720649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210927583254043132960865 158195687440532349720649)
                      ·
                        rfl

theorem cell23_308085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_308085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308085 prefixEnd_308085 := by exact prefixLift 308085
  have htrace : WordTrace (prefixWord ++ tailWord_308085) baseStart_308085 baseEnd_308085 := by
    simpa [prefixWord, tailWord_308085, baseEnd_308085] using wordTrace_append hprefix tailTrace_308085
  have hstable : (prefixWord ++ tailWord_308085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308085).length < 2 ^ (prefixWord ++ tailWord_308085).sum := by decide
  have hdescent : baseEnd_308085 < baseStart_308085 := by decide
  rcases family_descends (prefixWord ++ tailWord_308085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308091 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 1, 6]
def baseStart_308091 : Nat := 118140960795 + 308091 * 2 ^ 59
def prefixEnd_308091 : Nat := 4983230072969 + 3 ^ 40 * 308091 * 2
def baseEnd_308091 : Nat := 52732922774819775415207

theorem tailTrace_308091 : CollatzResearch.WordTrace tailWord_308091 prefixEnd_308091 52732922774819775415207 := by
  unfold tailWord_308091
  simp only [CollatzResearch.WordTrace]
  refine ⟨11237001926846399598796127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7491334617897599732530751 11237001926846399598796127)
  ·
    refine ⟨16855502890269599398194191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11237001926846399598796127 16855502890269599398194191)
    ·
      refine ⟨25283254335404399097291287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16855502890269599398194191 25283254335404399097291287)
      ·
        refine ⟨37924881503106598645936931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25283254335404399097291287 37924881503106598645936931)
        ·
          refine ⟨56887322254659897968905397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37924881503106598645936931 56887322254659897968905397)
          ·
            refine ⟨5333186461374365434584881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56887322254659897968905397 5333186461374365434584881)
            ·
              refine ⟨3999889846030774075938661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5333186461374365434584881 3999889846030774075938661)
              ·
                refine ⟨749979346130770139238499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3999889846030774075938661 749979346130770139238499)
                ·
                  refine ⟨1124969019196155208857749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749979346130770139238499 1124969019196155208857749)
                  ·
                    refine ⟨52732922774819775415207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1124969019196155208857749 52732922774819775415207)
                    ·
                      rfl

theorem cell23_308091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 6].length) (baseStart_308091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308091 prefixEnd_308091 := by exact prefixLift 308091
  have htrace : WordTrace (prefixWord ++ tailWord_308091) baseStart_308091 baseEnd_308091 := by
    simpa [prefixWord, tailWord_308091, baseEnd_308091] using wordTrace_append hprefix tailTrace_308091
  have hstable : (prefixWord ++ tailWord_308091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308091).length < 2 ^ (prefixWord ++ tailWord_308091).sum := by decide
  have hdescent : baseEnd_308091 < baseStart_308091 := by decide
  rcases family_descends (prefixWord ++ tailWord_308091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308108 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_308108 : Nat := 118140960795 + 308108 * 2 ^ 59
def prefixEnd_308108 : Nat := 4983230072969 + 3 ^ 40 * 308108 * 2
def baseEnd_308108 : Nat := 52735832498528586577681

theorem tailTrace_308108 : CollatzResearch.WordTrace tailWord_308108 prefixEnd_308108 52735832498528586577681 := by
  unfold tailWord_308108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618810983892405751082489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7491747978523207668109985 5618810983892405751082489)
  ·
    refine ⟨4214108237919304313311867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5618810983892405751082489 4214108237919304313311867)
    ·
      refine ⟨6321162356878956469967801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214108237919304313311867 6321162356878956469967801)
      ·
        refine ⟨4740871767659217352475851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6321162356878956469967801 4740871767659217352475851)
        ·
          refine ⟨7111307651488826028713777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740871767659217352475851 7111307651488826028713777)
          ·
            refine ⟨5333480738616619521535333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7111307651488826028713777 5333480738616619521535333)
            ·
              refine ⟨1000027638490616160287875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5333480738616619521535333 1000027638490616160287875)
              ·
                refine ⟨1500041457735924240431813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000027638490616160287875 1500041457735924240431813)
                ·
                  refine ⟨281257773325485795080965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1500041457735924240431813 281257773325485795080965)
                  ·
                    refine ⟨52735832498528586577681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281257773325485795080965 52735832498528586577681)
                    ·
                      rfl

theorem cell23_308108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_308108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308108 prefixEnd_308108 := by exact prefixLift 308108
  have htrace : WordTrace (prefixWord ++ tailWord_308108) baseStart_308108 baseEnd_308108 := by
    simpa [prefixWord, tailWord_308108, baseEnd_308108] using wordTrace_append hprefix tailTrace_308108
  have hstable : (prefixWord ++ tailWord_308108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308108).length < 2 ^ (prefixWord ++ tailWord_308108).sum := by decide
  have hdescent : baseEnd_308108 < baseStart_308108 := by decide
  rcases family_descends (prefixWord ++ tailWord_308108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308115 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 3, 2, 2]
def baseStart_308115 : Nat := 118140960795 + 308115 * 2 ^ 59
def prefixEnd_308115 : Nat := 4983230072969 + 3 ^ 40 * 308115 * 2
def baseEnd_308115 : Nat := 158211091860167232345511

theorem tailTrace_308115 : CollatzResearch.WordTrace tailWord_308115 prefixEnd_308115 158211091860167232345511 := by
  unfold tailWord_308115
  simp only [CollatzResearch.WordTrace]
  refine ⟨11237877278759451697669799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7491918185839634465113199 11237877278759451697669799)
  ·
    refine ⟨16856815918139177546504699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11237877278759451697669799 16856815918139177546504699)
    ·
      refine ⟨25285223877208766319757049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16856815918139177546504699 25285223877208766319757049)
      ·
        refine ⟨18963917907906574739817787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25285223877208766319757049 18963917907906574739817787)
        ·
          refine ⟨28445876861859862109726681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18963917907906574739817787 28445876861859862109726681)
          ·
            refine ⟨21334407646394896582295011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28445876861859862109726681 21334407646394896582295011)
            ·
              refine ⟨32001611469592344873442517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21334407646394896582295011 32001611469592344873442517)
              ·
                refine ⟨750037768818570582971309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32001611469592344873442517 750037768818570582971309)
                ·
                  refine ⟨281264163306963968614241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750037768818570582971309 281264163306963968614241)
                  ·
                    refine ⟨210948122480222976460681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 281264163306963968614241 210948122480222976460681)
                    ·
                      refine ⟨158211091860167232345511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210948122480222976460681 158211091860167232345511)
                      ·
                        rfl

theorem cell23_308115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2, 2].length) (baseStart_308115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308115 prefixEnd_308115 := by exact prefixLift 308115
  have htrace : WordTrace (prefixWord ++ tailWord_308115) baseStart_308115 baseEnd_308115 := by
    simpa [prefixWord, tailWord_308115, baseEnd_308115] using wordTrace_append hprefix tailTrace_308115
  have hstable : (prefixWord ++ tailWord_308115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308115).length < 2 ^ (prefixWord ++ tailWord_308115).sum := by decide
  have hdescent : baseEnd_308115 < baseStart_308115 := by decide
  rcases family_descends (prefixWord ++ tailWord_308115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308125 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_308125 : Nat := 118140960795 + 308125 * 2 ^ 59
def prefixEnd_308125 : Nat := 4983230072969 + 3 ^ 40 * 308125 * 2
def baseEnd_308125 : Nat := 52738742222237397740155

theorem tailTrace_308125 : CollatzResearch.WordTrace tailWord_308125 prefixEnd_308125 52738742222237397740155 := by
  unfold tailWord_308125
  simp only [CollatzResearch.WordTrace]
  refine ⟨11238242008723223405533829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7492161339148815603689219 11238242008723223405533829)
  ·
    refine ⟨2107170376635604388537593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11238242008723223405533829 2107170376635604388537593)
    ·
      refine ⟨1580377782476703291403195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2107170376635604388537593 1580377782476703291403195)
      ·
        refine ⟨2370566673715054937104793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1580377782476703291403195 2370566673715054937104793)
        ·
          refine ⟨1777925005286291202828595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2370566673715054937104793 1777925005286291202828595)
          ·
            refine ⟨2666887507929436804242893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777925005286291202828595 2666887507929436804242893)
            ·
              refine ⟨1000082815473538801591085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2666887507929436804242893 1000082815473538801591085)
              ·
                refine ⟨375031055802577050596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000082815473538801591085 375031055802577050596657)
                ·
                  refine ⟨281273291851932787947493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375031055802577050596657 281273291851932787947493)
                  ·
                    refine ⟨52738742222237397740155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281273291851932787947493 52738742222237397740155)
                    ·
                      rfl

theorem cell23_308125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_308125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308125 prefixEnd_308125 := by exact prefixLift 308125
  have htrace : WordTrace (prefixWord ++ tailWord_308125) baseStart_308125 baseEnd_308125 := by
    simpa [prefixWord, tailWord_308125, baseEnd_308125] using wordTrace_append hprefix tailTrace_308125
  have hstable : (prefixWord ++ tailWord_308125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308125).length < 2 ^ (prefixWord ++ tailWord_308125).sum := by decide
  have hdescent : baseEnd_308125 < baseStart_308125 := by decide
  rcases family_descends (prefixWord ++ tailWord_308125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308145 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_308145 : Nat := 118140960795 + 308145 * 2 ^ 59
def prefixEnd_308145 : Nat := 4983230072969 + 3 ^ 40 * 308145 * 2
def baseEnd_308145 : Nat := 158226496279802114970373

theorem tailTrace_308145 : CollatzResearch.WordTrace tailWord_308145 prefixEnd_308145 158226496279802114970373 := by
  unfold tailWord_308145
  simp only [CollatzResearch.WordTrace]
  refine ⟨11238971468650766821261889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7492647645767177880841259 11238971468650766821261889)
  ·
    refine ⟨8429228601488075115946417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11238971468650766821261889 8429228601488075115946417)
    ·
      refine ⟨6321921451116056336959813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8429228601488075115946417 6321921451116056336959813)
      ·
        refine ⟨1185360272084260563179965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6321921451116056336959813 1185360272084260563179965)
        ·
          refine ⟨444510102031597711192487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1185360272084260563179965 444510102031597711192487)
          ·
            refine ⟨666765153047396566788731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444510102031597711192487 666765153047396566788731)
            ·
              refine ⟨1000147729571094850183097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666765153047396566788731 1000147729571094850183097)
              ·
                refine ⟨750110797178321137637323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000147729571094850183097 750110797178321137637323)
                ·
                  refine ⟨1125166195767481706455985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750110797178321137637323 1125166195767481706455985)
                  ·
                    refine ⟨843874646825611279841989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1125166195767481706455985 843874646825611279841989)
                    ·
                      refine ⟨158226496279802114970373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 843874646825611279841989 158226496279802114970373)
                      ·
                        rfl

theorem cell23_308145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_308145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308145 prefixEnd_308145 := by exact prefixLift 308145
  have htrace : WordTrace (prefixWord ++ tailWord_308145) baseStart_308145 baseEnd_308145 := by
    simpa [prefixWord, tailWord_308145, baseEnd_308145] using wordTrace_append hprefix tailTrace_308145
  have hstable : (prefixWord ++ tailWord_308145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308145).length < 2 ^ (prefixWord ++ tailWord_308145).sum := by decide
  have hdescent : baseEnd_308145 < baseStart_308145 := by decide
  rcases family_descends (prefixWord ++ tailWord_308145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308149 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_308149 : Nat := 118140960795 + 308149 * 2 ^ 59
def prefixEnd_308149 : Nat := 4983230072969 + 3 ^ 40 * 308149 * 2
def baseEnd_308149 : Nat := 158228550202420099320355

theorem tailTrace_308149 : CollatzResearch.WordTrace tailWord_308149 prefixEnd_308149 158228550202420099320355 := by
  unfold tailWord_308149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239117360636275504407501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7492744907090850336271667 11239117360636275504407501)
  ·
    refine ⟨4214669010238603314152813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11239117360636275504407501 4214669010238603314152813)
    ·
      refine ⟨1580500878839476242807305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4214669010238603314152813 1580500878839476242807305)
      ·
        refine ⟨1185375659129607182105479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580500878839476242807305 1185375659129607182105479)
        ·
          refine ⟨1778063488694410773158219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185375659129607182105479 1778063488694410773158219)
          ·
            refine ⟨2667095233041616159737329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778063488694410773158219 2667095233041616159737329)
            ·
              refine ⟨2000321424781212119802997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667095233041616159737329 2000321424781212119802997)
              ·
                refine ⟨187530133573238636231531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2000321424781212119802997 187530133573238636231531)
                ·
                  refine ⟨281295200359857954347297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187530133573238636231531 281295200359857954347297)
                  ·
                    refine ⟨210971400269893465760473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 281295200359857954347297 210971400269893465760473)
                    ·
                      refine ⟨158228550202420099320355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210971400269893465760473 158228550202420099320355)
                      ·
                        rfl

theorem cell23_308149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_308149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308149 prefixEnd_308149 := by exact prefixLift 308149
  have htrace : WordTrace (prefixWord ++ tailWord_308149) baseStart_308149 baseEnd_308149 := by
    simpa [prefixWord, tailWord_308149, baseEnd_308149] using wordTrace_append hprefix tailTrace_308149
  have hstable : (prefixWord ++ tailWord_308149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308149).length < 2 ^ (prefixWord ++ tailWord_308149).sum := by decide
  have hdescent : baseEnd_308149 < baseStart_308149 := by decide
  rcases family_descends (prefixWord ++ tailWord_308149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308152 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_308152 : Nat := 118140960795 + 308152 * 2 ^ 59
def prefixEnd_308152 : Nat := 4983230072969 + 3 ^ 40 * 308152 * 2
def baseEnd_308152 : Nat := 158230090644383587582841

theorem tailTrace_308152 : CollatzResearch.WordTrace tailWord_308152 prefixEnd_308152 158230090644383587582841 := by
  unfold tailWord_308152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5619613389812703508383355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7492817853083604677844473 5619613389812703508383355)
  ·
    refine ⟨8429420084719055262575033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5619613389812703508383355 8429420084719055262575033)
    ·
      refine ⟨6322065063539291446931275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8429420084719055262575033 6322065063539291446931275)
      ·
        refine ⟨9483097595308937170396913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6322065063539291446931275 9483097595308937170396913)
        ·
          refine ⟨7112323196481702877797685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9483097595308937170396913 7112323196481702877797685)
          ·
            refine ⟨666780299670159644793533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7112323196481702877797685 666780299670159644793533)
            ·
              refine ⟨250042612376309866797575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666780299670159644793533 250042612376309866797575)
              ·
                refine ⟨375063918564464800196363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250042612376309866797575 375063918564464800196363)
                ·
                  refine ⟨562595877846697200294545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375063918564464800196363 562595877846697200294545)
                  ·
                    refine ⟨421946908385022900220909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 562595877846697200294545 421946908385022900220909)
                    ·
                      refine ⟨158230090644383587582841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421946908385022900220909 158230090644383587582841)
                      ·
                        rfl

theorem cell23_308152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_308152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308152 prefixEnd_308152 := by exact prefixLift 308152
  have htrace : WordTrace (prefixWord ++ tailWord_308152) baseStart_308152 baseEnd_308152 := by
    simpa [prefixWord, tailWord_308152, baseEnd_308152] using wordTrace_append hprefix tailTrace_308152
  have hstable : (prefixWord ++ tailWord_308152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308152).length < 2 ^ (prefixWord ++ tailWord_308152).sum := by decide
  have hdescent : baseEnd_308152 < baseStart_308152 := by decide
  rcases family_descends (prefixWord ++ tailWord_308152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308175 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 3, 3, 2]
def baseStart_308175 : Nat := 118140960795 + 308175 * 2 ^ 59
def prefixEnd_308175 : Nat := 4983230072969 + 3 ^ 40 * 308175 * 2
def baseEnd_308175 : Nat := 158241900699436997595235

theorem tailTrace_308175 : CollatzResearch.WordTrace tailWord_308175 prefixEnd_308175 158241900699436997595235 := by
  unfold tailWord_308175
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240065658542081944853979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7493377105694721296569319 11240065658542081944853979)
  ·
    refine ⟨16860098487813122917280969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11240065658542081944853979 16860098487813122917280969)
    ·
      refine ⟨12645073865859842187960727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16860098487813122917280969 12645073865859842187960727)
      ·
        refine ⟨18967610798789763281941091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645073865859842187960727 18967610798789763281941091)
        ·
          refine ⟨28451416198184644922911637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18967610798789763281941091 28451416198184644922911637)
          ·
            refine ⟨1333660134289905230761483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28451416198184644922911637 1333660134289905230761483)
            ·
              refine ⟨2000490201434857846142225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333660134289905230761483 2000490201434857846142225)
              ·
                refine ⟨1500367651076143384606669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000490201434857846142225 1500367651076143384606669)
                ·
                  refine ⟨562637869153553769227501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1500367651076143384606669 562637869153553769227501)
                  ·
                    refine ⟨210989200932582663460313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562637869153553769227501 210989200932582663460313)
                    ·
                      refine ⟨158241900699436997595235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 210989200932582663460313 158241900699436997595235)
                      ·
                        rfl

theorem cell23_308175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3, 2].length) (baseStart_308175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308175 prefixEnd_308175 := by exact prefixLift 308175
  have htrace : WordTrace (prefixWord ++ tailWord_308175) baseStart_308175 baseEnd_308175 := by
    simpa [prefixWord, tailWord_308175, baseEnd_308175] using wordTrace_append hprefix tailTrace_308175
  have hstable : (prefixWord ++ tailWord_308175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308175).length < 2 ^ (prefixWord ++ tailWord_308175).sum := by decide
  have hdescent : baseEnd_308175 < baseStart_308175 := by decide
  rcases family_descends (prefixWord ++ tailWord_308175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308182 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_308182 : Nat := 118140960795 + 308182 * 2 ^ 59
def prefixEnd_308182 : Nat := 4983230072969 + 3 ^ 40 * 308182 * 2
def baseEnd_308182 : Nat := 158245495064018470207703

theorem tailTrace_308182 : CollatzResearch.WordTrace tailWord_308182 prefixEnd_308182 158245495064018470207703 := by
  unfold tailWord_308182
  simp only [CollatzResearch.WordTrace]
  refine ⟨702520060594795133772425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7493547313011148093572533 702520060594795133772425)
  ·
    refine ⟨526890045446096350329319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 702520060594795133772425 526890045446096350329319)
    ·
      refine ⟨790335068169144525493979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526890045446096350329319 790335068169144525493979)
      ·
        refine ⟨1185502602253716788240969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790335068169144525493979 1185502602253716788240969)
        ·
          refine ⟨889126951690287591180727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185502602253716788240969 889126951690287591180727)
          ·
            refine ⟨1333690427535431386771091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889126951690287591180727 1333690427535431386771091)
            ·
              refine ⟨2000535641303147080156637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333690427535431386771091 2000535641303147080156637)
              ·
                refine ⟨750200865488680155058739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2000535641303147080156637 750200865488680155058739)
                ·
                  refine ⟨1125301298233020232588109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750200865488680155058739 1125301298233020232588109)
                  ·
                    refine ⟨421987986837382587220541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125301298233020232588109 421987986837382587220541)
                    ·
                      refine ⟨158245495064018470207703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 421987986837382587220541 158245495064018470207703)
                      ·
                        rfl

theorem cell23_308182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_308182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308182 prefixEnd_308182 := by exact prefixLift 308182
  have htrace : WordTrace (prefixWord ++ tailWord_308182) baseStart_308182 baseEnd_308182 := by
    simpa [prefixWord, tailWord_308182, baseEnd_308182] using wordTrace_append hprefix tailTrace_308182
  have hstable : (prefixWord ++ tailWord_308182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308182).length < 2 ^ (prefixWord ++ tailWord_308182).sum := by decide
  have hdescent : baseEnd_308182 < baseStart_308182 := by decide
  rcases family_descends (prefixWord ++ tailWord_308182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308209 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_308209 : Nat := 118140960795 + 308209 * 2 ^ 59
def prefixEnd_308209 : Nat := 4983230072969 + 3 ^ 40 * 308209 * 2
def baseEnd_308209 : Nat := 158259359041689864570079

theorem tailTrace_308209 : CollatzResearch.WordTrace tailWord_308209 prefixEnd_308209 158259359041689864570079 := by
  unfold tailWord_308209
  simp only [CollatzResearch.WordTrace]
  refine ⟨11241305740418905751591681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7494203826945937167727787 11241305740418905751591681)
  ·
    refine ⟨8430979305314179313693761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11241305740418905751591681 8430979305314179313693761)
    ·
      refine ⟨6323234478985634485270321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8430979305314179313693761 6323234478985634485270321)
      ·
        refine ⟨4742425859239225863952741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6323234478985634485270321 4742425859239225863952741)
        ·
          refine ⟨889204848607354849491139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4742425859239225863952741 889204848607354849491139)
          ·
            refine ⟨1333807272911032274236709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889204848607354849491139 1333807272911032274236709)
            ·
              refine ⟨250088863670818551419383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1333807272911032274236709 250088863670818551419383)
              ·
                refine ⟨375133295506227827129075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250088863670818551419383 375133295506227827129075)
                ·
                  refine ⟨562699943259341740693613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375133295506227827129075 562699943259341740693613)
                  ·
                    refine ⟨211012478722253152760105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562699943259341740693613 211012478722253152760105)
                    ·
                      refine ⟨158259359041689864570079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211012478722253152760105 158259359041689864570079)
                      ·
                        rfl

theorem cell23_308209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_308209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308209 prefixEnd_308209 := by exact prefixLift 308209
  have htrace : WordTrace (prefixWord ++ tailWord_308209) baseStart_308209 baseEnd_308209 := by
    simpa [prefixWord, tailWord_308209, baseEnd_308209] using wordTrace_append hprefix tailTrace_308209
  have hstable : (prefixWord ++ tailWord_308209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308209).length < 2 ^ (prefixWord ++ tailWord_308209).sum := by decide
  have hdescent : baseEnd_308209 < baseStart_308209 := by decide
  rcases family_descends (prefixWord ++ tailWord_308209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308268 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_308268 : Nat := 118140960795 + 308268 * 2 ^ 59
def prefixEnd_308268 : Nat := 4983230072969 + 3 ^ 40 * 308268 * 2
def baseEnd_308268 : Nat := 158289654400305133732307

theorem tailTrace_308268 : CollatzResearch.WordTrace tailWord_308268 prefixEnd_308268 158289654400305133732307 := by
  unfold tailWord_308268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621728823602579413994729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7495638431470105885326305 5621728823602579413994729)
  ·
    refine ⟨4216296617701934560496047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5621728823602579413994729 4216296617701934560496047)
    ·
      refine ⟨6324444926552901840744071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216296617701934560496047 6324444926552901840744071)
      ·
        refine ⟨9486667389829352761116107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324444926552901840744071 9486667389829352761116107)
        ·
          refine ⟨14230001084744029141674161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9486667389829352761116107 14230001084744029141674161)
          ·
            refine ⟨10672500813558021856255621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14230001084744029141674161 10672500813558021856255621)
            ·
              refine ⟨2001093902542129098047929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10672500813558021856255621 2001093902542129098047929)
              ·
                refine ⟨1500820426906596823535947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001093902542129098047929 1500820426906596823535947)
                ·
                  refine ⟨2251230640359895235303921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500820426906596823535947 2251230640359895235303921)
                  ·
                    refine ⟨1688422980269921426477941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251230640359895235303921 1688422980269921426477941)
                    ·
                      refine ⟨158289654400305133732307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1688422980269921426477941 158289654400305133732307)
                      ·
                        rfl

theorem cell23_308268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_308268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308268 prefixEnd_308268 := by exact prefixLift 308268
  have htrace : WordTrace (prefixWord ++ tailWord_308268) baseStart_308268 baseEnd_308268 := by
    simpa [prefixWord, tailWord_308268, baseEnd_308268] using wordTrace_append hprefix tailTrace_308268
  have hstable : (prefixWord ++ tailWord_308268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308268).length < 2 ^ (prefixWord ++ tailWord_308268).sum := by decide
  have hdescent : baseEnd_308268 < baseStart_308268 := by decide
  rcases family_descends (prefixWord ++ tailWord_308268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308285 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_308285 : Nat := 118140960795 + 308285 * 2 ^ 59
def prefixEnd_308285 : Nat := 4983230072969 + 3 ^ 40 * 308285 * 2
def baseEnd_308285 : Nat := 158298383571431567219729

theorem tailTrace_308285 : CollatzResearch.WordTrace tailWord_308285 prefixEnd_308285 158298383571431567219729 := by
  unfold tailWord_308285
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244077688143570731358309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7496051792095713820905539 11244077688143570731358309)
  ·
    refine ⟨2108264566526919512129683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11244077688143570731358309 2108264566526919512129683)
    ·
      refine ⟨3162396849790379268194525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108264566526919512129683 3162396849790379268194525)
      ·
        refine ⟨1185898818671392225572947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3162396849790379268194525 1185898818671392225572947)
        ·
          refine ⟨1778848228007088338359421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185898818671392225572947 1778848228007088338359421)
          ·
            refine ⟨667068085502658126884783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1778848228007088338359421 667068085502658126884783)
            ·
              refine ⟨1000602128253987190327175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667068085502658126884783 1000602128253987190327175)
              ·
                refine ⟨1500903192380980785490763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000602128253987190327175 1500903192380980785490763)
                ·
                  refine ⟨2251354788571471178236145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500903192380980785490763 2251354788571471178236145)
                  ·
                    refine ⟨1688516091428603383677109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251354788571471178236145 1688516091428603383677109)
                    ·
                      refine ⟨158298383571431567219729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1688516091428603383677109 158298383571431567219729)
                      ·
                        rfl

theorem cell23_308285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_308285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308285 prefixEnd_308285 := by exact prefixLift 308285
  have htrace : WordTrace (prefixWord ++ tailWord_308285) baseStart_308285 baseEnd_308285 := by
    simpa [prefixWord, tailWord_308285, baseEnd_308285] using wordTrace_append hprefix tailTrace_308285
  have hstable : (prefixWord ++ tailWord_308285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308285).length < 2 ^ (prefixWord ++ tailWord_308285).sum := by decide
  have hdescent : baseEnd_308285 < baseStart_308285 := by decide
  rcases family_descends (prefixWord ++ tailWord_308285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308305 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_308305 : Nat := 118140960795 + 308305 * 2 ^ 59
def prefixEnd_308305 : Nat := 4983230072969 + 3 ^ 40 * 308305 * 2
def baseEnd_308305 : Nat := 52769551061507162989879

theorem tailTrace_308305 : CollatzResearch.WordTrace tailWord_308305 prefixEnd_308305 52769551061507162989879 := by
  unfold tailWord_308305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244807148071114147086369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7496538098714076098057579 11244807148071114147086369)
  ·
    refine ⟨8433605361053335610314777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11244807148071114147086369 8433605361053335610314777)
    ·
      refine ⟨6325204020790001707736083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8433605361053335610314777 6325204020790001707736083)
      ·
        refine ⟨9487806031185002561604125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325204020790001707736083 9487806031185002561604125)
        ·
          refine ⟨3557927261694375960601547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9487806031185002561604125 3557927261694375960601547)
          ·
            refine ⟨5336890892541563940902321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557927261694375960601547 5336890892541563940902321)
            ·
              refine ⟨4002668169406172955676741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5336890892541563940902321 4002668169406172955676741)
              ·
                refine ⟨750500281763657429189389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4002668169406172955676741 750500281763657429189389)
                ·
                  refine ⟨281437605661371535946021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750500281763657429189389 281437605661371535946021)
                  ·
                    refine ⟨52769551061507162989879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281437605661371535946021 52769551061507162989879)
                    ·
                      rfl

theorem cell23_308305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_308305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308305 prefixEnd_308305 := by exact prefixLift 308305
  have htrace : WordTrace (prefixWord ++ tailWord_308305) baseStart_308305 baseEnd_308305 := by
    simpa [prefixWord, tailWord_308305, baseEnd_308305] using wordTrace_append hprefix tailTrace_308305
  have hstable : (prefixWord ++ tailWord_308305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308305).length < 2 ^ (prefixWord ++ tailWord_308305).sum := by decide
  have hdescent : baseEnd_308305 < baseStart_308305 := by decide
  rcases family_descends (prefixWord ++ tailWord_308305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308335 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 6]
def baseStart_308335 : Nat := 118140960795 + 308335 * 2 ^ 59
def prefixEnd_308335 : Nat := 4983230072969 + 3 ^ 40 * 308335 * 2
def baseEnd_308335 : Nat := 17591561956017374621611

theorem tailTrace_308335 : CollatzResearch.WordTrace tailWord_308335 prefixEnd_308335 17591561956017374621611 := by
  unfold tailWord_308335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11245901337962429270678459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7497267558641619513785639 11245901337962429270678459)
  ·
    refine ⟨16868852006943643906017689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11245901337962429270678459 16868852006943643906017689)
    ·
      refine ⟨12651639005207732929513267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16868852006943643906017689 12651639005207732929513267)
      ·
        refine ⟨18977458507811599394269901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12651639005207732929513267 18977458507811599394269901)
        ·
          refine ⟨7116546940429349772851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18977458507811599394269901 7116546940429349772851213)
          ·
            refine ⟨2668705102661006164819205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7116546940429349772851213 2668705102661006164819205)
            ·
              refine ⟨500382206748938655903601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2668705102661006164819205 500382206748938655903601)
              ·
                refine ⟨375286655061703991927701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500382206748938655903601 375286655061703991927701)
                ·
                  refine ⟨17591561956017374621611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375286655061703991927701 17591561956017374621611)
                  ·
                    rfl

theorem cell23_308335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 6].length) (baseStart_308335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308335 prefixEnd_308335 := by exact prefixLift 308335
  have htrace : WordTrace (prefixWord ++ tailWord_308335) baseStart_308335 baseEnd_308335 := by
    simpa [prefixWord, tailWord_308335, baseEnd_308335] using wordTrace_append hprefix tailTrace_308335
  have hstable : (prefixWord ++ tailWord_308335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308335).length < 2 ^ (prefixWord ++ tailWord_308335).sum := by decide
  have hdescent : baseEnd_308335 < baseStart_308335 := by decide
  rcases family_descends (prefixWord ++ tailWord_308335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308386 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_308386 : Nat := 118140960795 + 308386 * 2 ^ 59
def prefixEnd_308386 : Nat := 4983230072969 + 3 ^ 40 * 308386 * 2
def baseEnd_308386 : Nat := 17594471679726185784085

theorem tailTrace_308386 : CollatzResearch.WordTrace tailWord_308386 prefixEnd_308386 17594471679726185784085 := by
  unfold tailWord_308386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811940365194416245196253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7498507640518443320523341 2811940365194416245196253)
  ·
    refine ⟨1054477636947906091948595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2811940365194416245196253 1054477636947906091948595)
    ·
      refine ⟨1581716455421859137922893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054477636947906091948595 1581716455421859137922893)
      ·
        refine ⟨593143670783197176721085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1581716455421859137922893 593143670783197176721085)
        ·
          refine ⟨222428876543698941270407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593143670783197176721085 222428876543698941270407)
          ·
            refine ⟨333643314815548411905611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222428876543698941270407 333643314815548411905611)
            ·
              refine ⟨500464972223322617858417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333643314815548411905611 500464972223322617858417)
              ·
                refine ⟨375348729167491963393813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500464972223322617858417 375348729167491963393813)
                ·
                  refine ⟨17594471679726185784085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375348729167491963393813 17594471679726185784085)
                  ·
                    rfl

theorem cell23_308386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_308386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308386 prefixEnd_308386 := by exact prefixLift 308386
  have htrace : WordTrace (prefixWord ++ tailWord_308386) baseStart_308386 baseEnd_308386 := by
    simpa [prefixWord, tailWord_308386, baseEnd_308386] using wordTrace_append hprefix tailTrace_308386
  have hstable : (prefixWord ++ tailWord_308386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308386).length < 2 ^ (prefixWord ++ tailWord_308386).sum := by decide
  have hdescent : baseEnd_308386 < baseStart_308386 := by decide
  rcases family_descends (prefixWord ++ tailWord_308386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308412 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_308412 : Nat := 118140960795 + 308412 * 2 ^ 59
def prefixEnd_308412 : Nat := 4983230072969 + 3 ^ 40 * 308412 * 2
def baseEnd_308412 : Nat := 52787865204850856777215

theorem tailTrace_308412 : CollatzResearch.WordTrace tailWord_308412 prefixEnd_308412 52787865204850856777215 := by
  unfold tailWord_308412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624354879341735710615745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7499139839122314280820993 5624354879341735710615745)
  ·
    refine ⟨4218266159506301782961809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5624354879341735710615745 4218266159506301782961809)
    ·
      refine ⟨3163699619629726337221357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4218266159506301782961809 3163699619629726337221357)
      ·
        refine ⟨1186387357361147376458009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3163699619629726337221357 1186387357361147376458009)
        ·
          refine ⟨889790518020860532343507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186387357361147376458009 889790518020860532343507)
          ·
            refine ⟨1334685777031290798515261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889790518020860532343507 1334685777031290798515261)
            ·
              refine ⟨500507166386734049443223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1334685777031290798515261 500507166386734049443223)
              ·
                refine ⟨750760749580101074164835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500507166386734049443223 750760749580101074164835)
                ·
                  refine ⟨1126141124370151611247253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750760749580101074164835 1126141124370151611247253)
                  ·
                    refine ⟨52787865204850856777215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1126141124370151611247253 52787865204850856777215)
                    ·
                      rfl

theorem cell23_308412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_308412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308412 prefixEnd_308412 := by exact prefixLift 308412
  have htrace : WordTrace (prefixWord ++ tailWord_308412) baseStart_308412 baseEnd_308412 := by
    simpa [prefixWord, tailWord_308412, baseEnd_308412] using wordTrace_append hprefix tailTrace_308412
  have hstable : (prefixWord ++ tailWord_308412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308412).length < 2 ^ (prefixWord ++ tailWord_308412).sum := by decide
  have hdescent : baseEnd_308412 < baseStart_308412 := by decide
  rcases family_descends (prefixWord ++ tailWord_308412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308430 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_308430 : Nat := 118140960795 + 308430 * 2 ^ 59
def prefixEnd_308430 : Nat := 4983230072969 + 3 ^ 40 * 308430 * 2
def baseEnd_308430 : Nat := 158372838266333499906563

theorem tailTrace_308430 : CollatzResearch.WordTrace tailWord_308430 prefixEnd_308430 158372838266333499906563 := by
  unfold tailWord_308430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406170784077282561923343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7499577515078840330257829 1406170784077282561923343)
  ·
    refine ⟨2109256176115923842885015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1406170784077282561923343 2109256176115923842885015)
    ·
      refine ⟨3163884264173885764327523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109256176115923842885015 3163884264173885764327523)
      ·
        refine ⟨4745826396260828646491285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163884264173885764327523 4745826396260828646491285)
        ·
          refine ⟨222460612324726342804279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4745826396260828646491285 222460612324726342804279)
          ·
            refine ⟨333690918487089514206419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222460612324726342804279 333690918487089514206419)
            ·
              refine ⟨500536377730634271309629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333690918487089514206419 500536377730634271309629)
              ·
                refine ⟨187701141648987851741111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500536377730634271309629 187701141648987851741111)
                ·
                  refine ⟨281551712473481777611667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187701141648987851741111 281551712473481777611667)
                  ·
                    refine ⟨422327568710222666417501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 281551712473481777611667 422327568710222666417501)
                    ·
                      refine ⟨158372838266333499906563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 422327568710222666417501 158372838266333499906563)
                      ·
                        rfl

theorem cell23_308430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_308430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308430 prefixEnd_308430 := by exact prefixLift 308430
  have htrace : WordTrace (prefixWord ++ tailWord_308430) baseStart_308430 baseEnd_308430 := by
    simpa [prefixWord, tailWord_308430, baseEnd_308430] using wordTrace_append hprefix tailTrace_308430
  have hstable : (prefixWord ++ tailWord_308430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308430).length < 2 ^ (prefixWord ++ tailWord_308430).sum := by decide
  have hdescent : baseEnd_308430 < baseStart_308430 := by decide
  rcases family_descends (prefixWord ++ tailWord_308430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308453 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_308453 : Nat := 118140960795 + 308453 * 2 ^ 59
def prefixEnd_308453 : Nat := 4983230072969 + 3 ^ 40 * 308453 * 2
def baseEnd_308453 : Nat := 158384648321386909918957

theorem tailTrace_308453 : CollatzResearch.WordTrace tailWord_308453 prefixEnd_308453 158384648321386909918957 := by
  unfold tailWord_308453
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250205151534935423474013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7500136767689956948982675 11250205151534935423474013)
  ·
    refine ⟨4218826931825600783802755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11250205151534935423474013 4218826931825600783802755)
    ·
      refine ⟨6328240397738401175704133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218826931825600783802755 6328240397738401175704133)
      ·
        refine ⟨1186545074575950220444525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6328240397738401175704133 1186545074575950220444525)
        ·
          refine ⟨444954402965981332666697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1186545074575950220444525 444954402965981332666697)
          ·
            refine ⟨333715802224485999500023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444954402965981332666697 333715802224485999500023)
            ·
              refine ⟨500573703336728999250035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333715802224485999500023 500573703336728999250035)
              ·
                refine ⟨750860555005093498875053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500573703336728999250035 750860555005093498875053)
                ·
                  refine ⟨281572708126910062078145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 750860555005093498875053 281572708126910062078145)
                  ·
                    refine ⟨211179531095182546558609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 281572708126910062078145 211179531095182546558609)
                    ·
                      refine ⟨158384648321386909918957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211179531095182546558609 158384648321386909918957)
                      ·
                        rfl

theorem cell23_308453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_308453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308453 prefixEnd_308453 := by exact prefixLift 308453
  have htrace : WordTrace (prefixWord ++ tailWord_308453) baseStart_308453 baseEnd_308453 := by
    simpa [prefixWord, tailWord_308453, baseEnd_308453] using wordTrace_append hprefix tailTrace_308453
  have hstable : (prefixWord ++ tailWord_308453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308453).length < 2 ^ (prefixWord ++ tailWord_308453).sum := by decide
  have hdescent : baseEnd_308453 < baseStart_308453 := by decide
  rcases family_descends (prefixWord ++ tailWord_308453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308463 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 2, 4]
def baseStart_308463 : Nat := 118140960795 + 308463 * 2 ^ 59
def prefixEnd_308463 : Nat := 4983230072969 + 3 ^ 40 * 308463 * 2
def baseEnd_308463 : Nat := 52796594375977290264637

theorem tailTrace_308463 : CollatzResearch.WordTrace tailWord_308463 prefixEnd_308463 52796594375977290264637 := by
  unfold tailWord_308463
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250569881498707131338043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7500379920999138087558695 11250569881498707131338043)
  ·
    refine ⟨16875854822248060697007065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11250569881498707131338043 16875854822248060697007065)
    ·
      refine ⟨12656891116686045522755299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16875854822248060697007065 12656891116686045522755299)
      ·
        refine ⟨18985336675029068284132949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12656891116686045522755299 18985336675029068284132949)
        ·
          refine ⟨222484414160496893954683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 18985336675029068284132949 222484414160496893954683)
          ·
            refine ⟨333726621240745340932025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222484414160496893954683 333726621240745340932025)
            ·
              refine ⟨250294965930559005699019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333726621240745340932025 250294965930559005699019)
              ·
                refine ⟨375442448895838508548529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250294965930559005699019 375442448895838508548529)
                ·
                  refine ⟨281581836671878881411397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375442448895838508548529 281581836671878881411397)
                  ·
                    refine ⟨52796594375977290264637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281581836671878881411397 52796594375977290264637)
                    ·
                      rfl

theorem cell23_308463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_308463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308463 prefixEnd_308463 := by exact prefixLift 308463
  have htrace : WordTrace (prefixWord ++ tailWord_308463) baseStart_308463 baseEnd_308463 := by
    simpa [prefixWord, tailWord_308463, baseEnd_308463] using wordTrace_append hprefix tailTrace_308463
  have hstable : (prefixWord ++ tailWord_308463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308463).length < 2 ^ (prefixWord ++ tailWord_308463).sum := by decide
  have hdescent : baseEnd_308463 < baseStart_308463 := by decide
  rcases family_descends (prefixWord ++ tailWord_308463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308479 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 3, 3, 2]
def baseStart_308479 : Nat := 118140960795 + 308479 * 2 ^ 59
def prefixEnd_308479 : Nat := 4983230072969 + 3 ^ 40 * 308479 * 2
def baseEnd_308479 : Nat := 158397998818403808193837

theorem tailTrace_308479 : CollatzResearch.WordTrace tailWord_308479 prefixEnd_308479 158397998818403808193837 := by
  unfold tailWord_308479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251153449440741863920491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7500768966293827909280327 11251153449440741863920491)
  ·
    refine ⟨16876730174161112795880737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11251153449440741863920491 16876730174161112795880737)
    ·
      refine ⟨12657547630620834596910553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16876730174161112795880737 12657547630620834596910553)
      ·
        refine ⟨9493160722965625947682915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12657547630620834596910553 9493160722965625947682915)
        ·
          refine ⟨14239741084448438921524373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9493160722965625947682915 14239741084448438921524373)
          ·
            refine ⟨667487863333520574446455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14239741084448438921524373 667487863333520574446455)
            ·
              refine ⟨1001231795000280861669683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667487863333520574446455 1001231795000280861669683)
              ·
                refine ⟨1501847692500421292504525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001231795000280861669683 1501847692500421292504525)
                ·
                  refine ⟨563192884687657984689197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1501847692500421292504525 563192884687657984689197)
                  ·
                    refine ⟨211197331757871744258449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563192884687657984689197 211197331757871744258449)
                    ·
                      refine ⟨158397998818403808193837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211197331757871744258449 158397998818403808193837)
                      ·
                        rfl

theorem cell23_308479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_308479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308479 prefixEnd_308479 := by exact prefixLift 308479
  have htrace : WordTrace (prefixWord ++ tailWord_308479) baseStart_308479 baseEnd_308479 := by
    simpa [prefixWord, tailWord_308479, baseEnd_308479] using wordTrace_append hprefix tailTrace_308479
  have hstable : (prefixWord ++ tailWord_308479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308479).length < 2 ^ (prefixWord ++ tailWord_308479).sum := by decide
  have hdescent : baseEnd_308479 < baseStart_308479 := by decide
  rcases family_descends (prefixWord ++ tailWord_308479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308505 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_308505 : Nat := 118140960795 + 308505 * 2 ^ 59
def prefixEnd_308505 : Nat := 4983230072969 + 3 ^ 40 * 308505 * 2
def baseEnd_308505 : Nat := 158411349315420706468717

theorem tailTrace_308505 : CollatzResearch.WordTrace tailWord_308505 prefixEnd_308505 158411349315420706468717 := by
  unfold tailWord_308505
  simp only [CollatzResearch.WordTrace]
  refine ⟨11252101747346548304366969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7501401164897698869577979 11252101747346548304366969)
  ·
    refine ⟨8439076310509911228275227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11252101747346548304366969 8439076310509911228275227)
    ·
      refine ⟨12658614465764866842412841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8439076310509911228275227 12658614465764866842412841)
      ·
        refine ⟨9493960849323650131809631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12658614465764866842412841 9493960849323650131809631)
        ·
          refine ⟨14240941273985475197714447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9493960849323650131809631 14240941273985475197714447)
          ·
            refine ⟨21361411910978212796571671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240941273985475197714447 21361411910978212796571671)
            ·
              refine ⟨32042117866467319194857507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21361411910978212796571671 32042117866467319194857507)
              ·
                refine ⟨48063176799700978792286261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32042117866467319194857507 48063176799700978792286261)
                ·
                  refine ⟨4505922824971966761776837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48063176799700978792286261 4505922824971966761776837)
                  ·
                    refine ⟨844860529682243767833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4505922824971966761776837 844860529682243767833157)
                    ·
                      refine ⟨158411349315420706468717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 844860529682243767833157 158411349315420706468717)
                      ·
                        rfl

theorem cell23_308505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_308505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308505 prefixEnd_308505 := by exact prefixLift 308505
  have htrace : WordTrace (prefixWord ++ tailWord_308505) baseStart_308505 baseEnd_308505 := by
    simpa [prefixWord, tailWord_308505, baseEnd_308505] using wordTrace_append hprefix tailTrace_308505
  have hstable : (prefixWord ++ tailWord_308505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308505).length < 2 ^ (prefixWord ++ tailWord_308505).sum := by decide
  have hdescent : baseEnd_308505 < baseStart_308505 := by decide
  rcases family_descends (prefixWord ++ tailWord_308505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308562 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_308562 : Nat := 118140960795 + 308562 * 2 ^ 59
def prefixEnd_308562 : Nat := 4983230072969 + 3 ^ 40 * 308562 * 2
def baseEnd_308562 : Nat := 52813539237575661151985

theorem tailTrace_308562 : CollatzResearch.WordTrace tailWord_308562 prefixEnd_308562 52813539237575661151985 := by
  unfold tailWord_308562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813545177035011759797985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7502787138760031359461293 2813545177035011759797985)
  ·
    refine ⟨2110158882776258819848489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2813545177035011759797985 2110158882776258819848489)
    ·
      refine ⟨1582619162082194114886367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2110158882776258819848489 1582619162082194114886367)
      ·
        refine ⟨2373928743123291172329551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582619162082194114886367 2373928743123291172329551)
        ·
          refine ⟨3560893114684936758494327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373928743123291172329551 3560893114684936758494327)
          ·
            refine ⟨5341339672027405137741491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560893114684936758494327 5341339672027405137741491)
            ·
              refine ⟨8012009508041107706612237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341339672027405137741491 8012009508041107706612237)
              ·
                refine ⟨3004503565515415389979589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8012009508041107706612237 3004503565515415389979589)
                ·
                  refine ⟨563344418534140385621173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3004503565515415389979589 563344418534140385621173)
                  ·
                    refine ⟨52813539237575661151985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 563344418534140385621173 52813539237575661151985)
                    ·
                      rfl

theorem cell23_308562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_308562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308562 prefixEnd_308562 := by exact prefixLift 308562
  have htrace : WordTrace (prefixWord ++ tailWord_308562) baseStart_308562 baseEnd_308562 := by
    simpa [prefixWord, tailWord_308562, baseEnd_308562] using wordTrace_append hprefix tailTrace_308562
  have hstable : (prefixWord ++ tailWord_308562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308562).length < 2 ^ (prefixWord ++ tailWord_308562).sum := by decide
  have hdescent : baseEnd_308562 < baseStart_308562 := by decide
  rcases family_descends (prefixWord ++ tailWord_308562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308619 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3]
def baseStart_308619 : Nat := 118140960795 + 308619 * 2 ^ 59
def prefixEnd_308619 : Nat := 4983230072969 + 3 ^ 40 * 308619 * 2
def baseEnd_308619 : Nat := 158469886110033260443193

theorem tailTrace_308619 : CollatzResearch.WordTrace tailWord_308619 prefixEnd_308619 158469886110033260443193 := by
  unfold tailWord_308619
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256259668933545774016911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7504173112622363849344607 11256259668933545774016911)
  ·
    refine ⟨16884389503400318661025367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11256259668933545774016911 16884389503400318661025367)
    ·
      refine ⟨25326584255100477991538051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16884389503400318661025367 25326584255100477991538051)
      ·
        refine ⟨37989876382650716987307077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25326584255100477991538051 37989876382650716987307077)
        ·
          refine ⟨7123101821747009435120077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37989876382650716987307077 7123101821747009435120077)
          ·
            refine ⟨2671163183155128538170029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7123101821747009435120077 2671163183155128538170029)
            ·
              refine ⟨1001686193683173201813761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2671163183155128538170029 1001686193683173201813761)
              ·
                refine ⟨751264645262379901360321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001686193683173201813761 751264645262379901360321)
                ·
                  refine ⟨563448483946784926020241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751264645262379901360321 563448483946784926020241)
                  ·
                    refine ⟨422586362960088694515181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563448483946784926020241 422586362960088694515181)
                    ·
                      refine ⟨158469886110033260443193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 422586362960088694515181 158469886110033260443193)
                      ·
                        rfl

theorem cell23_308619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3].length) (baseStart_308619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308619 prefixEnd_308619 := by exact prefixLift 308619
  have htrace : WordTrace (prefixWord ++ tailWord_308619) baseStart_308619 baseEnd_308619 := by
    simpa [prefixWord, tailWord_308619, baseEnd_308619] using wordTrace_append hprefix tailTrace_308619
  have hstable : (prefixWord ++ tailWord_308619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308619).length < 2 ^ (prefixWord ++ tailWord_308619).sum := by decide
  have hdescent : baseEnd_308619 < baseStart_308619 := by decide
  rcases family_descends (prefixWord ++ tailWord_308619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308639 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 6]
def baseStart_308639 : Nat := 118140960795 + 308639 * 2 ^ 59
def prefixEnd_308639 : Nat := 4983230072969 + 3 ^ 40 * 308639 * 2
def baseEnd_308639 : Nat := 17608906191458131354789

theorem tailTrace_308639 : CollatzResearch.WordTrace tailWord_308639 prefixEnd_308639 17608906191458131354789 := by
  unfold tailWord_308639
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256989128861089189744971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7504659419240726126496647 11256989128861089189744971)
  ·
    refine ⟨16885483693291633784617457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11256989128861089189744971 16885483693291633784617457)
    ·
      refine ⟨12664112769968725338463093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16885483693291633784617457 12664112769968725338463093)
      ·
        refine ⟨1187260572184568000480915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12664112769968725338463093 1187260572184568000480915)
        ·
          refine ⟨1780890858276852000721373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187260572184568000480915 1780890858276852000721373)
          ·
            refine ⟨667834071853819500270515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1780890858276852000721373 667834071853819500270515)
            ·
              refine ⟨1001751107780729250405773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667834071853819500270515 1001751107780729250405773)
              ·
                refine ⟨375656665417773468902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001751107780729250405773 375656665417773468902165)
                ·
                  refine ⟨17608906191458131354789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375656665417773468902165 17608906191458131354789)
                  ·
                    rfl

theorem cell23_308639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 6].length) (baseStart_308639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308639 prefixEnd_308639 := by exact prefixLift 308639
  have htrace : WordTrace (prefixWord ++ tailWord_308639) baseStart_308639 baseEnd_308639 := by
    simpa [prefixWord, tailWord_308639, baseEnd_308639] using wordTrace_append hprefix tailTrace_308639
  have hstable : (prefixWord ++ tailWord_308639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308639).length < 2 ^ (prefixWord ++ tailWord_308639).sum := by decide
  have hdescent : baseEnd_308639 < baseStart_308639 := by decide
  rcases family_descends (prefixWord ++ tailWord_308639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308653 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_308653 : Nat := 118140960795 + 308653 * 2 ^ 59
def prefixEnd_308653 : Nat := 4983230072969 + 3 ^ 40 * 308653 * 2
def baseEnd_308653 : Nat := 158487344452286127418037

theorem tailTrace_308653 : CollatzResearch.WordTrace tailWord_308653 prefixEnd_308653 158487344452286127418037 := by
  unfold tailWord_308653
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257499750810369580754613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7504999833873579720503075 11257499750810369580754613)
  ·
    refine ⟨1055390601638472148195745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11257499750810369580754613 1055390601638472148195745)
    ·
      refine ⟨791542951228854111146809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055390601638472148195745 791542951228854111146809)
      ·
        refine ⟨593657213421640583360107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791542951228854111146809 593657213421640583360107)
        ·
          refine ⟨890485820132460875040161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593657213421640583360107 890485820132460875040161)
          ·
            refine ⟨667864365099345656280121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890485820132460875040161 667864365099345656280121)
            ·
              refine ⟨500898273824509242210091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667864365099345656280121 500898273824509242210091)
              ·
                refine ⟨751347410736763863315137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500898273824509242210091 751347410736763863315137)
                ·
                  refine ⟨563510558052572897486353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751347410736763863315137 563510558052572897486353)
                  ·
                    refine ⟨422632918539429673114765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563510558052572897486353 422632918539429673114765)
                    ·
                      refine ⟨158487344452286127418037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 422632918539429673114765 158487344452286127418037)
                      ·
                        rfl

theorem cell23_308653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_308653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308653 prefixEnd_308653 := by exact prefixLift 308653
  have htrace : WordTrace (prefixWord ++ tailWord_308653) baseStart_308653 baseEnd_308653 := by
    simpa [prefixWord, tailWord_308653, baseEnd_308653] using wordTrace_append hprefix tailTrace_308653
  have hstable : (prefixWord ++ tailWord_308653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308653).length < 2 ^ (prefixWord ++ tailWord_308653).sum := by decide
  have hdescent : baseEnd_308653 < baseStart_308653 := by decide
  rcases family_descends (prefixWord ++ tailWord_308653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308659 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 5, 2]
def baseStart_308659 : Nat := 118140960795 + 308659 * 2 ^ 59
def prefixEnd_308659 : Nat := 4983230072969 + 3 ^ 40 * 308659 * 2
def baseEnd_308659 : Nat := 158490425336213103943009

theorem tailTrace_308659 : CollatzResearch.WordTrace tailWord_308659 prefixEnd_308659 158490425336213103943009 := by
  unfold tailWord_308659
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257718588788632605473031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7505145725859088403648687 11257718588788632605473031)
  ·
    refine ⟨16886577883182948908209547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11257718588788632605473031 16886577883182948908209547)
    ·
      refine ⟨25329866824774423362314321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16886577883182948908209547 25329866824774423362314321)
      ·
        refine ⟨18997400118580817521735741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25329866824774423362314321 18997400118580817521735741)
        ·
          refine ⟨7124025044467806570650903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18997400118580817521735741 7124025044467806570650903)
          ·
            refine ⟨10686037566701709855976355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124025044467806570650903 10686037566701709855976355)
            ·
              refine ⟨16029056350052564783964533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10686037566701709855976355 16029056350052564783964533)
              ·
                refine ⟨1502724032817427948496675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16029056350052564783964533 1502724032817427948496675)
                ·
                  refine ⟨2254086049226141922745013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502724032817427948496675 2254086049226141922745013)
                  ·
                    refine ⟨211320567114950805257345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2254086049226141922745013 211320567114950805257345)
                    ·
                      refine ⟨158490425336213103943009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211320567114950805257345 158490425336213103943009)
                      ·
                        rfl

theorem cell23_308659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 5, 2].length) (baseStart_308659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308659 prefixEnd_308659 := by exact prefixLift 308659
  have htrace : WordTrace (prefixWord ++ tailWord_308659) baseStart_308659 baseEnd_308659 := by
    simpa [prefixWord, tailWord_308659, baseEnd_308659] using wordTrace_append hprefix tailTrace_308659
  have hstable : (prefixWord ++ tailWord_308659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308659).length < 2 ^ (prefixWord ++ tailWord_308659).sum := by decide
  have hdescent : baseEnd_308659 < baseStart_308659 := by decide
  rcases family_descends (prefixWord ++ tailWord_308659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308689 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_308689 : Nat := 118140960795 + 308689 * 2 ^ 59
def prefixEnd_308689 : Nat := 4983230072969 + 3 ^ 40 * 308689 * 2
def baseEnd_308689 : Nat := 158505829755847986567871

theorem tailTrace_308689 : CollatzResearch.WordTrace tailWord_308689 prefixEnd_308689 158505829755847986567871 := by
  unfold tailWord_308689
  simp only [CollatzResearch.WordTrace]
  refine ⟨11258812778679947729065121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7505875185786631819376747 11258812778679947729065121)
  ·
    refine ⟨8444109584009960796798841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11258812778679947729065121 8444109584009960796798841)
    ·
      refine ⟨6333082188007470597599131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8444109584009960796798841 6333082188007470597599131)
      ·
        refine ⟨9499623282011205896398697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333082188007470597599131 9499623282011205896398697)
        ·
          refine ⟨7124717461508404422299023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9499623282011205896398697 7124717461508404422299023)
          ·
            refine ⟨10687076192262606633448535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124717461508404422299023 10687076192262606633448535)
            ·
              refine ⟨16030614288393909950172803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10687076192262606633448535 16030614288393909950172803)
              ·
                refine ⟨24045921432590864925259205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16030614288393909950172803 24045921432590864925259205)
                ·
                  refine ⟨4508610268610787173486101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24045921432590864925259205 4508610268610787173486101)
                  ·
                    refine ⟨211341106341130648757161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4508610268610787173486101 211341106341130648757161)
                    ·
                      refine ⟨158505829755847986567871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211341106341130648757161 158505829755847986567871)
                      ·
                        rfl

theorem cell23_308689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_308689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308689 prefixEnd_308689 := by exact prefixLift 308689
  have htrace : WordTrace (prefixWord ++ tailWord_308689) baseStart_308689 baseEnd_308689 := by
    simpa [prefixWord, tailWord_308689, baseEnd_308689] using wordTrace_append hprefix tailTrace_308689
  have hstable : (prefixWord ++ tailWord_308689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308689).length < 2 ^ (prefixWord ++ tailWord_308689).sum := by decide
  have hdescent : baseEnd_308689 < baseStart_308689 := by decide
  rcases family_descends (prefixWord ++ tailWord_308689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308717 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_308717 : Nat := 118140960795 + 308717 * 2 ^ 59
def prefixEnd_308717 : Nat := 4983230072969 + 3 ^ 40 * 308717 * 2
def baseEnd_308717 : Nat := 158520207214173877017743

theorem tailTrace_308717 : CollatzResearch.WordTrace tailWord_308717 prefixEnd_308717 158520207214173877017743 := by
  unfold tailWord_308717
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259834022578508511084405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7506556015052339007389603 11259834022578508511084405)
  ·
    refine ⟨1055609439616735172914163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11259834022578508511084405 1055609439616735172914163)
    ·
      refine ⟨1583414159425102759371245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055609439616735172914163 1583414159425102759371245)
      ·
        refine ⟨593780309784413534764217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1583414159425102759371245 593780309784413534764217)
        ·
          refine ⟨445335232338310151073163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 593780309784413534764217 445335232338310151073163)
          ·
            refine ⟨668002848507465226609745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445335232338310151073163 668002848507465226609745)
            ·
              refine ⟨501002136380598919957309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668002848507465226609745 501002136380598919957309)
              ·
                refine ⟨187875801142724594983991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501002136380598919957309 187875801142724594983991)
                ·
                  refine ⟨281813701714086892475987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187875801142724594983991 281813701714086892475987)
                  ·
                    refine ⟨422720552571130338713981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 281813701714086892475987 422720552571130338713981)
                    ·
                      refine ⟨158520207214173877017743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 422720552571130338713981 158520207214173877017743)
                      ·
                        rfl

theorem cell23_308717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_308717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308717 prefixEnd_308717 := by exact prefixLift 308717
  have htrace : WordTrace (prefixWord ++ tailWord_308717) baseStart_308717 baseEnd_308717 := by
    simpa [prefixWord, tailWord_308717, baseEnd_308717] using wordTrace_append hprefix tailTrace_308717
  have hstable : (prefixWord ++ tailWord_308717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308717).length < 2 ^ (prefixWord ++ tailWord_308717).sum := by decide
  have hdescent : baseEnd_308717 < baseStart_308717 := by decide
  rcases family_descends (prefixWord ++ tailWord_308717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308719 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_308719 : Nat := 118140960795 + 308719 * 2 ^ 59
def prefixEnd_308719 : Nat := 4983230072969 + 3 ^ 40 * 308719 * 2
def baseEnd_308719 : Nat := 158521234175482869192733

theorem tailTrace_308719 : CollatzResearch.WordTrace tailWord_308719 prefixEnd_308719 158521234175482869192733 := by
  unfold tailWord_308719
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259906968571262852657211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7506604645714175235104807 11259906968571262852657211)
  ·
    refine ⟨16889860452856894278985817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259906968571262852657211 16889860452856894278985817)
    ·
      refine ⟨12667395339642670709239363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16889860452856894278985817 12667395339642670709239363)
      ·
        refine ⟨19001093009464006063859045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12667395339642670709239363 19001093009464006063859045)
        ·
          refine ⟨3562704939274501136973571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19001093009464006063859045 3562704939274501136973571)
          ·
            refine ⟨5344057408911751705460357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562704939274501136973571 5344057408911751705460357)
            ·
              refine ⟨1002010764170953444773817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5344057408911751705460357 1002010764170953444773817)
              ·
                refine ⟨751508073128215083580363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002010764170953444773817 751508073128215083580363)
                ·
                  refine ⟨1127262109692322625370545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751508073128215083580363 1127262109692322625370545)
                  ·
                    refine ⟨845446582269241969027909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127262109692322625370545 845446582269241969027909)
                    ·
                      refine ⟨158521234175482869192733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 845446582269241969027909 158521234175482869192733)
                      ·
                        rfl

theorem cell23_308719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_308719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308719 prefixEnd_308719 := by exact prefixLift 308719
  have htrace : WordTrace (prefixWord ++ tailWord_308719) baseStart_308719 baseEnd_308719 := by
    simpa [prefixWord, tailWord_308719, baseEnd_308719] using wordTrace_append hprefix tailTrace_308719
  have hstable : (prefixWord ++ tailWord_308719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308719).length < 2 ^ (prefixWord ++ tailWord_308719).sum := by decide
  have hdescent : baseEnd_308719 < baseStart_308719 := by decide
  rcases family_descends (prefixWord ++ tailWord_308719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308733 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_308733 : Nat := 118140960795 + 308733 * 2 ^ 59
def prefixEnd_308733 : Nat := 4983230072969 + 3 ^ 40 * 308733 * 2
def baseEnd_308733 : Nat := 52842807634881938139223

theorem tailTrace_308733 : CollatzResearch.WordTrace tailWord_308733 prefixEnd_308733 52842807634881938139223 := by
  unfold tailWord_308733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11260417590520543243666853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7506945060347028829111235 11260417590520543243666853)
  ·
    refine ⟨2111328298222601858187535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11260417590520543243666853 2111328298222601858187535)
    ·
      refine ⟨3166992447333902787281303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2111328298222601858187535 3166992447333902787281303)
      ·
        refine ⟨4750488671000854180921955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166992447333902787281303 4750488671000854180921955)
        ·
          refine ⟨7125733006501281271382933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750488671000854180921955 7125733006501281271382933)
          ·
            refine ⟨334018734679747559596075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7125733006501281271382933 334018734679747559596075)
            ·
              refine ⟨501028102019621339394113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334018734679747559596075 501028102019621339394113)
              ·
                refine ⟨375771076514716004545585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501028102019621339394113 375771076514716004545585)
                ·
                  refine ⟨281828307386037003409189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375771076514716004545585 281828307386037003409189)
                  ·
                    refine ⟨52842807634881938139223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281828307386037003409189 52842807634881938139223)
                    ·
                      rfl

theorem cell23_308733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_308733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308733 prefixEnd_308733 := by exact prefixLift 308733
  have htrace : WordTrace (prefixWord ++ tailWord_308733) baseStart_308733 baseEnd_308733 := by
    simpa [prefixWord, tailWord_308733, baseEnd_308733] using wordTrace_append hprefix tailTrace_308733
  have hstable : (prefixWord ++ tailWord_308733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308733).length < 2 ^ (prefixWord ++ tailWord_308733).sum := by decide
  have hdescent : baseEnd_308733 < baseStart_308733 := by decide
  rcases family_descends (prefixWord ++ tailWord_308733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308750 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_308750 : Nat := 118140960795 + 308750 * 2 ^ 59
def prefixEnd_308750 : Nat := 4983230072969 + 3 ^ 40 * 308750 * 2
def baseEnd_308750 : Nat := 52845717358590749301697

theorem tailTrace_308750 : CollatzResearch.WordTrace tailWord_308750 prefixEnd_308750 52845717358590749301697 := by
  unfold tailWord_308750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407629703932369393379463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7507358420972636764690469 1407629703932369393379463)
  ·
    refine ⟨2111444555898554090069195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1407629703932369393379463 2111444555898554090069195)
    ·
      refine ⟨3167166833847831135103793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2111444555898554090069195 3167166833847831135103793)
      ·
        refine ⟨2375375125385873351327845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3167166833847831135103793 2375375125385873351327845)
        ·
          refine ⟨445382836009851253373971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2375375125385873351327845 445382836009851253373971)
          ·
            refine ⟨668074254014776880060957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445382836009851253373971 668074254014776880060957)
            ·
              refine ⟨250527845255541330022859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668074254014776880060957 250527845255541330022859)
              ·
                refine ⟨375791767883311995034289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250527845255541330022859 375791767883311995034289)
                ·
                  refine ⟨281843825912483996275717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375791767883311995034289 281843825912483996275717)
                  ·
                    refine ⟨52845717358590749301697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281843825912483996275717 52845717358590749301697)
                    ·
                      rfl

theorem cell23_308750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_308750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308750 prefixEnd_308750 := by exact prefixLift 308750
  have htrace : WordTrace (prefixWord ++ tailWord_308750) baseStart_308750 baseEnd_308750 := by
    simpa [prefixWord, tailWord_308750, baseEnd_308750] using wordTrace_append hprefix tailTrace_308750
  have hstable : (prefixWord ++ tailWord_308750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308750).length < 2 ^ (prefixWord ++ tailWord_308750).sum := by decide
  have hdescent : baseEnd_308750 < baseStart_308750 := by decide
  rcases family_descends (prefixWord ++ tailWord_308750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308752 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_308752 : Nat := 118140960795 + 308752 * 2 ^ 59
def prefixEnd_308752 : Nat := 4983230072969 + 3 ^ 40 * 308752 * 2
def baseEnd_308752 : Nat := 158538179037081240080081

theorem tailTrace_308752 : CollatzResearch.WordTrace tailWord_308752 prefixEnd_308752 158538179037081240080081 := by
  unfold tailWord_308752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5630555288725854744304255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7507407051634472992405673 5630555288725854744304255)
  ·
    refine ⟨8445832933088782116456383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5630555288725854744304255 8445832933088782116456383)
    ·
      refine ⟨12668749399633173174684575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8445832933088782116456383 12668749399633173174684575)
      ·
        refine ⟨19003124099449759762026863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12668749399633173174684575 19003124099449759762026863)
        ·
          refine ⟨28504686149174639643040295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19003124099449759762026863 28504686149174639643040295)
          ·
            refine ⟨42757029223761959464560443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28504686149174639643040295 42757029223761959464560443)
            ·
              refine ⟨64135543835642939196840665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42757029223761959464560443 64135543835642939196840665)
              ·
                refine ⟨48101657876732204397630499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64135543835642939196840665 48101657876732204397630499)
                ·
                  refine ⟨72152486815098306596445749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48101657876732204397630499 72152486815098306596445749)
                  ·
                    refine ⟨6764295638915466243416789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72152486815098306596445749 6764295638915466243416789)
                    ·
                      refine ⟨158538179037081240080081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6764295638915466243416789 158538179037081240080081)
                      ·
                        rfl

theorem cell23_308752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_308752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308752 prefixEnd_308752 := by exact prefixLift 308752
  have htrace : WordTrace (prefixWord ++ tailWord_308752) baseStart_308752 baseEnd_308752 := by
    simpa [prefixWord, tailWord_308752, baseEnd_308752] using wordTrace_append hprefix tailTrace_308752
  have hstable : (prefixWord ++ tailWord_308752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308752).length < 2 ^ (prefixWord ++ tailWord_308752).sum := by decide
  have hdescent : baseEnd_308752 < baseStart_308752 := by decide
  rcases family_descends (prefixWord ++ tailWord_308752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308769 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_308769 : Nat := 118140960795 + 308769 * 2 ^ 59
def prefixEnd_308769 : Nat := 4983230072969 + 3 ^ 40 * 308769 * 2
def baseEnd_308769 : Nat := 158546908208207673567503

theorem tailTrace_308769 : CollatzResearch.WordTrace tailWord_308769 prefixEnd_308769 158546908208207673567503 := by
  unfold tailWord_308769
  simp only [CollatzResearch.WordTrace]
  refine ⟨11261730618390121391977361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7507820412260080927984907 11261730618390121391977361)
  ·
    refine ⟨8446297963792591043983021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11261730618390121391977361 8446297963792591043983021)
    ·
      refine ⟨3167361736422221641493633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8446297963792591043983021 3167361736422221641493633)
      ·
        refine ⟨2375521302316666231120225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3167361736422221641493633 2375521302316666231120225)
        ·
          refine ⟨1781640976737499673340169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375521302316666231120225 1781640976737499673340169)
          ·
            refine ⟨1336230732553124755005127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781640976737499673340169 1336230732553124755005127)
            ·
              refine ⟨2004346098829687132507691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336230732553124755005127 2004346098829687132507691)
              ·
                refine ⟨3006519148244530698761537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004346098829687132507691 3006519148244530698761537)
                ·
                  refine ⟨2254889361183398024071153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006519148244530698761537 2254889361183398024071153)
                  ·
                    refine ⟨1691167020887548518053365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254889361183398024071153 1691167020887548518053365)
                    ·
                      refine ⟨158546908208207673567503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1691167020887548518053365 158546908208207673567503)
                      ·
                        rfl

theorem cell23_308769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_308769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308769 prefixEnd_308769 := by exact prefixLift 308769
  have htrace : WordTrace (prefixWord ++ tailWord_308769) baseStart_308769 baseEnd_308769 := by
    simpa [prefixWord, tailWord_308769, baseEnd_308769] using wordTrace_append hprefix tailTrace_308769
  have hstable : (prefixWord ++ tailWord_308769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308769).length < 2 ^ (prefixWord ++ tailWord_308769).sum := by decide
  have hdescent : baseEnd_308769 < baseStart_308769 := by decide
  rcases family_descends (prefixWord ++ tailWord_308769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308807 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_308807 : Nat := 118140960795 + 308807 * 2 ^ 59
def prefixEnd_308807 : Nat := 4983230072969 + 3 ^ 40 * 308807 * 2
def baseEnd_308807 : Nat := 158566420473078524892329

theorem tailTrace_308807 : CollatzResearch.WordTrace tailWord_308807 prefixEnd_308807 158566420473078524892329 := by
  unfold tailWord_308807
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263116592252453881860675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7508744394834969254573783 11263116592252453881860675)
  ·
    refine ⟨16894674888378680822791013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11263116592252453881860675 16894674888378680822791013)
    ·
      refine ⟨3167751541571002654273315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16894674888378680822791013 3167751541571002654273315)
      ·
        refine ⟨4751627312356503981409973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167751541571002654273315 4751627312356503981409973)
        ·
          refine ⟨445465060533422248257185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4751627312356503981409973 445465060533422248257185)
          ·
            refine ⟨334098795400066686192889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445465060533422248257185 334098795400066686192889)
            ·
              refine ⟨250574096550050014644667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334098795400066686192889 250574096550050014644667)
              ·
                refine ⟨375861144825075021967001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250574096550050014644667 375861144825075021967001)
                ·
                  refine ⟨281895858618806266475251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375861144825075021967001 281895858618806266475251)
                  ·
                    refine ⟨422843787928209399712877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 281895858618806266475251 422843787928209399712877)
                    ·
                      refine ⟨158566420473078524892329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 422843787928209399712877 158566420473078524892329)
                      ·
                        rfl

theorem cell23_308807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_308807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308807 prefixEnd_308807 := by exact prefixLift 308807
  have htrace : WordTrace (prefixWord ++ tailWord_308807) baseStart_308807 baseEnd_308807 := by
    simpa [prefixWord, tailWord_308807, baseEnd_308807] using wordTrace_append hprefix tailTrace_308807
  have hstable : (prefixWord ++ tailWord_308807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308807).length < 2 ^ (prefixWord ++ tailWord_308807).sum := by decide
  have hdescent : baseEnd_308807 < baseStart_308807 := by decide
  rcases family_descends (prefixWord ++ tailWord_308807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308809 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_308809 : Nat := 118140960795 + 308809 * 2 ^ 59
def prefixEnd_308809 : Nat := 4983230072969 + 3 ^ 40 * 308809 * 2
def baseEnd_308809 : Nat := 158567447434387517067319

theorem tailTrace_308809 : CollatzResearch.WordTrace tailWord_308809 prefixEnd_308809 158567447434387517067319 := by
  unfold tailWord_308809
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263189538245208223433481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7508793025496805482288987 11263189538245208223433481)
  ·
    refine ⟨8447392153683906167575111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11263189538245208223433481 8447392153683906167575111)
    ·
      refine ⟨12671088230525859251362667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8447392153683906167575111 12671088230525859251362667)
      ·
        refine ⟨19006632345788788877044001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12671088230525859251362667 19006632345788788877044001)
        ·
          refine ⟨14254974259341591657783001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19006632345788788877044001 14254974259341591657783001)
          ·
            refine ⟨10691230694506193743337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14254974259341591657783001 10691230694506193743337251)
            ·
              refine ⟨16036846041759290615005877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10691230694506193743337251 16036846041759290615005877)
              ·
                refine ⟨1503454316414933495156801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16036846041759290615005877 1503454316414933495156801)
                ·
                  refine ⟨1127590737311200121367601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503454316414933495156801 1127590737311200121367601)
                  ·
                    refine ⟨845693052983400091025701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127590737311200121367601 845693052983400091025701)
                    ·
                      refine ⟨158567447434387517067319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 845693052983400091025701 158567447434387517067319)
                      ·
                        rfl

theorem cell23_308809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_308809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308809 prefixEnd_308809 := by exact prefixLift 308809
  have htrace : WordTrace (prefixWord ++ tailWord_308809) baseStart_308809 baseEnd_308809 := by
    simpa [prefixWord, tailWord_308809, baseEnd_308809] using wordTrace_append hprefix tailTrace_308809
  have hstable : (prefixWord ++ tailWord_308809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308809).length < 2 ^ (prefixWord ++ tailWord_308809).sum := by decide
  have hdescent : baseEnd_308809 < baseStart_308809 := by decide
  rcases family_descends (prefixWord ++ tailWord_308809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308859 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_308859 : Nat := 118140960795 + 308859 * 2 ^ 59
def prefixEnd_308859 : Nat := 4983230072969 + 3 ^ 40 * 308859 * 2
def baseEnd_308859 : Nat := 158593121467112321442089

theorem tailTrace_308859 : CollatzResearch.WordTrace tailWord_308859 prefixEnd_308859 158593121467112321442089 := by
  unfold tailWord_308859
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265013188064066762753631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7510008792042711175169087 11265013188064066762753631)
  ·
    refine ⟨16897519782096100144130447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11265013188064066762753631 16897519782096100144130447)
    ·
      refine ⟨25346279673144150216195671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16897519782096100144130447 25346279673144150216195671)
      ·
        refine ⟨38019419509716225324293507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25346279673144150216195671 38019419509716225324293507)
        ·
          refine ⟨57029129264574337986440261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38019419509716225324293507 57029129264574337986440261)
          ·
            refine ⟨10692961737107688372457549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57029129264574337986440261 10692961737107688372457549)
            ·
              refine ⟨4009860651415383139671581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10692961737107688372457549 4009860651415383139671581)
              ·
                refine ⟨1503697744280768677376843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4009860651415383139671581 1503697744280768677376843)
                ·
                  refine ⟨2255546616421153016065265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503697744280768677376843 2255546616421153016065265)
                  ·
                    refine ⟨1691659962315864762048949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2255546616421153016065265 1691659962315864762048949)
                    ·
                      refine ⟨158593121467112321442089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1691659962315864762048949 158593121467112321442089)
                      ·
                        rfl

theorem cell23_308859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_308859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308859 prefixEnd_308859 := by exact prefixLift 308859
  have htrace : WordTrace (prefixWord ++ tailWord_308859) baseStart_308859 baseEnd_308859 := by
    simpa [prefixWord, tailWord_308859, baseEnd_308859] using wordTrace_append hprefix tailTrace_308859
  have hstable : (prefixWord ++ tailWord_308859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308859).length < 2 ^ (prefixWord ++ tailWord_308859).sum := by decide
  have hdescent : baseEnd_308859 < baseStart_308859 := by decide
  rcases family_descends (prefixWord ++ tailWord_308859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308889 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_308889 : Nat := 118140960795 + 308889 * 2 ^ 59
def prefixEnd_308889 : Nat := 4983230072969 + 3 ^ 40 * 308889 * 2
def baseEnd_308889 : Nat := 158608525886747204066951

theorem tailTrace_308889 : CollatzResearch.WordTrace tailWord_308889 prefixEnd_308889 158608525886747204066951 := by
  unfold tailWord_308889
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266107377955381886345721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7510738251970254590897147 11266107377955381886345721)
  ·
    refine ⟨8449580533466536414759291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11266107377955381886345721 8449580533466536414759291)
    ·
      refine ⟨12674370800199804622138937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8449580533466536414759291 12674370800199804622138937)
      ·
        refine ⟨9505778100149853466604203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12674370800199804622138937 9505778100149853466604203)
        ·
          refine ⟨14258667150224780199906305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9505778100149853466604203 14258667150224780199906305)
          ·
            refine ⟨10694000362668585149929729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14258667150224780199906305 10694000362668585149929729)
            ·
              refine ⟨8020500272001438862447297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10694000362668585149929729 8020500272001438862447297)
              ·
                refine ⟨6015375204001079146835473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8020500272001438862447297 6015375204001079146835473)
                ·
                  refine ⟨4511531403000809360126605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015375204001079146835473 4511531403000809360126605)
                  ·
                    refine ⟨1691824276125303510047477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4511531403000809360126605 1691824276125303510047477)
                    ·
                      refine ⟨158608525886747204066951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1691824276125303510047477 158608525886747204066951)
                      ·
                        rfl

theorem cell23_308889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_308889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308889 prefixEnd_308889 := by exact prefixLift 308889
  have htrace : WordTrace (prefixWord ++ tailWord_308889) baseStart_308889 baseEnd_308889 := by
    simpa [prefixWord, tailWord_308889, baseEnd_308889] using wordTrace_append hprefix tailTrace_308889
  have hstable : (prefixWord ++ tailWord_308889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308889).length < 2 ^ (prefixWord ++ tailWord_308889).sum := by decide
  have hdescent : baseEnd_308889 < baseStart_308889 := by decide
  rcases family_descends (prefixWord ++ tailWord_308889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308899 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_308899 : Nat := 118140960795 + 308899 * 2 ^ 59
def prefixEnd_308899 : Nat := 4983230072969 + 3 ^ 40 * 308899 * 2
def baseEnd_308899 : Nat := 158613660693292164941905

theorem tailTrace_308899 : CollatzResearch.WordTrace tailWord_308899 prefixEnd_308899 158613660693292164941905 := by
  unfold tailWord_308899
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266472107919153594209751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7510981405279435729473167 11266472107919153594209751)
  ·
    refine ⟨16899708161878730391314627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11266472107919153594209751 16899708161878730391314627)
    ·
      refine ⟨25349562242818095586971941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16899708161878730391314627 25349562242818095586971941)
      ·
        refine ⟨4753042920528392922557239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25349562242818095586971941 4753042920528392922557239)
        ·
          refine ⟨7129564380792589383835859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753042920528392922557239 7129564380792589383835859)
          ·
            refine ⟨10694346571188884075753789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129564380792589383835859 10694346571188884075753789)
            ·
              refine ⟨4010379964195831528407671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10694346571188884075753789 4010379964195831528407671)
              ·
                refine ⟨6015569946293747292611507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010379964195831528407671 6015569946293747292611507)
                ·
                  refine ⟨9023354919440620938917261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015569946293747292611507 9023354919440620938917261)
                  ·
                    refine ⟨3383758094790232852093973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9023354919440620938917261 3383758094790232852093973)
                    ·
                      refine ⟨158613660693292164941905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3383758094790232852093973 158613660693292164941905)
                      ·
                        rfl

theorem cell23_308899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_308899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308899 prefixEnd_308899 := by exact prefixLift 308899
  have htrace : WordTrace (prefixWord ++ tailWord_308899) baseStart_308899 baseEnd_308899 := by
    simpa [prefixWord, tailWord_308899, baseEnd_308899] using wordTrace_append hprefix tailTrace_308899
  have hstable : (prefixWord ++ tailWord_308899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308899).length < 2 ^ (prefixWord ++ tailWord_308899).sum := by decide
  have hdescent : baseEnd_308899 < baseStart_308899 := by decide
  rcases family_descends (prefixWord ++ tailWord_308899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308936 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_308936 : Nat := 118140960795 + 308936 * 2 ^ 59
def prefixEnd_308936 : Nat := 4983230072969 + 3 ^ 40 * 308936 * 2
def baseEnd_308936 : Nat := 158632659477508520179235

theorem tailTrace_308936 : CollatzResearch.WordTrace tailWord_308936 prefixEnd_308936 158632659477508520179235 := by
  unfold tailWord_308936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633910804392554456653331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7511881072523405942204441 5633910804392554456653331)
  ·
    refine ⟨8450866206588831684979997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5633910804392554456653331 8450866206588831684979997)
    ·
      refine ⟨3169074827470811881867499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8450866206588831684979997 3169074827470811881867499)
      ·
        refine ⟨4753612241206217822801249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169074827470811881867499 4753612241206217822801249)
        ·
          refine ⟨3565209180904663367100937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4753612241206217822801249 3565209180904663367100937)
          ·
            refine ⟨2673906885678497525325703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565209180904663367100937 2673906885678497525325703)
            ·
              refine ⟨4010860328517746287988555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673906885678497525325703 4010860328517746287988555)
              ·
                refine ⟨6016290492776619431982833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010860328517746287988555 6016290492776619431982833)
                ·
                  refine ⟨4512217869582464573987125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6016290492776619431982833 4512217869582464573987125)
                  ·
                    refine ⟨423020425273356053811293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4512217869582464573987125 423020425273356053811293)
                    ·
                      refine ⟨158632659477508520179235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423020425273356053811293 158632659477508520179235)
                      ·
                        rfl

theorem cell23_308936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_308936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308936 prefixEnd_308936 := by exact prefixLift 308936
  have htrace : WordTrace (prefixWord ++ tailWord_308936) baseStart_308936 baseEnd_308936 := by
    simpa [prefixWord, tailWord_308936, baseEnd_308936] using wordTrace_append hprefix tailTrace_308936
  have hstable : (prefixWord ++ tailWord_308936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308936).length < 2 ^ (prefixWord ++ tailWord_308936).sum := by decide
  have hdescent : baseEnd_308936 < baseStart_308936 := by decide
  rcases family_descends (prefixWord ++ tailWord_308936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308939 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 9]
def baseStart_308939 : Nat := 118140960795 + 308939 * 2 ^ 59
def prefixEnd_308939 : Nat := 4983230072969 + 3 ^ 40 * 308939 * 2
def baseEnd_308939 : Nat := 52878066639824002813907

theorem tailTrace_308939 : CollatzResearch.WordTrace tailWord_308939 prefixEnd_308939 52878066639824002813907 := by
  unfold tailWord_308939
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267931027774240425665871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7511954018516160283777247 11267931027774240425665871)
  ·
    refine ⟨16901896541661360638498807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11267931027774240425665871 16901896541661360638498807)
    ·
      refine ⟨25352844812492040957748211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16901896541661360638498807 25352844812492040957748211)
      ·
        refine ⟨38029267218738061436622317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25352844812492040957748211 38029267218738061436622317)
        ·
          refine ⟨14260975207026773038733369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38029267218738061436622317 14260975207026773038733369)
          ·
            refine ⟨10695731405270079779050027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14260975207026773038733369 10695731405270079779050027)
            ·
              refine ⟨16043597107905119668575041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10695731405270079779050027 16043597107905119668575041)
              ·
                refine ⟨12032697830928839751431281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16043597107905119668575041 12032697830928839751431281)
                ·
                  refine ⟨9024523373196629813573461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12032697830928839751431281 9024523373196629813573461)
                  ·
                    refine ⟨52878066639824002813907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9024523373196629813573461 52878066639824002813907)
                    ·
                      rfl

theorem cell23_308939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_308939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308939 prefixEnd_308939 := by exact prefixLift 308939
  have htrace : WordTrace (prefixWord ++ tailWord_308939) baseStart_308939 baseEnd_308939 := by
    simpa [prefixWord, tailWord_308939, baseEnd_308939] using wordTrace_append hprefix tailTrace_308939
  have hstable : (prefixWord ++ tailWord_308939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308939).length < 2 ^ (prefixWord ++ tailWord_308939).sum := by decide
  have hdescent : baseEnd_308939 < baseStart_308939 := by decide
  rcases family_descends (prefixWord ++ tailWord_308939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308957 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_308957 : Nat := 118140960795 + 308957 * 2 ^ 59
def prefixEnd_308957 : Nat := 4983230072969 + 3 ^ 40 * 308957 * 2
def baseEnd_308957 : Nat := 158643442571252938016639

theorem tailTrace_308957 : CollatzResearch.WordTrace tailWord_308957 prefixEnd_308957 158643442571252938016639 := by
  unfold tailWord_308957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11268587541709029499821125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7512391694472686333214083 11268587541709029499821125)
  ·
    refine ⟨2112860164070443031216461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11268587541709029499821125 2112860164070443031216461)
    ·
      refine ⟨792322561526416136706173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2112860164070443031216461 792322561526416136706173)
      ·
        refine ⟨297120960572406051264815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 792322561526416136706173 297120960572406051264815)
        ·
          refine ⟨445681440858609076897223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297120960572406051264815 445681440858609076897223)
          ·
            refine ⟨668522161287913615345835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445681440858609076897223 668522161287913615345835)
            ·
              refine ⟨1002783241931870423018753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668522161287913615345835 1002783241931870423018753)
              ·
                refine ⟨752087431448902817264065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002783241931870423018753 752087431448902817264065)
                ·
                  refine ⟨564065573586677112948049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752087431448902817264065 564065573586677112948049)
                  ·
                    refine ⟨423049180190007834711037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 564065573586677112948049 423049180190007834711037)
                    ·
                      refine ⟨158643442571252938016639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423049180190007834711037 158643442571252938016639)
                      ·
                        rfl

theorem cell23_308957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_308957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308957 prefixEnd_308957 := by exact prefixLift 308957
  have htrace : WordTrace (prefixWord ++ tailWord_308957) baseStart_308957 baseEnd_308957 := by
    simpa [prefixWord, tailWord_308957, baseEnd_308957] using wordTrace_append hprefix tailTrace_308957
  have hstable : (prefixWord ++ tailWord_308957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308957).length < 2 ^ (prefixWord ++ tailWord_308957).sum := by decide
  have hdescent : baseEnd_308957 < baseStart_308957 := by decide
  rcases family_descends (prefixWord ++ tailWord_308957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308970 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_308970 : Nat := 118140960795 + 308970 * 2 ^ 59
def prefixEnd_308970 : Nat := 4983230072969 + 3 ^ 40 * 308970 * 2
def baseEnd_308970 : Nat := 158650117819761387154079

theorem tailTrace_308970 : CollatzResearch.WordTrace tailWord_308970 prefixEnd_308970 158650117819761387154079 := by
  unfold tailWord_308970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817265422665483180011091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7512707793774621813362909 2817265422665483180011091)
  ·
    refine ⟨4225898133998224770016637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2817265422665483180011091 4225898133998224770016637)
    ·
      refine ⟨1584711800249334288756239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4225898133998224770016637 1584711800249334288756239)
      ·
        refine ⟨2377067700374001433134359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584711800249334288756239 2377067700374001433134359)
        ·
          refine ⟨3565601550561002149701539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377067700374001433134359 3565601550561002149701539)
          ·
            refine ⟨5348402325841503224552309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565601550561002149701539 5348402325841503224552309)
            ·
              refine ⟨501412718047640927301779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5348402325841503224552309 501412718047640927301779)
              ·
                refine ⟨752119077071461390952669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501412718047640927301779 752119077071461390952669)
                ·
                  refine ⟨282044653901798021607251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752119077071461390952669 282044653901798021607251)
                  ·
                    refine ⟨423066980852697032410877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282044653901798021607251 423066980852697032410877)
                    ·
                      refine ⟨158650117819761387154079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423066980852697032410877 158650117819761387154079)
                      ·
                        rfl

theorem cell23_308970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_308970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308970 prefixEnd_308970 := by exact prefixLift 308970
  have htrace : WordTrace (prefixWord ++ tailWord_308970) baseStart_308970 baseEnd_308970 := by
    simpa [prefixWord, tailWord_308970, baseEnd_308970] using wordTrace_append hprefix tailTrace_308970
  have hstable : (prefixWord ++ tailWord_308970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308970).length < 2 ^ (prefixWord ++ tailWord_308970).sum := by decide
  have hdescent : baseEnd_308970 < baseStart_308970 := by decide
  rcases family_descends (prefixWord ++ tailWord_308970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308986 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_308986 : Nat := 118140960795 + 308986 * 2 ^ 59
def prefixEnd_308986 : Nat := 4983230072969 + 3 ^ 40 * 308986 * 2
def baseEnd_308986 : Nat := 52886111170077774851335

theorem tailTrace_308986 : CollatzResearch.WordTrace tailWord_308986 prefixEnd_308986 52886111170077774851335 := by
  unfold tailWord_308986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817411314650991863156703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7513096839069311635084541 2817411314650991863156703)
  ·
    refine ⟨4226116971976487794735055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2817411314650991863156703 4226116971976487794735055)
    ·
      refine ⟨6339175457964731692102583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226116971976487794735055 6339175457964731692102583)
      ·
        refine ⟨9508763186947097538153875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339175457964731692102583 9508763186947097538153875)
        ·
          refine ⟨14263144780420646307230813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508763186947097538153875 14263144780420646307230813)
          ·
            refine ⟨5348679292657742365211555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14263144780420646307230813 5348679292657742365211555)
            ·
              refine ⟨8023018938986613547817333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348679292657742365211555 8023018938986613547817333)
              ·
                refine ⟨752158025529995020107875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8023018938986613547817333 752158025529995020107875)
                ·
                  refine ⟨1128237038294992530161813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752158025529995020107875 1128237038294992530161813)
                  ·
                    refine ⟨52886111170077774851335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1128237038294992530161813 52886111170077774851335)
                    ·
                      rfl

theorem cell23_308986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_308986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308986 prefixEnd_308986 := by exact prefixLift 308986
  have htrace : WordTrace (prefixWord ++ tailWord_308986) baseStart_308986 baseEnd_308986 := by
    simpa [prefixWord, tailWord_308986, baseEnd_308986] using wordTrace_append hprefix tailTrace_308986
  have hstable : (prefixWord ++ tailWord_308986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308986).length < 2 ^ (prefixWord ++ tailWord_308986).sum := by decide
  have hdescent : baseEnd_308986 < baseStart_308986 := by decide
  rcases family_descends (prefixWord ++ tailWord_308986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308990 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_308990 : Nat := 118140960795 + 308990 * 2 ^ 59
def prefixEnd_308990 : Nat := 4983230072969 + 3 ^ 40 * 308990 * 2
def baseEnd_308990 : Nat := 52886795810950436301329

theorem tailTrace_308990 : CollatzResearch.WordTrace tailWord_308990 prefixEnd_308990 52886795810950436301329 := by
  unfold tailWord_308990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408723893823684516971553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7513194100392984090514949 1408723893823684516971553)
  ·
    refine ⟨1056542920367763387728665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1408723893823684516971553 1056542920367763387728665)
    ·
      refine ⟨792407190275822540796499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1056542920367763387728665 792407190275822540796499)
      ·
        refine ⟨1188610785413733811194749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792407190275822540796499 1188610785413733811194749)
        ·
          refine ⟨445729044530150179198031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1188610785413733811194749 445729044530150179198031)
          ·
            refine ⟨668593566795225268797047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445729044530150179198031 668593566795225268797047)
            ·
              refine ⟨1002890350192837903195571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668593566795225268797047 1002890350192837903195571)
              ·
                refine ⟨1504335525289256854793357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002890350192837903195571 1504335525289256854793357)
                ·
                  refine ⟨564125821983471320547509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1504335525289256854793357 564125821983471320547509)
                  ·
                    refine ⟨52886795810950436301329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 564125821983471320547509 52886795810950436301329)
                    ·
                      rfl

theorem cell23_308990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_308990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308990 prefixEnd_308990 := by exact prefixLift 308990
  have htrace : WordTrace (prefixWord ++ tailWord_308990) baseStart_308990 baseEnd_308990 := by
    simpa [prefixWord, tailWord_308990, baseEnd_308990] using wordTrace_append hprefix tailTrace_308990
  have hstable : (prefixWord ++ tailWord_308990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308990).length < 2 ^ (prefixWord ++ tailWord_308990).sum := by decide
  have hdescent : baseEnd_308990 < baseStart_308990 := by decide
  rcases family_descends (prefixWord ++ tailWord_308990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308993 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_308993 : Nat := 118140960795 + 308993 * 2 ^ 59
def prefixEnd_308993 : Nat := 4983230072969 + 3 ^ 40 * 308993 * 2
def baseEnd_308993 : Nat := 158661927874814797166473

theorem tailTrace_308993 : CollatzResearch.WordTrace tailWord_308993 prefixEnd_308993 158661927874814797166473 := by
  unfold tailWord_308993
  simp only [CollatzResearch.WordTrace]
  refine ⟨11269900569578607648131633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7513267046385738432087755 11269900569578607648131633)
  ·
    refine ⟨8452425427183955736098725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11269900569578607648131633 8452425427183955736098725)
    ·
      refine ⟨1584829767596991700518511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8452425427183955736098725 1584829767596991700518511)
      ·
        refine ⟨2377244651395487550777767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584829767596991700518511 2377244651395487550777767)
        ·
          refine ⟨3565866977093231326166651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377244651395487550777767 3565866977093231326166651)
          ·
            refine ⟨5348800465639846989249977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565866977093231326166651 5348800465639846989249977)
            ·
              refine ⟨4011600349229885241937483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5348800465639846989249977 4011600349229885241937483)
              ·
                refine ⟨6017400523844827862906225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011600349229885241937483 6017400523844827862906225)
                ·
                  refine ⟨4513050392883620897179669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017400523844827862906225 4513050392883620897179669)
                  ·
                    refine ⟨211549237166419729555297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4513050392883620897179669 211549237166419729555297)
                    ·
                      refine ⟨158661927874814797166473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211549237166419729555297 158661927874814797166473)
                      ·
                        rfl

theorem cell23_308993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_308993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_308993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_308993 prefixEnd_308993 := by exact prefixLift 308993
  have htrace : WordTrace (prefixWord ++ tailWord_308993) baseStart_308993 baseEnd_308993 := by
    simpa [prefixWord, tailWord_308993, baseEnd_308993] using wordTrace_append hprefix tailTrace_308993
  have hstable : (prefixWord ++ tailWord_308993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308993).length < 2 ^ (prefixWord ++ tailWord_308993).sum := by decide
  have hdescent : baseEnd_308993 < baseStart_308993 := by decide
  rcases family_descends (prefixWord ++ tailWord_308993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309013 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_309013 : Nat := 118140960795 + 309013 * 2 ^ 59
def prefixEnd_309013 : Nat := 4983230072969 + 3 ^ 40 * 309013 * 2
def baseEnd_309013 : Nat := 158672197487904718916381

theorem tailTrace_309013 : CollatzResearch.WordTrace tailWord_309013 prefixEnd_309013 158672197487904718916381 := by
  unfold tailWord_309013
  simp only [CollatzResearch.WordTrace]
  refine ⟨11270630029506151063859693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7513753353004100709239795 11270630029506151063859693)
  ·
    refine ⟨4226486261064806648947385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11270630029506151063859693 4226486261064806648947385)
    ·
      refine ⟨3169864695798604986710539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4226486261064806648947385 3169864695798604986710539)
      ·
        refine ⟨4754797043697907480065809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169864695798604986710539 4754797043697907480065809)
        ·
          refine ⟨3566097782773430610049357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4754797043697907480065809 3566097782773430610049357)
          ·
            refine ⟨1337286668540036478768509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3566097782773430610049357 1337286668540036478768509)
            ·
              refine ⟨501482500702513679538191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1337286668540036478768509 501482500702513679538191)
              ·
                refine ⟨752223751053770519307287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501482500702513679538191 752223751053770519307287)
                ·
                  refine ⟨1128335626580655778960931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752223751053770519307287 1128335626580655778960931)
                  ·
                    refine ⟨1692503439870983668441397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1128335626580655778960931 1692503439870983668441397)
                    ·
                      refine ⟨158672197487904718916381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1692503439870983668441397 158672197487904718916381)
                      ·
                        rfl

theorem cell23_309013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_309013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309013 prefixEnd_309013 := by exact prefixLift 309013
  have htrace : WordTrace (prefixWord ++ tailWord_309013) baseStart_309013 baseEnd_309013 := by
    simpa [prefixWord, tailWord_309013, baseEnd_309013] using wordTrace_append hprefix tailTrace_309013
  have hstable : (prefixWord ++ tailWord_309013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309013).length < 2 ^ (prefixWord ++ tailWord_309013).sum := by decide
  have hdescent : baseEnd_309013 < baseStart_309013 := by decide
  rcases family_descends (prefixWord ++ tailWord_309013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309020 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_309020 : Nat := 118140960795 + 309020 * 2 ^ 59
def prefixEnd_309020 : Nat := 4983230072969 + 3 ^ 40 * 309020 * 2
def baseEnd_309020 : Nat := 52891930617495397176283

theorem tailTrace_309020 : CollatzResearch.WordTrace tailWord_309020 prefixEnd_309020 52891930617495397176283 := by
  unfold tailWord_309020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635442670240395629682257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7513923560320527506243009 5635442670240395629682257)
  ·
    refine ⟨4226582002680296722261693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5635442670240395629682257 4226582002680296722261693)
    ·
      refine ⟨1584968251005111270848135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4226582002680296722261693 1584968251005111270848135)
      ·
        refine ⟨2377452376507666906272203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584968251005111270848135 2377452376507666906272203)
        ·
          refine ⟨3566178564761500359408305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377452376507666906272203 3566178564761500359408305)
          ·
            refine ⟨2674633923571125269556229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566178564761500359408305 2674633923571125269556229)
            ·
              refine ⟨501493860669585988041793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2674633923571125269556229 501493860669585988041793)
              ·
                refine ⟨376120395502189491031345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501493860669585988041793 376120395502189491031345)
                ·
                  refine ⟨282090296626642118273509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376120395502189491031345 282090296626642118273509)
                  ·
                    refine ⟨52891930617495397176283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282090296626642118273509 52891930617495397176283)
                    ·
                      rfl

theorem cell23_309020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_309020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309020 prefixEnd_309020 := by exact prefixLift 309020
  have htrace : WordTrace (prefixWord ++ tailWord_309020) baseStart_309020 baseEnd_309020 := by
    simpa [prefixWord, tailWord_309020, baseEnd_309020] using wordTrace_append hprefix tailTrace_309020
  have hstable : (prefixWord ++ tailWord_309020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309020).length < 2 ^ (prefixWord ++ tailWord_309020).sum := by decide
  have hdescent : baseEnd_309020 < baseStart_309020 := by decide
  rcases family_descends (prefixWord ++ tailWord_309020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309044 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_309044 : Nat := 118140960795 + 309044 * 2 ^ 59
def prefixEnd_309044 : Nat := 4983230072969 + 3 ^ 40 * 309044 * 2
def baseEnd_309044 : Nat := 158688115388194097628739

theorem tailTrace_309044 : CollatzResearch.WordTrace tailWord_309044 prefixEnd_309044 158688115388194097628739 := by
  unfold tailWord_309044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635880346196921679119093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7514507128262562238825457 5635880346196921679119093)
  ·
    refine ⟨528363782455961407417415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5635880346196921679119093 528363782455961407417415)
    ·
      refine ⟨792545673683942111126123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528363782455961407417415 792545673683942111126123)
      ·
        refine ⟨1188818510525913166689185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792545673683942111126123 1188818510525913166689185)
        ·
          refine ⟨891613882894434875016889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188818510525913166689185 891613882894434875016889)
          ·
            refine ⟨668710412170826156262667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891613882894434875016889 668710412170826156262667)
            ·
              refine ⟨1003065618256239234394001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668710412170826156262667 1003065618256239234394001)
              ·
                refine ⟨752299213692179425795501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003065618256239234394001 752299213692179425795501)
                ·
                  refine ⟨282112205134567284673313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752299213692179425795501 282112205134567284673313)
                  ·
                    refine ⟨211584153850925463504985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 282112205134567284673313 211584153850925463504985)
                    ·
                      refine ⟨158688115388194097628739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211584153850925463504985 158688115388194097628739)
                      ·
                        rfl

theorem cell23_309044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_309044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309044 prefixEnd_309044 := by exact prefixLift 309044
  have htrace : WordTrace (prefixWord ++ tailWord_309044) baseStart_309044 baseEnd_309044 := by
    simpa [prefixWord, tailWord_309044, baseEnd_309044] using wordTrace_append hprefix tailTrace_309044
  have hstable : (prefixWord ++ tailWord_309044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309044).length < 2 ^ (prefixWord ++ tailWord_309044).sum := by decide
  have hdescent : baseEnd_309044 < baseStart_309044 := by decide
  rcases family_descends (prefixWord ++ tailWord_309044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309077 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_309077 : Nat := 118140960795 + 309077 * 2 ^ 59
def prefixEnd_309077 : Nat := 4983230072969 + 3 ^ 40 * 309077 * 2
def baseEnd_309077 : Nat := 158705060249792468516087

theorem tailTrace_309077 : CollatzResearch.WordTrace tailWord_309077 prefixEnd_309077 158705060249792468516087 := by
  unfold tailWord_309077
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272964301274289994189485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7515309534182859996126323 11272964301274289994189485)
  ·
    refine ⟨4227361612977858747821057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11272964301274289994189485 4227361612977858747821057)
    ·
      refine ⟨3170521209733394060865793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4227361612977858747821057 3170521209733394060865793)
      ·
        refine ⟨2377890907300045545649345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3170521209733394060865793 2377890907300045545649345)
        ·
          refine ⟨1783418180475034159237009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2377890907300045545649345 1783418180475034159237009)
          ·
            refine ⟨1337563635356275619427757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783418180475034159237009 1337563635356275619427757)
            ·
              refine ⟨501586363258603357285409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1337563635356275619427757 501586363258603357285409)
              ·
                refine ⟨376189772443952517964057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501586363258603357285409 376189772443952517964057)
                ·
                  refine ⟨282142329332964388473043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376189772443952517964057 282142329332964388473043)
                  ·
                    refine ⟨423213493999446582709565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282142329332964388473043 423213493999446582709565)
                    ·
                      refine ⟨158705060249792468516087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423213493999446582709565 158705060249792468516087)
                      ·
                        rfl

theorem cell23_309077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_309077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309077 prefixEnd_309077 := by exact prefixLift 309077
  have htrace : WordTrace (prefixWord ++ tailWord_309077) baseStart_309077 baseEnd_309077 := by
    simpa [prefixWord, tailWord_309077, baseEnd_309077] using wordTrace_append hprefix tailTrace_309077
  have hstable : (prefixWord ++ tailWord_309077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309077).length < 2 ^ (prefixWord ++ tailWord_309077).sum := by decide
  have hdescent : baseEnd_309077 < baseStart_309077 := by decide
  rcases family_descends (prefixWord ++ tailWord_309077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309140 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 7]
def baseStart_309140 : Nat := 118140960795 + 309140 * 2 ^ 59
def prefixEnd_309140 : Nat := 4983230072969 + 3 ^ 40 * 309140 * 2
def baseEnd_309140 : Nat := 17637489947891746892033

theorem tailTrace_309140 : CollatzResearch.WordTrace tailWord_309140 prefixEnd_309140 17637489947891746892033 := by
  unfold tailWord_309140
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637631050023025876866437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7516841400030701169155249 5637631050023025876866437)
  ·
    refine ⟨1057055821879317351912457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5637631050023025876866437 1057055821879317351912457)
    ·
      refine ⟨792791866409488013934343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057055821879317351912457 792791866409488013934343)
      ·
        refine ⟨1189187799614232020901515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792791866409488013934343 1189187799614232020901515)
        ·
          refine ⟨1783781699421348031352273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189187799614232020901515 1783781699421348031352273)
          ·
            refine ⟨1337836274566011023514205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783781699421348031352273 1337836274566011023514205)
            ·
              refine ⟨501688602962254133817827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1337836274566011023514205 501688602962254133817827)
              ·
                refine ⟨752532904443381200726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501688602962254133817827 752532904443381200726741)
                ·
                  refine ⟨17637489947891746892033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 752532904443381200726741 17637489947891746892033)
                  ·
                    rfl

theorem cell23_309140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_309140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309140 prefixEnd_309140 := by exact prefixLift 309140
  have htrace : WordTrace (prefixWord ++ tailWord_309140) baseStart_309140 baseEnd_309140 := by
    simpa [prefixWord, tailWord_309140, baseEnd_309140] using wordTrace_append hprefix tailTrace_309140
  have hstable : (prefixWord ++ tailWord_309140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309140).length < 2 ^ (prefixWord ++ tailWord_309140).sum := by decide
  have hdescent : baseEnd_309140 < baseStart_309140 := by decide
  rcases family_descends (prefixWord ++ tailWord_309140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309277 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_309277 : Nat := 118140960795 + 309277 * 2 ^ 59
def prefixEnd_309277 : Nat := 4983230072969 + 3 ^ 40 * 309277 * 2
def baseEnd_309277 : Nat := 52935918793563895338389

theorem tailTrace_309277 : CollatzResearch.WordTrace tailWord_309277 prefixEnd_309277 52935918793563895338389 := by
  unfold tailWord_309277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280258900549724151470085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7520172600366482767646723 11280258900549724151470085)
  ·
    refine ⟨2115048543853073278400641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11280258900549724151470085 2115048543853073278400641)
    ·
      refine ⟨1586286407889804958800481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2115048543853073278400641 1586286407889804958800481)
      ·
        refine ⟨1189714805917353719100361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586286407889804958800481 1189714805917353719100361)
        ·
          refine ⟨892286104438015289325271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189714805917353719100361 892286104438015289325271)
          ·
            refine ⟨1338429156657022933987907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892286104438015289325271 1338429156657022933987907)
            ·
              refine ⟨2007643734985534400981861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338429156657022933987907 2007643734985534400981861)
              ·
                refine ⟨376433200309787700184099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2007643734985534400981861 376433200309787700184099)
                ·
                  refine ⟨564649800464681550276149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376433200309787700184099 564649800464681550276149)
                  ·
                    refine ⟨52935918793563895338389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 564649800464681550276149 52935918793563895338389)
                    ·
                      rfl

theorem cell23_309277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_309277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309277 prefixEnd_309277 := by exact prefixLift 309277
  have htrace : WordTrace (prefixWord ++ tailWord_309277) baseStart_309277 baseEnd_309277 := by
    simpa [prefixWord, tailWord_309277, baseEnd_309277] using wordTrace_append hprefix tailTrace_309277
  have hstable : (prefixWord ++ tailWord_309277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309277).length < 2 ^ (prefixWord ++ tailWord_309277).sum := by decide
  have hdescent : baseEnd_309277 < baseStart_309277 := by decide
  rcases family_descends (prefixWord ++ tailWord_309277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309297 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_309297 : Nat := 118140960795 + 309297 * 2 ^ 59
def prefixEnd_309297 : Nat := 4983230072969 + 3 ^ 40 * 309297 * 2
def baseEnd_309297 : Nat := 158818025993781607765075

theorem tailTrace_309297 : CollatzResearch.WordTrace tailWord_309297 prefixEnd_309297 158818025993781607765075 := by
  unfold tailWord_309297
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280988360477267567198145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7520658906984845044798763 11280988360477267567198145)
  ·
    refine ⟨8460741270357950675398609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11280988360477267567198145 8460741270357950675398609)
    ·
      refine ⟨6345555952768463006548957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8460741270357950675398609 6345555952768463006548957)
      ·
        refine ⟨2379583482288173627455859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6345555952768463006548957 2379583482288173627455859)
        ·
          refine ⟨3569375223432260441183789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379583482288173627455859 3569375223432260441183789)
          ·
            refine ⟨1338515708787097665443921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3569375223432260441183789 1338515708787097665443921)
            ·
              refine ⟨1003886781590323249082941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338515708787097665443921 1003886781590323249082941)
              ·
                refine ⟨376457543096371218406103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1003886781590323249082941 376457543096371218406103)
                ·
                  refine ⟨564686314644556827609155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376457543096371218406103 564686314644556827609155)
                  ·
                    refine ⟨847029471966835241413733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564686314644556827609155 847029471966835241413733)
                    ·
                      refine ⟨158818025993781607765075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 847029471966835241413733 158818025993781607765075)
                      ·
                        rfl

theorem cell23_309297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_309297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309297 prefixEnd_309297 := by exact prefixLift 309297
  have htrace : WordTrace (prefixWord ++ tailWord_309297) baseStart_309297 baseEnd_309297 := by
    simpa [prefixWord, tailWord_309297, baseEnd_309297] using wordTrace_append hprefix tailTrace_309297
  have hstable : (prefixWord ++ tailWord_309297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309297).length < 2 ^ (prefixWord ++ tailWord_309297).sum := by decide
  have hdescent : baseEnd_309297 < baseStart_309297 := by decide
  rcases family_descends (prefixWord ++ tailWord_309297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309303 : List Nat := [1, 1, 3, 1, 2, 2, 13]
def baseStart_309303 : Nat := 118140960795 + 309303 * 2 ^ 59
def prefixEnd_309303 : Nat := 4983230072969 + 3 ^ 40 * 309303 * 2
def baseEnd_309303 : Nat := 1960754405897636843087

theorem tailTrace_309303 : CollatzResearch.WordTrace tailWord_309303 prefixEnd_309303 1960754405897636843087 := by
  unfold tailWord_309303
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281207198455530591916563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7520804798970353727944375 11281207198455530591916563)
  ·
    refine ⟨16921810797683295887874845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11281207198455530591916563 16921810797683295887874845)
    ·
      refine ⟨6345679049131235957953067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16921810797683295887874845 6345679049131235957953067)
      ·
        refine ⟨9518518573696853936929601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345679049131235957953067 9518518573696853936929601)
        ·
          refine ⟨7138888930272640452697201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518518573696853936929601 7138888930272640452697201)
          ·
            refine ⟨5354166697704480339522901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7138888930272640452697201 5354166697704480339522901)
            ·
              refine ⟨1960754405897636843087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 5354166697704480339522901 1960754405897636843087)
              ·
                rfl

theorem cell23_309303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 13].length) (baseStart_309303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309303 prefixEnd_309303 := by exact prefixLift 309303
  have htrace : WordTrace (prefixWord ++ tailWord_309303) baseStart_309303 baseEnd_309303 := by
    simpa [prefixWord, tailWord_309303, baseEnd_309303] using wordTrace_append hprefix tailTrace_309303
  have hstable : (prefixWord ++ tailWord_309303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309303).length < 2 ^ (prefixWord ++ tailWord_309303).sum := by decide
  have hdescent : baseEnd_309303 < baseStart_309303 := by decide
  rcases family_descends (prefixWord ++ tailWord_309303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309324 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_309324 : Nat := 118140960795 + 309324 * 2 ^ 59
def prefixEnd_309324 : Nat := 4983230072969 + 3 ^ 40 * 309324 * 2
def baseEnd_309324 : Nat := 52943963323817667375817

theorem tailTrace_309324 : CollatzResearch.WordTrace tailWord_309324 prefixEnd_309324 52943963323817667375817 := by
  unfold tailWord_309324
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640986565689725589215513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7521315420919634118954017 5640986565689725589215513)
  ·
    refine ⟨4230739924267294191911635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5640986565689725589215513 4230739924267294191911635)
    ·
      refine ⟨6346109886400941287867453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230739924267294191911635 6346109886400941287867453)
      ·
        refine ⟨2379791207400352982950295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6346109886400941287867453 2379791207400352982950295)
        ·
          refine ⟨3569686811100529474425443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379791207400352982950295 3569686811100529474425443)
          ·
            refine ⟨5354530216650794211638165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569686811100529474425443 5354530216650794211638165)
            ·
              refine ⟨250993603905505978670539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5354530216650794211638165 250993603905505978670539)
              ·
                refine ⟨376490405858258968005809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250993603905505978670539 376490405858258968005809)
                ·
                  refine ⟨282367804393694226004357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376490405858258968005809 282367804393694226004357)
                  ·
                    refine ⟨52943963323817667375817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282367804393694226004357 52943963323817667375817)
                    ·
                      rfl

theorem cell23_309324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_309324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309324 prefixEnd_309324 := by exact prefixLift 309324
  have htrace : WordTrace (prefixWord ++ tailWord_309324) baseStart_309324 baseEnd_309324 := by
    simpa [prefixWord, tailWord_309324, baseEnd_309324] using wordTrace_append hprefix tailTrace_309324
  have hstable : (prefixWord ++ tailWord_309324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309324).length < 2 ^ (prefixWord ++ tailWord_309324).sum := by decide
  have hdescent : baseEnd_309324 < baseStart_309324 := by decide
  rcases family_descends (prefixWord ++ tailWord_309324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309347 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 3]
def baseStart_309347 : Nat := 118140960795 + 309347 * 2 ^ 59
def prefixEnd_309347 : Nat := 4983230072969 + 3 ^ 40 * 309347 * 2
def baseEnd_309347 : Nat := 158843700026506412139845

theorem tailTrace_309347 : CollatzResearch.WordTrace tailWord_309347 prefixEnd_309347 158843700026506412139845 := by
  unfold tailWord_309347
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282812010296126106518295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7521874673530750737678863 11282812010296126106518295)
  ·
    refine ⟨16924218015444189159777443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11282812010296126106518295 16924218015444189159777443)
    ·
      refine ⟨25386327023166283739666165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16924218015444189159777443 25386327023166283739666165)
      ·
        refine ⟨2379968158421839100593703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25386327023166283739666165 2379968158421839100593703)
        ·
          refine ⟨3569952237632758650890555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379968158421839100593703 3569952237632758650890555)
          ·
            refine ⟨5354928356449137976335833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569952237632758650890555 5354928356449137976335833)
            ·
              refine ⟨4016196267336853482251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354928356449137976335833 4016196267336853482251875)
              ·
                refine ⟨6024294401005280223377813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016196267336853482251875 6024294401005280223377813)
                ·
                  refine ⟨282388800047122510470835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6024294401005280223377813 282388800047122510470835)
                  ·
                    refine ⟨423583200070683765706253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282388800047122510470835 423583200070683765706253)
                    ·
                      refine ⟨158843700026506412139845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423583200070683765706253 158843700026506412139845)
                      ·
                        rfl

theorem cell23_309347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_309347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309347 prefixEnd_309347 := by exact prefixLift 309347
  have htrace : WordTrace (prefixWord ++ tailWord_309347) baseStart_309347 baseEnd_309347 := by
    simpa [prefixWord, tailWord_309347, baseEnd_309347] using wordTrace_append hprefix tailTrace_309347
  have hstable : (prefixWord ++ tailWord_309347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309347).length < 2 ^ (prefixWord ++ tailWord_309347).sum := by decide
  have hdescent : baseEnd_309347 < baseStart_309347 := by decide
  rcases family_descends (prefixWord ++ tailWord_309347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309404 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_309404 : Nat := 118140960795 + 309404 * 2 ^ 59
def prefixEnd_309404 : Nat := 4983230072969 + 3 ^ 40 * 309404 * 2
def baseEnd_309404 : Nat := 158872968423812689127083

theorem tailTrace_309404 : CollatzResearch.WordTrace tailWord_309404 prefixEnd_309404 158872968423812689127083 := by
  unfold tailWord_309404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5642445485544812420671633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7523260647393083227562177 5642445485544812420671633)
  ·
    refine ⟨4231834114158609315503725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5642445485544812420671633 4231834114158609315503725)
    ·
      refine ⟨1586937792809478493313897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4231834114158609315503725 1586937792809478493313897)
      ·
        refine ⟨1190203344607108869985423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586937792809478493313897 1190203344607108869985423)
        ·
          refine ⟨1785305016910663304978135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190203344607108869985423 1785305016910663304978135)
          ·
            refine ⟨2677957525365994957467203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785305016910663304978135 2677957525365994957467203)
            ·
              refine ⟨4016936288048992436200805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677957525365994957467203 4016936288048992436200805)
              ·
                refine ⟨753175554009186081787651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4016936288048992436200805 753175554009186081787651)
                ·
                  refine ⟨1129763331013779122681477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753175554009186081787651 1129763331013779122681477)
                  ·
                    refine ⟨211830624565083585502777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129763331013779122681477 211830624565083585502777)
                    ·
                      refine ⟨158872968423812689127083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211830624565083585502777 158872968423812689127083)
                      ·
                        rfl

theorem cell23_309404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_309404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309404 prefixEnd_309404 := by exact prefixLift 309404
  have htrace : WordTrace (prefixWord ++ tailWord_309404) baseStart_309404 baseEnd_309404 := by
    simpa [prefixWord, tailWord_309404, baseEnd_309404] using wordTrace_append hprefix tailTrace_309404
  have hstable : (prefixWord ++ tailWord_309404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309404).length < 2 ^ (prefixWord ++ tailWord_309404).sum := by decide
  have hdescent : baseEnd_309404 < baseStart_309404 := by decide
  rcases family_descends (prefixWord ++ tailWord_309404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309408 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2]
def baseStart_309408 : Nat := 118140960795 + 309408 * 2 ^ 59
def prefixEnd_309408 : Nat := 4983230072969 + 3 ^ 40 * 309408 * 2
def baseEnd_309408 : Nat := 158875022346430673477065

theorem tailTrace_309408 : CollatzResearch.WordTrace tailWord_309408 prefixEnd_309408 158875022346430673477065 := by
  unfold tailWord_309408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5642518431537566762244439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7523357908716755682992585 5642518431537566762244439)
  ·
    refine ⟨8463777647306350143366659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5642518431537566762244439 8463777647306350143366659)
    ·
      refine ⟨12695666470959525215049989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463777647306350143366659 12695666470959525215049989)
      ·
        refine ⟨2380437463304910977821873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12695666470959525215049989 2380437463304910977821873)
        ·
          refine ⟨1785328097478683233366405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380437463304910977821873 1785328097478683233366405)
          ·
            refine ⟨334749018277253106256201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1785328097478683233366405 334749018277253106256201)
            ·
              refine ⟨251061763707939829692151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334749018277253106256201 251061763707939829692151)
              ·
                refine ⟨376592645561909744538227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251061763707939829692151 376592645561909744538227)
                ·
                  refine ⟨564888968342864616807341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376592645561909744538227 564888968342864616807341)
                  ·
                    refine ⟨211833363128574231302753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564888968342864616807341 211833363128574231302753)
                    ·
                      refine ⟨158875022346430673477065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211833363128574231302753 158875022346430673477065)
                      ·
                        rfl

theorem cell23_309408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_309408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309408 prefixEnd_309408 := by exact prefixLift 309408
  have htrace : WordTrace (prefixWord ++ tailWord_309408) baseStart_309408 baseEnd_309408 := by
    simpa [prefixWord, tailWord_309408, baseEnd_309408] using wordTrace_append hprefix tailTrace_309408
  have hstable : (prefixWord ++ tailWord_309408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309408).length < 2 ^ (prefixWord ++ tailWord_309408).sum := by decide
  have hdescent : baseEnd_309408 < baseStart_309408 := by decide
  rcases family_descends (prefixWord ++ tailWord_309408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309415 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_309415 : Nat := 118140960795 + 309415 * 2 ^ 59
def prefixEnd_309415 : Nat := 4983230072969 + 3 ^ 40 * 309415 * 2
def baseEnd_309415 : Nat := 158878616711012146089533

theorem tailTrace_309415 : CollatzResearch.WordTrace tailWord_309415 prefixEnd_309415 158878616711012146089533 := by
  unfold tailWord_309415
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285292174049773719993699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7523528116033182479995799 11285292174049773719993699)
  ·
    refine ⟨16927938261074660579990549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11285292174049773719993699 16927938261074660579990549)
    ·
      refine ⟨793497105987874714687057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16927938261074660579990549 793497105987874714687057)
      ·
        refine ⟨595122829490906036015293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793497105987874714687057 595122829490906036015293)
        ·
          refine ⟨223171061059089763505735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 595122829490906036015293 223171061059089763505735)
          ·
            refine ⟨334756591588634645258603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223171061059089763505735 334756591588634645258603)
            ·
              refine ⟨502134887382951967887905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334756591588634645258603 502134887382951967887905)
              ·
                refine ⟨376601165537213975915929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502134887382951967887905 376601165537213975915929)
                ·
                  refine ⟨282450874152910481936947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376601165537213975915929 282450874152910481936947)
                  ·
                    refine ⟨423676311229365722905421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282450874152910481936947 423676311229365722905421)
                    ·
                      refine ⟨158878616711012146089533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423676311229365722905421 158878616711012146089533)
                      ·
                        rfl

theorem cell23_309415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_309415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309415 prefixEnd_309415 := by exact prefixLift 309415
  have htrace : WordTrace (prefixWord ++ tailWord_309415) baseStart_309415 baseEnd_309415 := by
    simpa [prefixWord, tailWord_309415, baseEnd_309415] using wordTrace_append hprefix tailTrace_309415
  have hstable : (prefixWord ++ tailWord_309415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309415).length < 2 ^ (prefixWord ++ tailWord_309415).sum := by decide
  have hdescent : baseEnd_309415 < baseStart_309415 := by decide
  rcases family_descends (prefixWord ++ tailWord_309415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309438 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_309438 : Nat := 118140960795 + 309438 * 2 ^ 59
def prefixEnd_309438 : Nat := 4983230072969 + 3 ^ 40 * 309438 * 2
def baseEnd_309438 : Nat := 158890426766065556101927

theorem tailTrace_309438 : CollatzResearch.WordTrace tailWord_309438 prefixEnd_309438 158890426766065556101927 := by
  unfold tailWord_309438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410766381620806081010121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7524087368644299098720645 1410766381620806081010121)
  ·
    refine ⟨1058074786215604560757591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1410766381620806081010121 1058074786215604560757591)
    ·
      refine ⟨1587112179323406841136387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058074786215604560757591 1587112179323406841136387)
      ·
        refine ⟨2380668268985110261704581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587112179323406841136387 2380668268985110261704581)
        ·
          refine ⟨446375300434708174069609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2380668268985110261704581 446375300434708174069609)
          ·
            refine ⟨334781475326031130552207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446375300434708174069609 334781475326031130552207)
            ·
              refine ⟨502172212989046695828311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334781475326031130552207 502172212989046695828311)
              ·
                refine ⟨753258319483570043742467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502172212989046695828311 753258319483570043742467)
                ·
                  refine ⟨1129887479225355065613701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753258319483570043742467 1129887479225355065613701)
                  ·
                    refine ⟨211853902354754074802569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129887479225355065613701 211853902354754074802569)
                    ·
                      refine ⟨158890426766065556101927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211853902354754074802569 158890426766065556101927)
                      ·
                        rfl

theorem cell23_309438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_309438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309438 prefixEnd_309438 := by exact prefixLift 309438
  have htrace : WordTrace (prefixWord ++ tailWord_309438) baseStart_309438 baseEnd_309438 := by
    simpa [prefixWord, tailWord_309438, baseEnd_309438] using wordTrace_append hprefix tailTrace_309438
  have hstable : (prefixWord ++ tailWord_309438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309438).length < 2 ^ (prefixWord ++ tailWord_309438).sum := by decide
  have hdescent : baseEnd_309438 < baseStart_309438 := by decide
  rcases family_descends (prefixWord ++ tailWord_309438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309497 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_309497 : Nat := 118140960795 + 309497 * 2 ^ 59
def prefixEnd_309497 : Nat := 4983230072969 + 3 ^ 40 * 309497 * 2
def baseEnd_309497 : Nat := 158920722124680825264155

theorem tailTrace_309497 : CollatzResearch.WordTrace tailWord_309497 prefixEnd_309497 158920722124680825264155 := by
  unfold tailWord_309497
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288282959752701724478745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7525521973168467816319163 11288282959752701724478745)
  ·
    refine ⟨8466212219814526293359059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11288282959752701724478745 8466212219814526293359059)
    ·
      refine ⟨12699318329721789440038589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8466212219814526293359059 12699318329721789440038589)
      ·
        refine ⟨4762244373645671040014471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12699318329721789440038589 4762244373645671040014471)
        ·
          refine ⟨7143366560468506560021707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762244373645671040014471 7143366560468506560021707)
          ·
            refine ⟨10715049840702759840032561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143366560468506560021707 10715049840702759840032561)
            ·
              refine ⟨8036287380527069880024421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10715049840702759840032561 8036287380527069880024421)
              ·
                refine ⟨1506803883848825602504579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8036287380527069880024421 1506803883848825602504579)
                ·
                  refine ⟨2260205825773238403756869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506803883848825602504579 2260205825773238403756869)
                  ·
                    refine ⟨423788592332482200704413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2260205825773238403756869 423788592332482200704413)
                    ·
                      refine ⟨158920722124680825264155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423788592332482200704413 158920722124680825264155)
                      ·
                        rfl

theorem cell23_309497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_309497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309497 prefixEnd_309497 := by exact prefixLift 309497
  have htrace : WordTrace (prefixWord ++ tailWord_309497) baseStart_309497 baseEnd_309497 := by
    simpa [prefixWord, tailWord_309497, baseEnd_309497] using wordTrace_append hprefix tailTrace_309497
  have hstable : (prefixWord ++ tailWord_309497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309497).length < 2 ^ (prefixWord ++ tailWord_309497).sum := by decide
  have hdescent : baseEnd_309497 < baseStart_309497 := by decide
  rcases family_descends (prefixWord ++ tailWord_309497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309514 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_309514 : Nat := 118140960795 + 309514 * 2 ^ 59
def prefixEnd_309514 : Nat := 4983230072969 + 3 ^ 40 * 309514 * 2
def baseEnd_309514 : Nat := 158929451295807258751577

theorem tailTrace_309514 : CollatzResearch.WordTrace tailWord_309514 prefixEnd_309514 158929451295807258751577 := by
  unfold tailWord_309514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822225750172778406961899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7525935333794075751898397 2822225750172778406961899)
  ·
    refine ⟨4233338625259167610442849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2822225750172778406961899 4233338625259167610442849)
    ·
      refine ⟨3175003968944375707832137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4233338625259167610442849 3175003968944375707832137)
      ·
        refine ⟨2381252976708281780874103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175003968944375707832137 2381252976708281780874103)
        ·
          refine ⟨3571879465062422671311155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381252976708281780874103 3571879465062422671311155)
          ·
            refine ⟨5357819197593634006966733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571879465062422671311155 5357819197593634006966733)
            ·
              refine ⟨2009182199097612752612525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5357819197593634006966733 2009182199097612752612525)
              ·
                refine ⟨753443324661604782229697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2009182199097612752612525 753443324661604782229697)
                ·
                  refine ⟨565082493496203586672273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 753443324661604782229697 565082493496203586672273)
                  ·
                    refine ⟨423811870122152690004205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 565082493496203586672273 423811870122152690004205)
                    ·
                      refine ⟨158929451295807258751577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423811870122152690004205 158929451295807258751577)
                      ·
                        rfl

theorem cell23_309514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_309514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309514 prefixEnd_309514 := by exact prefixLift 309514
  have htrace : WordTrace (prefixWord ++ tailWord_309514) baseStart_309514 baseEnd_309514 := by
    simpa [prefixWord, tailWord_309514, baseEnd_309514] using wordTrace_append hprefix tailTrace_309514
  have hstable : (prefixWord ++ tailWord_309514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309514).length < 2 ^ (prefixWord ++ tailWord_309514).sum := by decide
  have hdescent : baseEnd_309514 < baseStart_309514 := by decide
  rcases family_descends (prefixWord ++ tailWord_309514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309538 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_309538 : Nat := 118140960795 + 309538 * 2 ^ 59
def prefixEnd_309538 : Nat := 4983230072969 + 3 ^ 40 * 309538 * 2
def baseEnd_309538 : Nat := 52980591610505054950489

theorem tailTrace_309538 : CollatzResearch.WordTrace tailWord_309538 prefixEnd_309538 52980591610505054950489 := by
  unfold tailWord_309538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822444588151041431680317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7526518901736110484480845 2822444588151041431680317)
  ·
    refine ⟨1058416720556640536880119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2822444588151041431680317 1058416720556640536880119)
    ·
      refine ⟨1587625080834960805320179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058416720556640536880119 1587625080834960805320179)
      ·
        refine ⟨2381437621252441207980269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587625080834960805320179 2381437621252441207980269)
        ·
          refine ⟨893039107969665452992601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2381437621252441207980269 893039107969665452992601)
          ·
            refine ⟨669779330977249089744451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893039107969665452992601 669779330977249089744451)
            ·
              refine ⟨1004668996465873634616677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669779330977249089744451 1004668996465873634616677)
              ·
                refine ⟨188375436837351306490627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1004668996465873634616677 188375436837351306490627)
                ·
                  refine ⟨282563155256026959735941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188375436837351306490627 282563155256026959735941)
                  ·
                    refine ⟨52980591610505054950489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282563155256026959735941 52980591610505054950489)
                    ·
                      rfl

theorem cell23_309538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_309538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309538 prefixEnd_309538 := by exact prefixLift 309538
  have htrace : WordTrace (prefixWord ++ tailWord_309538) baseStart_309538 baseEnd_309538 := by
    simpa [prefixWord, tailWord_309538, baseEnd_309538] using wordTrace_append hprefix tailTrace_309538
  have hstable : (prefixWord ++ tailWord_309538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309538).length < 2 ^ (prefixWord ++ tailWord_309538).sum := by decide
  have hdescent : baseEnd_309538 < baseStart_309538 := by decide
  rcases family_descends (prefixWord ++ tailWord_309538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309557 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_309557 : Nat := 118140960795 + 309557 * 2 ^ 59
def prefixEnd_309557 : Nat := 4983230072969 + 3 ^ 40 * 309557 * 2
def baseEnd_309557 : Nat := 158951530963950590513879

theorem tailTrace_309557 : CollatzResearch.WordTrace tailWord_309557 prefixEnd_309557 158951530963950590513879 := by
  unfold tailWord_309557
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290471339535331971662925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7526980893023554647775283 11290471339535331971662925)
  ·
    refine ⟨4233926752325749489373597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11290471339535331971662925 4233926752325749489373597)
    ·
      refine ⟨1587722532122156058515099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4233926752325749489373597 1587722532122156058515099)
      ·
        refine ⟨2381583798183234087772649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587722532122156058515099 2381583798183234087772649)
        ·
          refine ⟨1786187848637425565829487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2381583798183234087772649 1786187848637425565829487)
          ·
            refine ⟨2679281772956138348744231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786187848637425565829487 2679281772956138348744231)
            ·
              refine ⟨4018922659434207523116347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679281772956138348744231 4018922659434207523116347)
              ·
                refine ⟨6028383989151311284674521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018922659434207523116347 6028383989151311284674521)
                ·
                  refine ⟨4521287991863483463505891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028383989151311284674521 4521287991863483463505891)
                  ·
                    refine ⟨6781931987795225195258837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4521287991863483463505891 6781931987795225195258837)
                    ·
                      refine ⟨158951530963950590513879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6781931987795225195258837 158951530963950590513879)
                      ·
                        rfl

theorem cell23_309557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_309557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309557 prefixEnd_309557 := by exact prefixLift 309557
  have htrace : WordTrace (prefixWord ++ tailWord_309557) baseStart_309557 baseEnd_309557 := by
    simpa [prefixWord, tailWord_309557, baseEnd_309557] using wordTrace_append hprefix tailTrace_309557
  have hstable : (prefixWord ++ tailWord_309557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309557).length < 2 ^ (prefixWord ++ tailWord_309557).sum := by decide
  have hdescent : baseEnd_309557 < baseStart_309557 := by decide
  rcases family_descends (prefixWord ++ tailWord_309557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309561 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 3]
def baseStart_309561 : Nat := 118140960795 + 309561 * 2 ^ 59
def prefixEnd_309561 : Nat := 4983230072969 + 3 ^ 40 * 309561 * 2
def baseEnd_309561 : Nat := 158953584886568574863861

theorem tailTrace_309561 : CollatzResearch.WordTrace tailWord_309561 prefixEnd_309561 158953584886568574863861 := by
  unfold tailWord_309561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290617231520840654808537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7527078154347227103205691 11290617231520840654808537)
  ·
    refine ⟨8467962923640630491106403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11290617231520840654808537 8467962923640630491106403)
    ·
      refine ⟨12701944385460945736659605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8467962923640630491106403 12701944385460945736659605)
      ·
        refine ⟨595403643068481831405919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12701944385460945736659605 595403643068481831405919)
        ·
          refine ⟨893105464602722747108879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595403643068481831405919 893105464602722747108879)
          ·
            refine ⟨1339658196904084120663319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893105464602722747108879 1339658196904084120663319)
            ·
              refine ⟨2009487295356126180994979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339658196904084120663319 2009487295356126180994979)
              ·
                refine ⟨3014230943034189271492469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009487295356126180994979 3014230943034189271492469)
                ·
                  refine ⟨282584150909455244202419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3014230943034189271492469 282584150909455244202419)
                  ·
                    refine ⟨423876226364182866303629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282584150909455244202419 423876226364182866303629)
                    ·
                      refine ⟨158953584886568574863861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 423876226364182866303629 158953584886568574863861)
                      ·
                        rfl

theorem cell23_309561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_309561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309561 prefixEnd_309561 := by exact prefixLift 309561
  have htrace : WordTrace (prefixWord ++ tailWord_309561) baseStart_309561 baseEnd_309561 := by
    simpa [prefixWord, tailWord_309561, baseEnd_309561] using wordTrace_append hprefix tailTrace_309561
  have hstable : (prefixWord ++ tailWord_309561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309561).length < 2 ^ (prefixWord ++ tailWord_309561).sum := by decide
  have hdescent : baseEnd_309561 < baseStart_309561 := by decide
  rcases family_descends (prefixWord ++ tailWord_309561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309564 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_309564 : Nat := 118140960795 + 309564 * 2 ^ 59
def prefixEnd_309564 : Nat := 4983230072969 + 3 ^ 40 * 309564 * 2
def baseEnd_309564 : Nat := 52985041776177354375449

theorem tailTrace_309564 : CollatzResearch.WordTrace tailWord_309564 prefixEnd_309564 52985041776177354375449 := by
  unfold tailWord_309564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645363325254986083583873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7527151100339981444778497 5645363325254986083583873)
  ·
    refine ⟨4234022493941239562687905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5645363325254986083583873 4234022493941239562687905)
    ·
      refine ⟨3175516870455929672015929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4234022493941239562687905 3175516870455929672015929)
      ·
        refine ⟨2381637652841947254011947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175516870455929672015929 2381637652841947254011947)
        ·
          refine ⟨3572456479262920881017921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381637652841947254011947 3572456479262920881017921)
          ·
            refine ⟨2679342359447190660763441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3572456479262920881017921 2679342359447190660763441)
            ·
              refine ⟨2009506769585392995572581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679342359447190660763441 2009506769585392995572581)
              ·
                refine ⟨376782519297261186669859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2009506769585392995572581 376782519297261186669859)
                ·
                  refine ⟨565173778945891780004789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376782519297261186669859 565173778945891780004789)
                  ·
                    refine ⟨52985041776177354375449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 565173778945891780004789 52985041776177354375449)
                    ·
                      rfl

theorem cell23_309564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_309564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309564 prefixEnd_309564 := by exact prefixLift 309564
  have htrace : WordTrace (prefixWord ++ tailWord_309564) baseStart_309564 baseEnd_309564 := by
    simpa [prefixWord, tailWord_309564, baseEnd_309564] using wordTrace_append hprefix tailTrace_309564
  have hstable : (prefixWord ++ tailWord_309564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309564).length < 2 ^ (prefixWord ++ tailWord_309564).sum := by decide
  have hdescent : baseEnd_309564 < baseStart_309564 := by decide
  rcases family_descends (prefixWord ++ tailWord_309564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309571 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 2, 3, 2]
def baseStart_309571 : Nat := 118140960795 + 309571 * 2 ^ 59
def prefixEnd_309571 : Nat := 4983230072969 + 3 ^ 40 * 309571 * 2
def baseEnd_309571 : Nat := 158958719693113535738815

theorem tailTrace_309571 : CollatzResearch.WordTrace tailWord_309571 prefixEnd_309571 158958719693113535738815 := by
  unfold tailWord_309571
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290981961484612362672567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7527321307656408241781711 11290981961484612362672567)
  ·
    refine ⟨16936472942226918544008851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11290981961484612362672567 16936472942226918544008851)
    ·
      refine ⟨25404709413340377816013277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16936472942226918544008851 25404709413340377816013277)
      ·
        refine ⟨9526766030002641681004979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25404709413340377816013277 9526766030002641681004979)
        ·
          refine ⟨14290149045003962521507469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9526766030002641681004979 14290149045003962521507469)
          ·
            refine ⟨5358805891876485945565301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14290149045003962521507469 5358805891876485945565301)
            ·
              refine ⟨502388052363420557396747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5358805891876485945565301 502388052363420557396747)
              ·
                refine ⟨753582078545130836095121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502388052363420557396747 753582078545130836095121)
                ·
                  refine ⟨565186558908848127071341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 753582078545130836095121 565186558908848127071341)
                  ·
                    refine ⟨211944959590818047651753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565186558908848127071341 211944959590818047651753)
                    ·
                      refine ⟨158958719693113535738815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211944959590818047651753 158958719693113535738815)
                      ·
                        rfl

theorem cell23_309571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_309571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309571 prefixEnd_309571 := by exact prefixLift 309571
  have htrace : WordTrace (prefixWord ++ tailWord_309571) baseStart_309571 baseEnd_309571 := by
    simpa [prefixWord, tailWord_309571, baseEnd_309571] using wordTrace_append hprefix tailTrace_309571
  have hstable : (prefixWord ++ tailWord_309571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309571).length < 2 ^ (prefixWord ++ tailWord_309571).sum := by decide
  have hdescent : baseEnd_309571 < baseStart_309571 := by decide
  rcases family_descends (prefixWord ++ tailWord_309571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309604 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_309604 : Nat := 118140960795 + 309604 * 2 ^ 59
def prefixEnd_309604 : Nat := 4983230072969 + 3 ^ 40 * 309604 * 2
def baseEnd_309604 : Nat := 158975664554711906626163

theorem tailTrace_309604 : CollatzResearch.WordTrace tailWord_309604 prefixEnd_309604 158975664554711906626163 := by
  unfold tailWord_309604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646092785182529499311933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7528123713576705999082577 5646092785182529499311933)
  ·
    refine ⟨2117284794443448562241975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5646092785182529499311933 2117284794443448562241975)
    ·
      refine ⟨3175927191665172843362963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117284794443448562241975 3175927191665172843362963)
      ·
        refine ⟨4763890787497759265044445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175927191665172843362963 4763890787497759265044445)
        ·
          refine ⟨1786459045311659724391667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4763890787497759265044445 1786459045311659724391667)
          ·
            refine ⟨2679688567967489586587501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786459045311659724391667 2679688567967489586587501)
            ·
              refine ⟨1004883212987808594970313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2679688567967489586587501 1004883212987808594970313)
              ·
                refine ⟨753662409740856446227735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004883212987808594970313 753662409740856446227735)
                ·
                  refine ⟨1130493614611284669341603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753662409740856446227735 1130493614611284669341603)
                  ·
                    refine ⟨1695740421916927004012405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1130493614611284669341603 1695740421916927004012405)
                    ·
                      refine ⟨158975664554711906626163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1695740421916927004012405 158975664554711906626163)
                      ·
                        rfl

theorem cell23_309604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_309604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309604 prefixEnd_309604 := by exact prefixLift 309604
  have htrace : WordTrace (prefixWord ++ tailWord_309604) baseStart_309604 baseEnd_309604 := by
    simpa [prefixWord, tailWord_309604, baseEnd_309604] using wordTrace_append hprefix tailTrace_309604
  have hstable : (prefixWord ++ tailWord_309604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309604).length < 2 ^ (prefixWord ++ tailWord_309604).sum := by decide
  have hdescent : baseEnd_309604 < baseStart_309604 := by decide
  rcases family_descends (prefixWord ++ tailWord_309604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309618 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_309618 : Nat := 118140960795 + 309618 * 2 ^ 59
def prefixEnd_309618 : Nat := 4983230072969 + 3 ^ 40 * 309618 * 2
def baseEnd_309618 : Nat := 158982853283874851851099

theorem tailTrace_309618 : CollatzResearch.WordTrace tailWord_309618 prefixEnd_309618 158982853283874851851099 := by
  unfold tailWord_309618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823174048078584847408377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7528464128209559593089005 2823174048078584847408377)
  ·
    refine ⟨2117380536058938635556283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2823174048078584847408377 2117380536058938635556283)
    ·
      refine ⟨3176070804088407953334425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117380536058938635556283 3176070804088407953334425)
      ·
        refine ⟨2382053103066305965000819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3176070804088407953334425 2382053103066305965000819)
        ·
          refine ⟨3573079654599458947501229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382053103066305965000819 3573079654599458947501229)
          ·
            refine ⟨1339904870474797105312961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3573079654599458947501229 1339904870474797105312961)
            ·
              refine ⟨1004928652856097828984721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1339904870474797105312961 1004928652856097828984721)
              ·
                refine ⟨753696489642073371738541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004928652856097828984721 753696489642073371738541)
                ·
                  refine ⟨282636183615777514401953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753696489642073371738541 282636183615777514401953)
                  ·
                    refine ⟨211977137711833135801465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 282636183615777514401953 211977137711833135801465)
                    ·
                      refine ⟨158982853283874851851099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 211977137711833135801465 158982853283874851851099)
                      ·
                        rfl

theorem cell23_309618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_309618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309618 prefixEnd_309618 := by exact prefixLift 309618
  have htrace : WordTrace (prefixWord ++ tailWord_309618) baseStart_309618 baseEnd_309618 := by
    simpa [prefixWord, tailWord_309618, baseEnd_309618] using wordTrace_append hprefix tailTrace_309618
  have hstable : (prefixWord ++ tailWord_309618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309618).length < 2 ^ (prefixWord ++ tailWord_309618).sum := by decide
  have hdescent : baseEnd_309618 < baseStart_309618 := by decide
  rcases family_descends (prefixWord ++ tailWord_309618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309637 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_309637 : Nat := 118140960795 + 309637 * 2 ^ 59
def prefixEnd_309637 : Nat := 4983230072969 + 3 ^ 40 * 309637 * 2
def baseEnd_309637 : Nat := 52997536472103425837837

theorem tailTrace_309637 : CollatzResearch.WordTrace tailWord_309637 prefixEnd_309637 52997536472103425837837 := by
  unfold tailWord_309637
  simp only [CollatzResearch.WordTrace]
  refine ⟨11293389179245505634575165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7528926119497003756383443 11293389179245505634575165)
  ·
    refine ⟨4235020942217064612965687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11293389179245505634575165 4235020942217064612965687)
    ·
      refine ⟨6352531413325596919448531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235020942217064612965687 6352531413325596919448531)
      ·
        refine ⟨9528797119988395379172797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352531413325596919448531 9528797119988395379172797)
        ·
          refine ⟨3573298919995648267189799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9528797119988395379172797 3573298919995648267189799)
          ·
            refine ⟨5359948379993472400784699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573298919995648267189799 5359948379993472400784699)
            ·
              refine ⟨8039922569990208601177049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5359948379993472400784699 8039922569990208601177049)
              ·
                refine ⟨6029941927492656450882787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8039922569990208601177049 6029941927492656450882787)
                ·
                  refine ⟨9044912891238984676324181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6029941927492656450882787 9044912891238984676324181)
                  ·
                    refine ⟨52997536472103425837837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9044912891238984676324181 52997536472103425837837)
                    ·
                      rfl

theorem cell23_309637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_309637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309637 prefixEnd_309637 := by exact prefixLift 309637
  have htrace : WordTrace (prefixWord ++ tailWord_309637) baseStart_309637 baseEnd_309637 := by
    simpa [prefixWord, tailWord_309637, baseEnd_309637] using wordTrace_append hprefix tailTrace_309637
  have hstable : (prefixWord ++ tailWord_309637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309637).length < 2 ^ (prefixWord ++ tailWord_309637).sum := by decide
  have hdescent : baseEnd_309637 < baseStart_309637 := by decide
  rcases family_descends (prefixWord ++ tailWord_309637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309652 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_309652 : Nat := 118140960795 + 309652 * 2 ^ 59
def prefixEnd_309652 : Nat := 4983230072969 + 3 ^ 40 * 309652 * 2
def baseEnd_309652 : Nat := 159000311626127718825943

theorem tailTrace_309652 : CollatzResearch.WordTrace tailWord_309652 prefixEnd_309652 159000311626127718825943 := by
  unfold tailWord_309652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646968137095581598185605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7529290849460775464247473 5646968137095581598185605)
  ·
    refine ⟨1058806525705421549659801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5646968137095581598185605 1058806525705421549659801)
    ·
      refine ⟨794104894279066162244851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1058806525705421549659801 794104894279066162244851)
      ·
        refine ⟨1191157341418599243367277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794104894279066162244851 1191157341418599243367277)
        ·
          refine ⟨446684003031974716262729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1191157341418599243367277 446684003031974716262729)
          ·
            refine ⟨335013002273981037197047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446684003031974716262729 335013002273981037197047)
            ·
              refine ⟨502519503410971555795571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335013002273981037197047 502519503410971555795571)
              ·
                refine ⟨753779255116457333693357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502519503410971555795571 753779255116457333693357)
                ·
                  refine ⟨282667220668671500135009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753779255116457333693357 282667220668671500135009)
                  ·
                    refine ⟨212000415501503625101257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 282667220668671500135009 212000415501503625101257)
                    ·
                      refine ⟨159000311626127718825943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212000415501503625101257 159000311626127718825943)
                      ·
                        rfl

theorem cell23_309652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_309652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309652 prefixEnd_309652 := by exact prefixLift 309652
  have htrace : WordTrace (prefixWord ++ tailWord_309652) baseStart_309652 baseEnd_309652 := by
    simpa [prefixWord, tailWord_309652, baseEnd_309652] using wordTrace_append hprefix tailTrace_309652
  have hstable : (prefixWord ++ tailWord_309652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309652).length < 2 ^ (prefixWord ++ tailWord_309652).sum := by decide
  have hdescent : baseEnd_309652 < baseStart_309652 := by decide
  rcases family_descends (prefixWord ++ tailWord_309652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309662 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_309662 : Nat := 118140960795 + 309662 * 2 ^ 59
def prefixEnd_309662 : Nat := 4983230072969 + 3 ^ 40 * 309662 * 2
def baseEnd_309662 : Nat := 53001815477557559900299

theorem tailTrace_309662 : CollatzResearch.WordTrace tailWord_309662 prefixEnd_309662 53001815477557559900299 := by
  unfold tailWord_309662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411787625519366863029405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7529534002769956602823493 1411787625519366863029405)
  ·
    refine ⟨529420359569762573636027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1411787625519366863029405 529420359569762573636027)
    ·
      refine ⟨794130539354643860454041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529420359569762573636027 794130539354643860454041)
      ·
        refine ⟨595597904515982895340531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794130539354643860454041 595597904515982895340531)
        ·
          refine ⟨893396856773974343010797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595597904515982895340531 893396856773974343010797)
          ·
            refine ⟨335023821290240378629049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 893396856773974343010797 335023821290240378629049)
            ·
              refine ⟨251267865967680283971787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335023821290240378629049 251267865967680283971787)
              ·
                refine ⟨376901798951520425957681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251267865967680283971787 376901798951520425957681)
                ·
                  refine ⟨282676349213640319468261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376901798951520425957681 282676349213640319468261)
                  ·
                    refine ⟨53001815477557559900299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282676349213640319468261 53001815477557559900299)
                    ·
                      rfl

theorem cell23_309662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_309662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309662 prefixEnd_309662 := by exact prefixLift 309662
  have htrace : WordTrace (prefixWord ++ tailWord_309662) baseStart_309662 baseEnd_309662 := by
    simpa [prefixWord, tailWord_309662, baseEnd_309662] using wordTrace_append hprefix tailTrace_309662
  have hstable : (prefixWord ++ tailWord_309662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309662).length < 2 ^ (prefixWord ++ tailWord_309662).sum := by decide
  have hdescent : baseEnd_309662 < baseStart_309662 := by decide
  rcases family_descends (prefixWord ++ tailWord_309662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309725 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_309725 : Nat := 118140960795 + 309725 * 2 ^ 59
def prefixEnd_309725 : Nat := 4983230072969 + 3 ^ 40 * 309725 * 2
def baseEnd_309725 : Nat := 159037795713905933213107

theorem tailTrace_309725 : CollatzResearch.WordTrace tailWord_309725 prefixEnd_309725 159037795713905933213107 := by
  unfold tailWord_309725
  simp only [CollatzResearch.WordTrace]
  refine ⟨11296598802926696663778629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7531065868617797775852419 11296598802926696663778629)
  ·
    refine ⟨2118112275548755624458493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11296598802926696663778629 2118112275548755624458493)
    ·
      refine ⟨794292103330783359171935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2118112275548755624458493 794292103330783359171935)
      ·
        refine ⟨1191438154996175038757903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794292103330783359171935 1191438154996175038757903)
        ·
          refine ⟨1787157232494262558136855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191438154996175038757903 1787157232494262558136855)
          ·
            refine ⟨2680735848741393837205283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787157232494262558136855 2680735848741393837205283)
            ·
              refine ⟨4021103773112090755807925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680735848741393837205283 4021103773112090755807925)
              ·
                refine ⟨376978478729258508356993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4021103773112090755807925 376978478729258508356993)
                ·
                  refine ⟨282733859046943881267745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376978478729258508356993 282733859046943881267745)
                  ·
                    refine ⟨212050394285207910950809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 282733859046943881267745 212050394285207910950809)
                    ·
                      refine ⟨159037795713905933213107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212050394285207910950809 159037795713905933213107)
                      ·
                        rfl

theorem cell23_309725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_309725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309725 prefixEnd_309725 := by exact prefixLift 309725
  have htrace : WordTrace (prefixWord ++ tailWord_309725) baseStart_309725 baseEnd_309725 := by
    simpa [prefixWord, tailWord_309725, baseEnd_309725] using wordTrace_append hprefix tailTrace_309725
  have hstable : (prefixWord ++ tailWord_309725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309725).length < 2 ^ (prefixWord ++ tailWord_309725).sum := by decide
  have hdescent : baseEnd_309725 < baseStart_309725 := by decide
  rcases family_descends (prefixWord ++ tailWord_309725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309731 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 7]
def baseStart_309731 : Nat := 118140960795 + 309731 * 2 ^ 59
def prefixEnd_309731 : Nat := 4983230072969 + 3 ^ 40 * 309731 * 2
def baseEnd_309731 : Nat := 17671208510870323304231

theorem tailTrace_309731 : CollatzResearch.WordTrace tailWord_309731 prefixEnd_309731 17671208510870323304231 := by
  unfold tailWord_309731
  simp only [CollatzResearch.WordTrace]
  refine ⟨11296817640904959688497047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7531211760603306458998031 11296817640904959688497047)
  ·
    refine ⟨16945226461357439532745571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11296817640904959688497047 16945226461357439532745571)
    ·
      refine ⟨25417839692036159299118357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16945226461357439532745571 25417839692036159299118357)
      ·
        refine ⟨1191461235564194967146173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25417839692036159299118357 1191461235564194967146173)
        ·
          refine ⟨446797963336573112679815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1191461235564194967146173 446797963336573112679815)
          ·
            refine ⟨670196945004859669019723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446797963336573112679815 670196945004859669019723)
            ·
              refine ⟨1005295417507289503529585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670196945004859669019723 1005295417507289503529585)
              ·
                refine ⟨753971563130467127647189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005295417507289503529585 753971563130467127647189)
                ·
                  refine ⟨17671208510870323304231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 753971563130467127647189 17671208510870323304231)
                  ·
                    rfl

theorem cell23_309731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 7].length) (baseStart_309731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309731 prefixEnd_309731 := by exact prefixLift 309731
  have htrace : WordTrace (prefixWord ++ tailWord_309731) baseStart_309731 baseEnd_309731 := by
    simpa [prefixWord, tailWord_309731, baseEnd_309731] using wordTrace_append hprefix tailTrace_309731
  have hstable : (prefixWord ++ tailWord_309731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309731).length < 2 ^ (prefixWord ++ tailWord_309731).sum := by decide
  have hdescent : baseEnd_309731 < baseStart_309731 := by decide
  rcases family_descends (prefixWord ++ tailWord_309731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309744 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_309744 : Nat := 118140960795 + 309744 * 2 ^ 59
def prefixEnd_309744 : Nat := 4983230072969 + 3 ^ 40 * 309744 * 2
def baseEnd_309744 : Nat := 53015850615447119625173

theorem tailTrace_309744 : CollatzResearch.WordTrace tailWord_309744 prefixEnd_309744 53015850615447119625173 := by
  unfold tailWord_309744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5648645894928931454360143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7531527859905241939146857 5648645894928931454360143)
  ·
    refine ⟨8472968842393397181540215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5648645894928931454360143 8472968842393397181540215)
    ·
      refine ⟨12709453263590095772310323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8472968842393397181540215 12709453263590095772310323)
      ·
        refine ⟨19064179895385143658465485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12709453263590095772310323 19064179895385143658465485)
        ·
          refine ⟨7149067460769428871924557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19064179895385143658465485 7149067460769428871924557)
          ·
            refine ⟨2680900297788535826971709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7149067460769428871924557 2680900297788535826971709)
            ·
              refine ⟨1005337611670700935114391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2680900297788535826971709 1005337611670700935114391)
              ·
                refine ⟨1508006417506051402671587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005337611670700935114391 1508006417506051402671587)
                ·
                  refine ⟨2262009626259077104007381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508006417506051402671587 2262009626259077104007381)
                  ·
                    refine ⟨53015850615447119625173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2262009626259077104007381 53015850615447119625173)
                    ·
                      rfl

theorem cell23_309744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_309744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309744 prefixEnd_309744 := by exact prefixLift 309744
  have htrace : WordTrace (prefixWord ++ tailWord_309744) baseStart_309744 baseEnd_309744 := by
    simpa [prefixWord, tailWord_309744, baseEnd_309744] using wordTrace_append hprefix tailTrace_309744
  have hstable : (prefixWord ++ tailWord_309744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309744).length < 2 ^ (prefixWord ++ tailWord_309744).sum := by decide
  have hdescent : baseEnd_309744 < baseStart_309744 := by decide
  rcases family_descends (prefixWord ++ tailWord_309744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309754 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_309754 : Nat := 118140960795 + 309754 * 2 ^ 59
def prefixEnd_309754 : Nat := 4983230072969 + 3 ^ 40 * 309754 * 2
def baseEnd_309754 : Nat := 159052686652886319750473

theorem tailTrace_309754 : CollatzResearch.WordTrace tailWord_309754 prefixEnd_309754 159052686652886319750473 := by
  unfold tailWord_309754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824414129955408654146079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7531771013214423077722877 2824414129955408654146079)
  ·
    refine ⟨4236621194933112981219119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824414129955408654146079 4236621194933112981219119)
    ·
      refine ⟨6354931792399669471828679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236621194933112981219119 6354931792399669471828679)
      ·
        refine ⟨9532397688599504207743019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354931792399669471828679 9532397688599504207743019)
        ·
          refine ⟨14298596532899256311614529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9532397688599504207743019 14298596532899256311614529)
          ·
            refine ⟨10723947399674442233710897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298596532899256311614529 10723947399674442233710897)
            ·
              refine ⟨8042960549755831675283173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10723947399674442233710897 8042960549755831675283173)
              ·
                refine ⟨1508055103079218439115595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8042960549755831675283173 1508055103079218439115595)
                ·
                  refine ⟨2262082654618827658673393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508055103079218439115595 2262082654618827658673393)
                  ·
                    refine ⟨1696561990964120744005045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262082654618827658673393 1696561990964120744005045)
                    ·
                      refine ⟨159052686652886319750473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1696561990964120744005045 159052686652886319750473)
                      ·
                        rfl

theorem cell23_309754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_309754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309754 prefixEnd_309754 := by exact prefixLift 309754
  have htrace : WordTrace (prefixWord ++ tailWord_309754) baseStart_309754 baseEnd_309754 := by
    simpa [prefixWord, tailWord_309754, baseEnd_309754] using wordTrace_append hprefix tailTrace_309754
  have hstable : (prefixWord ++ tailWord_309754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309754).length < 2 ^ (prefixWord ++ tailWord_309754).sum := by decide
  have hdescent : baseEnd_309754 < baseStart_309754 := by decide
  rcases family_descends (prefixWord ++ tailWord_309754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309799 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 5]
def baseStart_309799 : Nat := 118140960795 + 309799 * 2 ^ 59
def prefixEnd_309799 : Nat := 4983230072969 + 3 ^ 40 * 309799 * 2
def baseEnd_309799 : Nat := 17675088142482071520863

theorem tailTrace_309799 : CollatzResearch.WordTrace tailWord_309799 prefixEnd_309799 17675088142482071520863 := by
  unfold tailWord_309799
  simp only [CollatzResearch.WordTrace]
  refine ⟨11299297804658607301972451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7532865203105738201314967 11299297804658607301972451)
  ·
    refine ⟨16948946706987910952958677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11299297804658607301972451 16948946706987910952958677)
    ·
      refine ⟨397240938445029162959969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16948946706987910952958677 397240938445029162959969)
      ·
        refine ⟨297930703833771872219977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397240938445029162959969 297930703833771872219977)
        ·
          refine ⟨223448027875328904164983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297930703833771872219977 223448027875328904164983)
          ·
            refine ⟨335172041812993356247475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223448027875328904164983 335172041812993356247475)
            ·
              refine ⟨502758062719490034371213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335172041812993356247475 502758062719490034371213)
              ·
                refine ⟨188534273519808762889205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 502758062719490034371213 188534273519808762889205)
                ·
                  refine ⟨17675088142482071520863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188534273519808762889205 17675088142482071520863)
                  ·
                    rfl

theorem cell23_309799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 5].length) (baseStart_309799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309799 prefixEnd_309799 := by exact prefixLift 309799
  have htrace : WordTrace (prefixWord ++ tailWord_309799) baseStart_309799 baseEnd_309799 := by
    simpa [prefixWord, tailWord_309799, baseEnd_309799] using wordTrace_append hprefix tailTrace_309799
  have hstable : (prefixWord ++ tailWord_309799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309799).length < 2 ^ (prefixWord ++ tailWord_309799).sum := by decide
  have hdescent : baseEnd_309799 < baseStart_309799 := by decide
  rcases family_descends (prefixWord ++ tailWord_309799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309818 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_309818 : Nat := 118140960795 + 309818 * 2 ^ 59
def prefixEnd_309818 : Nat := 4983230072969 + 3 ^ 40 * 309818 * 2
def baseEnd_309818 : Nat := 159085549414774069350179

theorem tailTrace_309818 : CollatzResearch.WordTrace tailWord_309818 prefixEnd_309818 159085549414774069350179 := by
  unfold tailWord_309818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824997697897443386728527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7533327194393182364609405 2824997697897443386728527)
  ·
    refine ⟨4237496546846165080092791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824997697897443386728527 4237496546846165080092791)
    ·
      refine ⟨6356244820269247620139187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4237496546846165080092791 6356244820269247620139187)
      ·
        refine ⟨9534367230403871430208781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6356244820269247620139187 9534367230403871430208781)
        ·
          refine ⟨3575387711401451786328293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9534367230403871430208781 3575387711401451786328293)
          ·
            refine ⟨670385195887772209936555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3575387711401451786328293 670385195887772209936555)
            ·
              refine ⟨1005577793831658314904833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670385195887772209936555 1005577793831658314904833)
              ·
                refine ⟨754183345373743736178625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005577793831658314904833 754183345373743736178625)
                ·
                  refine ⟨565637509030307802133969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 754183345373743736178625 565637509030307802133969)
                  ·
                    refine ⟨424228131772730851600477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 565637509030307802133969 424228131772730851600477)
                    ·
                      refine ⟨159085549414774069350179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 424228131772730851600477 159085549414774069350179)
                      ·
                        rfl

theorem cell23_309818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_309818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309818 prefixEnd_309818 := by exact prefixLift 309818
  have htrace : WordTrace (prefixWord ++ tailWord_309818) baseStart_309818 baseEnd_309818 := by
    simpa [prefixWord, tailWord_309818, baseEnd_309818] using wordTrace_append hprefix tailTrace_309818
  have hstable : (prefixWord ++ tailWord_309818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309818).length < 2 ^ (prefixWord ++ tailWord_309818).sum := by decide
  have hdescent : baseEnd_309818 < baseStart_309818 := by decide
  rcases family_descends (prefixWord ++ tailWord_309818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309821 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 8]
def baseStart_309821 : Nat := 118140960795 + 309821 * 2 ^ 59
def prefixEnd_309821 : Nat := 4983230072969 + 3 ^ 40 * 309821 * 2
def baseEnd_309821 : Nat := 17676343317415284179185

theorem tailTrace_309821 : CollatzResearch.WordTrace tailWord_309821 prefixEnd_309821 17676343317415284179185 := by
  unfold tailWord_309821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11300100210578905059273317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7533400140385936706182211 11300100210578905059273317)
  ·
    refine ⟨2118768789483544698613747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11300100210578905059273317 2118768789483544698613747)
    ·
      refine ⟨3178153184225317047920621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118768789483544698613747 3178153184225317047920621)
      ·
        refine ⟨1191807444084493892970233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3178153184225317047920621 1191807444084493892970233)
        ·
          refine ⟨893855583063370419727675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191807444084493892970233 893855583063370419727675)
          ·
            refine ⟨1340783374595055629591513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893855583063370419727675 1340783374595055629591513)
            ·
              refine ⟨1005587530946291722193635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340783374595055629591513 1005587530946291722193635)
              ·
                refine ⟨1508381296419437583290453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005587530946291722193635 1508381296419437583290453)
                ·
                  refine ⟨17676343317415284179185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1508381296419437583290453 17676343317415284179185)
                  ·
                    rfl

theorem cell23_309821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_309821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309821 prefixEnd_309821 := by exact prefixLift 309821
  have htrace : WordTrace (prefixWord ++ tailWord_309821) baseStart_309821 baseEnd_309821 := by
    simpa [prefixWord, tailWord_309821, baseEnd_309821] using wordTrace_append hprefix tailTrace_309821
  have hstable : (prefixWord ++ tailWord_309821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309821).length < 2 ^ (prefixWord ++ tailWord_309821).sum := by decide
  have hdescent : baseEnd_309821 < baseStart_309821 := by decide
  rcases family_descends (prefixWord ++ tailWord_309821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309824 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_309824 : Nat := 118140960795 + 309824 * 2 ^ 59
def prefixEnd_309824 : Nat := 4983230072969 + 3 ^ 40 * 309824 * 2
def baseEnd_309824 : Nat := 159088630298701045875151

theorem tailTrace_309824 : CollatzResearch.WordTrace tailWord_309824 prefixEnd_309824 159088630298701045875151 := by
  unfold tailWord_309824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650104814784018285816263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7533473086378691047755017 5650104814784018285816263)
  ·
    refine ⟨8475157222176027428724395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650104814784018285816263 8475157222176027428724395)
    ·
      refine ⟨12712735833264041143086593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8475157222176027428724395 12712735833264041143086593)
      ·
        refine ⟨9534551874948030857314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12712735833264041143086593 9534551874948030857314945)
        ·
          refine ⟨7150913906211023142986209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9534551874948030857314945 7150913906211023142986209)
          ·
            refine ⟨5363185429658267357239657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7150913906211023142986209 5363185429658267357239657)
            ·
              refine ⟨4022389072243700517929743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363185429658267357239657 4022389072243700517929743)
              ·
                refine ⟨6033583608365550776894615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022389072243700517929743 6033583608365550776894615)
                ·
                  refine ⟨9050375412548326165341923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6033583608365550776894615 9050375412548326165341923)
                  ·
                    refine ⟨13575563118822489248012885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9050375412548326165341923 13575563118822489248012885)
                    ·
                      refine ⟨159088630298701045875151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 13575563118822489248012885 159088630298701045875151)
                      ·
                        rfl

theorem cell23_309824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_309824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309824 prefixEnd_309824 := by exact prefixLift 309824
  have htrace : WordTrace (prefixWord ++ tailWord_309824) baseStart_309824 baseEnd_309824 := by
    simpa [prefixWord, tailWord_309824, baseEnd_309824] using wordTrace_append hprefix tailTrace_309824
  have hstable : (prefixWord ++ tailWord_309824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309824).length < 2 ^ (prefixWord ++ tailWord_309824).sum := by decide
  have hdescent : baseEnd_309824 < baseStart_309824 := by decide
  rcases family_descends (prefixWord ++ tailWord_309824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309825 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_309825 : Nat := 118140960795 + 309825 * 2 ^ 59
def prefixEnd_309825 : Nat := 4983230072969 + 3 ^ 40 * 309825 * 2
def baseEnd_309825 : Nat := 53029714593118513987549

theorem tailTrace_309825 : CollatzResearch.WordTrace tailWord_309825 prefixEnd_309825 53029714593118513987549 := by
  unfold tailWord_309825
  simp only [CollatzResearch.WordTrace]
  refine ⟨11300246102564413742418929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7533497401709609161612619 11300246102564413742418929)
  ·
    refine ⟨8475184576923310306814197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11300246102564413742418929 8475184576923310306814197)
    ·
      refine ⟨794548554086560341263831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8475184576923310306814197 794548554086560341263831)
      ·
        refine ⟨1191822831129840511895747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794548554086560341263831 1191822831129840511895747)
        ·
          refine ⟨1787734246694760767843621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191822831129840511895747 1787734246694760767843621)
          ·
            refine ⟨335200171255267643970679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1787734246694760767843621 335200171255267643970679)
            ·
              refine ⟨502800256882901465956019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335200171255267643970679 502800256882901465956019)
              ·
                refine ⟨754200385324352198934029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502800256882901465956019 754200385324352198934029)
                ·
                  refine ⟨282825144496632074600261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754200385324352198934029 282825144496632074600261)
                  ·
                    refine ⟨53029714593118513987549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282825144496632074600261 53029714593118513987549)
                    ·
                      rfl

theorem cell23_309825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_309825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309825 prefixEnd_309825 := by exact prefixLift 309825
  have htrace : WordTrace (prefixWord ++ tailWord_309825) baseStart_309825 baseEnd_309825 := by
    simpa [prefixWord, tailWord_309825, baseEnd_309825] using wordTrace_append hprefix tailTrace_309825
  have hstable : (prefixWord ++ tailWord_309825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309825).length < 2 ^ (prefixWord ++ tailWord_309825).sum := by decide
  have hdescent : baseEnd_309825 < baseStart_309825 := by decide
  rcases family_descends (prefixWord ++ tailWord_309825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309838 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_309838 : Nat := 118140960795 + 309838 * 2 ^ 59
def prefixEnd_309838 : Nat := 4983230072969 + 3 ^ 40 * 309838 * 2
def baseEnd_309838 : Nat := 17677313225318221233343

theorem tailTrace_309838 : CollatzResearch.WordTrace tailWord_309838 prefixEnd_309838 17677313225318221233343 := by
  unfold tailWord_309838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412590031439664620330271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7533813501011544641761445 1412590031439664620330271)
  ·
    refine ⟨2118885047159496930495407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1412590031439664620330271 2118885047159496930495407)
    ·
      refine ⟨3178327570739245395743111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118885047159496930495407 3178327570739245395743111)
      ·
        refine ⟨4767491356108868093614667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178327570739245395743111 4767491356108868093614667)
        ·
          refine ⟨7151237034163302140422001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767491356108868093614667 7151237034163302140422001)
          ·
            refine ⟨5363427775622476605316501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7151237034163302140422001 5363427775622476605316501)
            ·
              refine ⟨251410676982303590874211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5363427775622476605316501 251410676982303590874211)
              ·
                refine ⟨377116015473455386311317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251410676982303590874211 377116015473455386311317)
                ·
                  refine ⟨17677313225318221233343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 377116015473455386311317 17677313225318221233343)
                  ·
                    rfl

theorem cell23_309838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_309838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309838 prefixEnd_309838 := by exact prefixLift 309838
  have htrace : WordTrace (prefixWord ++ tailWord_309838) baseStart_309838 baseEnd_309838 := by
    simpa [prefixWord, tailWord_309838, baseEnd_309838] using wordTrace_append hprefix tailTrace_309838
  have hstable : (prefixWord ++ tailWord_309838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309838).length < 2 ^ (prefixWord ++ tailWord_309838).sum := by decide
  have hdescent : baseEnd_309838 < baseStart_309838 := by decide
  rcases family_descends (prefixWord ++ tailWord_309838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309848 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_309848 : Nat := 118140960795 + 309848 * 2 ^ 59
def prefixEnd_309848 : Nat := 4983230072969 + 3 ^ 40 * 309848 * 2
def baseEnd_309848 : Nat := 159100953834408951975041

theorem tailTrace_309848 : CollatzResearch.WordTrace tailWord_309848 prefixEnd_309848 159100953834408951975041 := by
  unfold tailWord_309848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650542490740544335253099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7534056654320725780337465 5650542490740544335253099)
  ·
    refine ⟨8475813736110816502879649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5650542490740544335253099 8475813736110816502879649)
    ·
      refine ⟨6356860302083112377159737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8475813736110816502879649 6356860302083112377159737)
      ·
        refine ⟨4767645226562334282869803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6356860302083112377159737 4767645226562334282869803)
        ·
          refine ⟨7151467839843501424304705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767645226562334282869803 7151467839843501424304705)
          ·
            refine ⟨5363600879882626068228529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7151467839843501424304705 5363600879882626068228529)
            ·
              refine ⟨4022700659911969551171397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363600879882626068228529 4022700659911969551171397)
              ·
                refine ⟨754256373733494290844637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4022700659911969551171397 754256373733494290844637)
                ·
                  refine ⟨282846140150060359066739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754256373733494290844637 282846140150060359066739)
                  ·
                    refine ⟨424269210225090538600109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282846140150060359066739 424269210225090538600109)
                    ·
                      refine ⟨159100953834408951975041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 424269210225090538600109 159100953834408951975041)
                      ·
                        rfl

theorem cell23_309848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_309848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309848 prefixEnd_309848 := by exact prefixLift 309848
  have htrace : WordTrace (prefixWord ++ tailWord_309848) baseStart_309848 baseEnd_309848 := by
    simpa [prefixWord, tailWord_309848, baseEnd_309848] using wordTrace_append hprefix tailTrace_309848
  have hstable : (prefixWord ++ tailWord_309848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309848).length < 2 ^ (prefixWord ++ tailWord_309848).sum := by decide
  have hdescent : baseEnd_309848 < baseStart_309848 := by decide
  rcases family_descends (prefixWord ++ tailWord_309848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309865 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 1, 1, 3]
def baseStart_309865 : Nat := 118140960795 + 309865 * 2 ^ 59
def prefixEnd_309865 : Nat := 4983230072969 + 3 ^ 40 * 309865 * 2
def baseEnd_309865 : Nat := 159109683005535385462463

theorem tailTrace_309865 : CollatzResearch.WordTrace tailWord_309865 prefixEnd_309865 159109683005535385462463 := by
  unfold tailWord_309865
  simp only [CollatzResearch.WordTrace]
  refine ⟨11301705022419500573875049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7534470014946333715916699 11301705022419500573875049)
  ·
    refine ⟨8476278766814625430406287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11301705022419500573875049 8476278766814625430406287)
    ·
      refine ⟨12714418150221938145609431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8476278766814625430406287 12714418150221938145609431)
      ·
        refine ⟨19071627225332907218414147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12714418150221938145609431 19071627225332907218414147)
        ·
          refine ⟨28607440837999360827621221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19071627225332907218414147 28607440837999360827621221)
          ·
            refine ⟨5363895157124880155178979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28607440837999360827621221 5363895157124880155178979)
            ·
              refine ⟨8045842735687320232768469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363895157124880155178979 8045842735687320232768469)
              ·
                refine ⟨188574439117671567955511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8045842735687320232768469 188574439117671567955511)
                ·
                  refine ⟨282861658676507351933267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188574439117671567955511 282861658676507351933267)
                  ·
                    refine ⟨424292488014761027899901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282861658676507351933267 424292488014761027899901)
                    ·
                      refine ⟨159109683005535385462463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 424292488014761027899901 159109683005535385462463)
                      ·
                        rfl

theorem cell23_309865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 1, 3].length) (baseStart_309865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309865 prefixEnd_309865 := by exact prefixLift 309865
  have htrace : WordTrace (prefixWord ++ tailWord_309865) baseStart_309865 baseEnd_309865 := by
    simpa [prefixWord, tailWord_309865, baseEnd_309865] using wordTrace_append hprefix tailTrace_309865
  have hstable : (prefixWord ++ tailWord_309865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309865).length < 2 ^ (prefixWord ++ tailWord_309865).sum := by decide
  have hdescent : baseEnd_309865 < baseStart_309865 := by decide
  rcases family_descends (prefixWord ++ tailWord_309865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309891 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5]
def baseStart_309891 : Nat := 118140960795 + 309891 * 2 ^ 59
def prefixEnd_309891 : Nat := 4983230072969 + 3 ^ 40 * 309891 * 2
def baseEnd_309891 : Nat := 159123033502552283737343

theorem tailTrace_309891 : CollatzResearch.WordTrace tailWord_309891 prefixEnd_309891 159123033502552283737343 := by
  unfold tailWord_309891
  simp only [CollatzResearch.WordTrace]
  refine ⟨11302653320325307014321527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7535102213550204676214351 11302653320325307014321527)
  ·
    refine ⟨16953979980487960521482291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11302653320325307014321527 16953979980487960521482291)
    ·
      refine ⟨25430969970731940782223437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16953979980487960521482291 25430969970731940782223437)
      ·
        refine ⟨9536613739024477793333789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25430969970731940782223437 9536613739024477793333789)
        ·
          refine ⟨3576230152134179172500171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9536613739024477793333789 3576230152134179172500171)
          ·
            refine ⟨5364345228201268758750257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576230152134179172500171 5364345228201268758750257)
            ·
              refine ⟨4023258921150951569062693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5364345228201268758750257 4023258921150951569062693)
              ·
                refine ⟨754361047715803419199255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4023258921150951569062693 754361047715803419199255)
                ·
                  refine ⟨1131541571573705128798883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754361047715803419199255 1131541571573705128798883)
                  ·
                    refine ⟨1697312357360557693198325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1131541571573705128798883 1697312357360557693198325)
                    ·
                      refine ⟨159123033502552283737343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1697312357360557693198325 159123033502552283737343)
                      ·
                        rfl

theorem cell23_309891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_309891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309891 prefixEnd_309891 := by exact prefixLift 309891
  have htrace : WordTrace (prefixWord ++ tailWord_309891) baseStart_309891 baseEnd_309891 := by
    simpa [prefixWord, tailWord_309891, baseEnd_309891] using wordTrace_append hprefix tailTrace_309891
  have hstable : (prefixWord ++ tailWord_309891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309891).length < 2 ^ (prefixWord ++ tailWord_309891).sum := by decide
  have hdescent : baseEnd_309891 < baseStart_309891 := by decide
  rcases family_descends (prefixWord ++ tailWord_309891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309942 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_309942 : Nat := 118140960795 + 309942 * 2 ^ 59
def prefixEnd_309942 : Nat := 4983230072969 + 3 ^ 40 * 309942 * 2
def baseEnd_309942 : Nat := 159149221015931584199609

theorem tailTrace_309942 : CollatzResearch.WordTrace tailWord_309942 prefixEnd_309942 159149221015931584199609 := by
  unfold tailWord_309942
  simp only [CollatzResearch.WordTrace]
  refine ⟨706532090196283920276755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7536342295427028482952053 706532090196283920276755)
  ·
    refine ⟨1059798135294425880415133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706532090196283920276755 1059798135294425880415133)
    ·
      refine ⟨397424300735409705155675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1059798135294425880415133 397424300735409705155675)
      ·
        refine ⟨596136451103114557733513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397424300735409705155675 596136451103114557733513)
        ·
          refine ⟨447102338327335918300135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596136451103114557733513 447102338327335918300135)
          ·
            refine ⟨670653507491003877450203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447102338327335918300135 670653507491003877450203)
            ·
              refine ⟨1005980261236505816175305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670653507491003877450203 1005980261236505816175305)
              ·
                refine ⟨754485195927379362131479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005980261236505816175305 754485195927379362131479)
                ·
                  refine ⟨1131727793891069043197219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754485195927379362131479 1131727793891069043197219)
                  ·
                    refine ⟨1697591690836603564795829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1131727793891069043197219 1697591690836603564795829)
                    ·
                      refine ⟨159149221015931584199609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1697591690836603564795829 159149221015931584199609)
                      ·
                        rfl

theorem cell23_309942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_309942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309942 prefixEnd_309942 := by exact prefixLift 309942
  have htrace : WordTrace (prefixWord ++ tailWord_309942) baseStart_309942 baseEnd_309942 := by
    simpa [prefixWord, tailWord_309942, baseEnd_309942] using wordTrace_append hprefix tailTrace_309942
  have hstable : (prefixWord ++ tailWord_309942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309942).length < 2 ^ (prefixWord ++ tailWord_309942).sum := by decide
  have hdescent : baseEnd_309942 < baseStart_309942 := by decide
  rcases family_descends (prefixWord ++ tailWord_309942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309973 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_309973 : Nat := 118140960795 + 309973 * 2 ^ 59
def prefixEnd_309973 : Nat := 4983230072969 + 3 ^ 40 * 309973 * 2
def baseEnd_309973 : Nat := 159165138916220962911967

theorem tailTrace_309973 : CollatzResearch.WordTrace tailWord_309973 prefixEnd_309973 159165138916220962911967 := by
  unfold tailWord_309973
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305644106028235018806573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7537096070685490012537715 11305644106028235018806573)
  ·
    refine ⟨4239616539760588132052465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11305644106028235018806573 4239616539760588132052465)
    ·
      refine ⟨3179712404820441099039349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4239616539760588132052465 3179712404820441099039349)
      ·
        refine ⟨298098037951916353034939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3179712404820441099039349 298098037951916353034939)
        ·
          refine ⟨447147056927874529552409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298098037951916353034939 447147056927874529552409)
          ·
            refine ⟨335360292695905897164307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447147056927874529552409 335360292695905897164307)
            ·
              refine ⟨503040439043858845746461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335360292695905897164307 503040439043858845746461)
              ·
                refine ⟨188640164641447067154923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503040439043858845746461 188640164641447067154923)
                ·
                  refine ⟨282960246962170600732385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188640164641447067154923 282960246962170600732385)
                  ·
                    refine ⟨212220185221627950549289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 282960246962170600732385 212220185221627950549289)
                    ·
                      refine ⟨159165138916220962911967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212220185221627950549289 159165138916220962911967)
                      ·
                        rfl

theorem cell23_309973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_309973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_309973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_309973 prefixEnd_309973 := by exact prefixLift 309973
  have htrace : WordTrace (prefixWord ++ tailWord_309973) baseStart_309973 baseEnd_309973 := by
    simpa [prefixWord, tailWord_309973, baseEnd_309973] using wordTrace_append hprefix tailTrace_309973
  have hstable : (prefixWord ++ tailWord_309973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309973).length < 2 ^ (prefixWord ++ tailWord_309973).sum := by decide
  have hdescent : baseEnd_309973 < baseStart_309973 := by decide
  rcases family_descends (prefixWord ++ tailWord_309973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310021 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_310021 : Nat := 118140960795 + 310021 * 2 ^ 59
def prefixEnd_310021 : Nat := 4983230072969 + 3 ^ 40 * 310021 * 2
def baseEnd_310021 : Nat := 159189785987636775111745

theorem tailTrace_310021 : CollatzResearch.WordTrace tailWord_310021 prefixEnd_310021 159189785987636775111745 := by
  unfold tailWord_310021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11307394809854339216553917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7538263206569559477702611 11307394809854339216553917)
  ·
    refine ⟨4240273053695377206207719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11307394809854339216553917 4240273053695377206207719)
    ·
      refine ⟨6360409580543065809311579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240273053695377206207719 6360409580543065809311579)
      ·
        refine ⟨9540614370814598713967369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360409580543065809311579 9540614370814598713967369)
        ·
          refine ⟨7155460778110949035475527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9540614370814598713967369 7155460778110949035475527)
          ·
            refine ⟨10733191167166423553213291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7155460778110949035475527 10733191167166423553213291)
            ·
              refine ⟨16099786750749635329819937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10733191167166423553213291 16099786750749635329819937)
              ·
                refine ⟨12074840063062226497364953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16099786750749635329819937 12074840063062226497364953)
                ·
                  refine ⟨9056130047296669873023715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12074840063062226497364953 9056130047296669873023715)
                  ·
                    refine ⟨13584195070945004809535573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9056130047296669873023715 13584195070945004809535573)
                    ·
                      refine ⟨159189785987636775111745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 13584195070945004809535573 159189785987636775111745)
                      ·
                        rfl

theorem cell23_310021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_310021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310021 prefixEnd_310021 := by exact prefixLift 310021
  have htrace : WordTrace (prefixWord ++ tailWord_310021) baseStart_310021 baseEnd_310021 := by
    simpa [prefixWord, tailWord_310021, baseEnd_310021] using wordTrace_append hprefix tailTrace_310021
  have hstable : (prefixWord ++ tailWord_310021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310021).length < 2 ^ (prefixWord ++ tailWord_310021).sum := by decide
  have hdescent : baseEnd_310021 < baseStart_310021 := by decide
  rcases family_descends (prefixWord ++ tailWord_310021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310028 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_310028 : Nat := 118140960795 + 310028 * 2 ^ 59
def prefixEnd_310028 : Nat := 4983230072969 + 3 ^ 40 * 310028 * 2
def baseEnd_310028 : Nat := 159193380352218247724213

theorem tailTrace_310028 : CollatzResearch.WordTrace tailWord_310028 prefixEnd_310028 159193380352218247724213 := by
  unfold tailWord_310028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5653825060414489706029369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7538433413885986274705825 5653825060414489706029369)
  ·
    refine ⟨4240368795310867279522027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5653825060414489706029369 4240368795310867279522027)
    ·
      refine ⟨6360553192966300919283041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240368795310867279522027 6360553192966300919283041)
      ·
        refine ⟨4770414894724725689462281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6360553192966300919283041 4770414894724725689462281)
        ·
          refine ⟨3577811171043544267096711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770414894724725689462281 3577811171043544267096711)
          ·
            refine ⟨5366716756565316400645067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577811171043544267096711 5366716756565316400645067)
            ·
              refine ⟨8050075134847974600967601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366716756565316400645067 8050075134847974600967601)
              ·
                refine ⟨6037556351135980950725701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050075134847974600967601 6037556351135980950725701)
                ·
                  refine ⟨1132041815837996428261069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6037556351135980950725701 1132041815837996428261069)
                  ·
                    refine ⟨424515680939248660597901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1132041815837996428261069 424515680939248660597901)
                    ·
                      refine ⟨159193380352218247724213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 424515680939248660597901 159193380352218247724213)
                      ·
                        rfl

theorem cell23_310028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_310028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310028 prefixEnd_310028 := by exact prefixLift 310028
  have htrace : WordTrace (prefixWord ++ tailWord_310028) baseStart_310028 baseEnd_310028 := by
    simpa [prefixWord, tailWord_310028, baseEnd_310028] using wordTrace_append hprefix tailTrace_310028
  have hstable : (prefixWord ++ tailWord_310028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310028).length < 2 ^ (prefixWord ++ tailWord_310028).sum := by decide
  have hdescent : baseEnd_310028 < baseStart_310028 := by decide
  rcases family_descends (prefixWord ++ tailWord_310028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310052 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 5]
def baseStart_310052 : Nat := 118140960795 + 310052 * 2 ^ 59
def prefixEnd_310052 : Nat := 4983230072969 + 3 ^ 40 * 310052 * 2
def baseEnd_310052 : Nat := 17689522654214017091567

theorem tailTrace_310052 : CollatzResearch.WordTrace tailWord_310052 prefixEnd_310052 17689522654214017091567 := by
  unfold tailWord_310052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654262736371015755466205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7539016981828021007288273 5654262736371015755466205)
  ·
    refine ⟨2120348526139130908299827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5654262736371015755466205 2120348526139130908299827)
    ·
      refine ⟨3180522789208696362449741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120348526139130908299827 3180522789208696362449741)
      ·
        refine ⟨1192696045953261135918653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3180522789208696362449741 1192696045953261135918653)
        ·
          refine ⟨447261017232472925969495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1192696045953261135918653 447261017232472925969495)
          ·
            refine ⟨670891525848709388954243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447261017232472925969495 670891525848709388954243)
            ·
              refine ⟨1006337288773064083431365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670891525848709388954243 1006337288773064083431365)
              ·
                refine ⟨188688241644949515643381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1006337288773064083431365 188688241644949515643381)
                ·
                  refine ⟨17689522654214017091567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188688241644949515643381 17689522654214017091567)
                  ·
                    rfl

theorem cell23_310052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_310052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310052 prefixEnd_310052 := by exact prefixLift 310052
  have htrace : WordTrace (prefixWord ++ tailWord_310052) baseStart_310052 baseEnd_310052 := by
    simpa [prefixWord, tailWord_310052, baseEnd_310052] using wordTrace_append hprefix tailTrace_310052
  have hstable : (prefixWord ++ tailWord_310052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310052).length < 2 ^ (prefixWord ++ tailWord_310052).sum := by decide
  have hdescent : baseEnd_310052 < baseStart_310052 := by decide
  rcases family_descends (prefixWord ++ tailWord_310052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310062 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_310062 : Nat := 118140960795 + 310062 * 2 ^ 59
def prefixEnd_310062 : Nat := 4983230072969 + 3 ^ 40 * 310062 * 2
def baseEnd_310062 : Nat := 159210838694471114699057

theorem tailTrace_310062 : CollatzResearch.WordTrace tailWord_310062 prefixEnd_310062 159210838694471114699057 := by
  unfold tailWord_310062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413611275338225402349555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7539260135137202145864293 1413611275338225402349555)
  ·
    refine ⟨2120416913007338103524333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413611275338225402349555 2120416913007338103524333)
    ·
      refine ⟨795156342377751788821625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2120416913007338103524333 795156342377751788821625)
      ·
        refine ⟨596367256783313841616219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 795156342377751788821625 596367256783313841616219)
        ·
          refine ⟨894550885174970762424329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596367256783313841616219 894550885174970762424329)
          ·
            refine ⟨670913163881228071818247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 894550885174970762424329 670913163881228071818247)
            ·
              refine ⟨1006369745821842107727371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670913163881228071818247 1006369745821842107727371)
              ·
                refine ⟨1509554618732763161591057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006369745821842107727371 1509554618732763161591057)
                ·
                  refine ⟨1132165964049572371193293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1509554618732763161591057 1132165964049572371193293)
                  ·
                    refine ⟨424562236518589639197485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1132165964049572371193293 424562236518589639197485)
                    ·
                      refine ⟨159210838694471114699057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 424562236518589639197485 159210838694471114699057)
                      ·
                        rfl

theorem cell23_310062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_310062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310062 prefixEnd_310062 := by exact prefixLift 310062
  have htrace : WordTrace (prefixWord ++ tailWord_310062) baseStart_310062 baseEnd_310062 := by
    simpa [prefixWord, tailWord_310062, baseEnd_310062] using wordTrace_append hprefix tailTrace_310062
  have hstable : (prefixWord ++ tailWord_310062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310062).length < 2 ^ (prefixWord ++ tailWord_310062).sum := by decide
  have hdescent : baseEnd_310062 < baseStart_310062 := by decide
  rcases family_descends (prefixWord ++ tailWord_310062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310086 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_310086 : Nat := 118140960795 + 310086 * 2 ^ 59
def prefixEnd_310086 : Nat := 4983230072969 + 3 ^ 40 * 310086 * 2
def baseEnd_310086 : Nat := 17691462470019891199883

theorem tailTrace_310086 : CollatzResearch.WordTrace tailWord_310086 prefixEnd_310086 17691462470019891199883 := by
  unfold tailWord_310086
  simp only [CollatzResearch.WordTrace]
  refine ⟨353430173581839228677191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7539843703079236878446741 353430173581839228677191)
  ·
    refine ⟨530145260372758843015787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353430173581839228677191 530145260372758843015787)
    ·
      refine ⟨795217890559138264523681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530145260372758843015787 795217890559138264523681)
      ·
        refine ⟨596413417919353698392761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 795217890559138264523681 596413417919353698392761)
        ·
          refine ⟨447310063439515273794571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596413417919353698392761 447310063439515273794571)
          ·
            refine ⟨670965095159272910691857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447310063439515273794571 670965095159272910691857)
            ·
              refine ⟨503223821369454683018893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670965095159272910691857 503223821369454683018893)
              ·
                refine ⟨188708933013545506132085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503223821369454683018893 188708933013545506132085)
                ·
                  refine ⟨17691462470019891199883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188708933013545506132085 17691462470019891199883)
                  ·
                    rfl

theorem cell23_310086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_310086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310086 prefixEnd_310086 := by exact prefixLift 310086
  have htrace : WordTrace (prefixWord ++ tailWord_310086) baseStart_310086 baseEnd_310086 := by
    simpa [prefixWord, tailWord_310086, baseEnd_310086] using wordTrace_append hprefix tailTrace_310086
  have hstable : (prefixWord ++ tailWord_310086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310086).length < 2 ^ (prefixWord ++ tailWord_310086).sum := by decide
  have hdescent : baseEnd_310086 < baseStart_310086 := by decide
  rcases family_descends (prefixWord ++ tailWord_310086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310098 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_310098 : Nat := 118140960795 + 310098 * 2 ^ 59
def prefixEnd_310098 : Nat := 4983230072969 + 3 ^ 40 * 310098 * 2
def baseEnd_310098 : Nat := 159229323998032973848891

theorem tailTrace_310098 : CollatzResearch.WordTrace tailWord_310098 prefixEnd_310098 159229323998032973848891 := by
  unfold tailWord_310098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827550807643845341776737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7540135487050254244737965 2827550807643845341776737)
  ·
    refine ⟨2120663105732884006332553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2827550807643845341776737 2120663105732884006332553)
    ·
      refine ⟨1590497329299663004749415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2120663105732884006332553 1590497329299663004749415)
      ·
        refine ⟨2385745993949494507124123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590497329299663004749415 2385745993949494507124123)
        ·
          refine ⟨3578618990924241760686185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385745993949494507124123 3578618990924241760686185)
          ·
            refine ⟨2683964243193181320514639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578618990924241760686185 2683964243193181320514639)
            ·
              refine ⟨4025946364789771980771959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683964243193181320514639 4025946364789771980771959)
              ·
                refine ⟨6038919547184657971157939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025946364789771980771959 6038919547184657971157939)
                ·
                  refine ⟨9058379320776986956736909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038919547184657971157939 9058379320776986956736909)
                  ·
                    refine ⟨3396892245291370108776341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9058379320776986956736909 3396892245291370108776341)
                    ·
                      refine ⟨159229323998032973848891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3396892245291370108776341 159229323998032973848891)
                      ·
                        rfl

theorem cell23_310098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_310098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310098 prefixEnd_310098 := by exact prefixLift 310098
  have htrace : WordTrace (prefixWord ++ tailWord_310098) baseStart_310098 baseEnd_310098 := by
    simpa [prefixWord, tailWord_310098, baseEnd_310098] using wordTrace_append hprefix tailTrace_310098
  have hstable : (prefixWord ++ tailWord_310098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310098).length < 2 ^ (prefixWord ++ tailWord_310098).sum := by decide
  have hdescent : baseEnd_310098 < baseStart_310098 := by decide
  rcases family_descends (prefixWord ++ tailWord_310098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310112 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 1, 4]
def baseStart_310112 : Nat := 118140960795 + 310112 * 2 ^ 59
def prefixEnd_310112 : Nat := 4983230072969 + 3 ^ 40 * 310112 * 2
def baseEnd_310112 : Nat := 53078837575731973024609

theorem tailTrace_310112 : CollatzResearch.WordTrace tailWord_310112 prefixEnd_310112 53078837575731973024609 := by
  unfold tailWord_310112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5655356926262330879058295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7540475901683107838744393 5655356926262330879058295)
  ·
    refine ⟨8483035389393496318587443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5655356926262330879058295 8483035389393496318587443)
    ·
      refine ⟨12724553084090244477881165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8483035389393496318587443 12724553084090244477881165)
      ·
        refine ⟨4771707406533841679205437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12724553084090244477881165 4771707406533841679205437)
        ·
          refine ⟨1789390277450190629702039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4771707406533841679205437 1789390277450190629702039)
          ·
            refine ⟨2684085416175285944553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789390277450190629702039 2684085416175285944553059)
            ·
              refine ⟨4026128124262928916829589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684085416175285944553059 4026128124262928916829589)
              ·
                refine ⟨188724755824824792976387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4026128124262928916829589 188724755824824792976387)
                ·
                  refine ⟨283087133737237189464581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188724755824824792976387 283087133737237189464581)
                  ·
                    refine ⟨53078837575731973024609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283087133737237189464581 53078837575731973024609)
                    ·
                      rfl

theorem cell23_310112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 4].length) (baseStart_310112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310112 prefixEnd_310112 := by exact prefixLift 310112
  have htrace : WordTrace (prefixWord ++ tailWord_310112) baseStart_310112 baseEnd_310112 := by
    simpa [prefixWord, tailWord_310112, baseEnd_310112] using wordTrace_append hprefix tailTrace_310112
  have hstable : (prefixWord ++ tailWord_310112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310112).length < 2 ^ (prefixWord ++ tailWord_310112).sum := by decide
  have hdescent : baseEnd_310112 < baseStart_310112 := by decide
  rcases family_descends (prefixWord ++ tailWord_310112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310155 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 1, 5]
def baseStart_310155 : Nat := 118140960795 + 310155 * 2 ^ 59
def prefixEnd_310155 : Nat := 4983230072969 + 3 ^ 40 * 310155 * 2
def baseEnd_310155 : Nat := 53086197465113083612043

theorem tailTrace_310155 : CollatzResearch.WordTrace tailWord_310155 prefixEnd_310155 53086197465113083612043 := by
  unfold tailWord_310155
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312282191368880101931919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7541521460912586734621279 11312282191368880101931919)
  ·
    refine ⟨16968423287053320152897879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11312282191368880101931919 16968423287053320152897879)
    ·
      refine ⟨25452634930579980229346819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16968423287053320152897879 25452634930579980229346819)
      ·
        refine ⟨38178952395869970344020229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25452634930579980229346819 38178952395869970344020229)
        ·
          refine ⟨7158553574225619439503793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38178952395869970344020229 7158553574225619439503793)
          ·
            refine ⟨5368915180669214579627845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7158553574225619439503793 5368915180669214579627845)
            ·
              refine ⟨1006671596375477733680221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5368915180669214579627845 1006671596375477733680221)
              ·
                refine ⟨377501848640804150130083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006671596375477733680221 377501848640804150130083)
                ·
                  refine ⟨566252772961206225195125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377501848640804150130083 566252772961206225195125)
                  ·
                    refine ⟨53086197465113083612043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 566252772961206225195125 53086197465113083612043)
                    ·
                      rfl

theorem cell23_310155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 5].length) (baseStart_310155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310155 prefixEnd_310155 := by exact prefixLift 310155
  have htrace : WordTrace (prefixWord ++ tailWord_310155) baseStart_310155 baseEnd_310155 := by
    simpa [prefixWord, tailWord_310155, baseEnd_310155] using wordTrace_append hprefix tailTrace_310155
  have hstable : (prefixWord ++ tailWord_310155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310155).length < 2 ^ (prefixWord ++ tailWord_310155).sum := by decide
  have hdescent : baseEnd_310155 < baseStart_310155 := by decide
  rcases family_descends (prefixWord ++ tailWord_310155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310189 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_310189 : Nat := 118140960795 + 310189 * 2 ^ 59
def prefixEnd_310189 : Nat := 4983230072969 + 3 ^ 40 * 310189 * 2
def baseEnd_310189 : Nat := 53092016912530705936991

theorem tailTrace_310189 : CollatzResearch.WordTrace tailWord_310189 prefixEnd_310189 53092016912530705936991 := by
  unfold tailWord_310189
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313522273245703908669621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7542348182163802605779747 11313522273245703908669621)
  ·
    refine ⟨1060642713116784741437777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11313522273245703908669621 1060642713116784741437777)
    ·
      refine ⟨795482034837588556078333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1060642713116784741437777 795482034837588556078333)
      ·
        refine ⟨298305763064095708529375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 795482034837588556078333 298305763064095708529375)
        ·
          refine ⟨447458644596143562794063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298305763064095708529375 447458644596143562794063)
          ·
            refine ⟨671187966894215344191095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447458644596143562794063 671187966894215344191095)
            ·
              refine ⟨1006781950341323016286643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671187966894215344191095 1006781950341323016286643)
              ·
                refine ⟨1510172925511984524429965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006781950341323016286643 1510172925511984524429965)
                ·
                  refine ⟨566314847066994196661237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1510172925511984524429965 566314847066994196661237)
                  ·
                    refine ⟨53092016912530705936991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 566314847066994196661237 53092016912530705936991)
                    ·
                      rfl

theorem cell23_310189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_310189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310189 prefixEnd_310189 := by exact prefixLift 310189
  have htrace : WordTrace (prefixWord ++ tailWord_310189) baseStart_310189 baseEnd_310189 := by
    simpa [prefixWord, tailWord_310189, baseEnd_310189] using wordTrace_append hprefix tailTrace_310189
  have hstable : (prefixWord ++ tailWord_310189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310189).length < 2 ^ (prefixWord ++ tailWord_310189).sum := by decide
  have hdescent : baseEnd_310189 < baseStart_310189 := by decide
  rcases family_descends (prefixWord ++ tailWord_310189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310196 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_310196 : Nat := 118140960795 + 310196 * 2 ^ 59
def prefixEnd_310196 : Nat := 4983230072969 + 3 ^ 40 * 310196 * 2
def baseEnd_310196 : Nat := 159279645102173590423441

theorem tailTrace_310196 : CollatzResearch.WordTrace tailWord_310196 prefixEnd_310196 159279645102173590423441 := by
  unfold tailWord_310196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656888792110172052087221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7542518389480229402782961 5656888792110172052087221)
  ·
    refine ⟨530333324260328629883177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5656888792110172052087221 530333324260328629883177)
    ·
      refine ⟨397749993195246472412383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530333324260328629883177 397749993195246472412383)
      ·
        refine ⟨596624989792869708618575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397749993195246472412383 596624989792869708618575)
        ·
          refine ⟨894937484689304562927863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596624989792869708618575 894937484689304562927863)
          ·
            refine ⟨1342406227033956844391795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894937484689304562927863 1342406227033956844391795)
            ·
              refine ⟨2013609340550935266587693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342406227033956844391795 2013609340550935266587693)
              ·
                refine ⟨755103502706600724970385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2013609340550935266587693 755103502706600724970385)
                ·
                  refine ⟨566327627029950543727789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755103502706600724970385 566327627029950543727789)
                  ·
                    refine ⟨212372860136231453897921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566327627029950543727789 212372860136231453897921)
                    ·
                      refine ⟨159279645102173590423441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212372860136231453897921 159279645102173590423441)
                      ·
                        rfl

theorem cell23_310196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_310196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310196 prefixEnd_310196 := by exact prefixLift 310196
  have htrace : WordTrace (prefixWord ++ tailWord_310196) baseStart_310196 baseEnd_310196 := by
    simpa [prefixWord, tailWord_310196, baseEnd_310196] using wordTrace_append hprefix tailTrace_310196
  have hstable : (prefixWord ++ tailWord_310196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310196).length < 2 ^ (prefixWord ++ tailWord_310196).sum := by decide
  have hdescent : baseEnd_310196 < baseStart_310196 := by decide
  rcases family_descends (prefixWord ++ tailWord_310196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310214 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_310214 : Nat := 118140960795 + 310214 * 2 ^ 59
def prefixEnd_310214 : Nat := 4983230072969 + 3 ^ 40 * 310214 * 2
def baseEnd_310214 : Nat := 53096295917984839999453

theorem tailTrace_310214 : CollatzResearch.WordTrace tailWord_310214 prefixEnd_310214 53096295917984839999453 := by
  unfold tailWord_310214
  simp only [CollatzResearch.WordTrace]
  refine ⟨353576065567347911822803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7542956065436755452219797 353576065567347911822803)
  ·
    refine ⟨530364098351021867734205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353576065567347911822803 530364098351021867734205)
    ·
      refine ⟨198886536881633200400327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 530364098351021867734205 198886536881633200400327)
      ·
        refine ⟨298329805322449800600491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198886536881633200400327 298329805322449800600491)
        ·
          refine ⟨447494707983674700900737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298329805322449800600491 447494707983674700900737)
          ·
            refine ⟨335621030987756025675553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447494707983674700900737 335621030987756025675553)
            ·
              refine ⟨251715773240817019256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335621030987756025675553 251715773240817019256665)
              ·
                refine ⟨188786829930612764442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251715773240817019256665 188786829930612764442499)
                ·
                  refine ⟨283180244895919146663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188786829930612764442499 283180244895919146663749)
                  ·
                    refine ⟨53096295917984839999453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283180244895919146663749 53096295917984839999453)
                    ·
                      rfl

theorem cell23_310214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_310214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310214 prefixEnd_310214 := by exact prefixLift 310214
  have htrace : WordTrace (prefixWord ++ tailWord_310214) baseStart_310214 baseEnd_310214 := by
    simpa [prefixWord, tailWord_310214, baseEnd_310214] using wordTrace_append hprefix tailTrace_310214
  have hstable : (prefixWord ++ tailWord_310214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310214).length < 2 ^ (prefixWord ++ tailWord_310214).sum := by decide
  have hdescent : baseEnd_310214 < baseStart_310214 := by decide
  rcases family_descends (prefixWord ++ tailWord_310214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310225 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_310225 : Nat := 118140960795 + 310225 * 2 ^ 59
def prefixEnd_310225 : Nat := 4983230072969 + 3 ^ 40 * 310225 * 2
def baseEnd_310225 : Nat := 159294536041153976960807

theorem tailTrace_310225 : CollatzResearch.WordTrace tailWord_310225 prefixEnd_310225 159294536041153976960807 := by
  unfold tailWord_310225
  simp only [CollatzResearch.WordTrace]
  refine ⟨11314835301115282056980129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7543223534076854704653419 11314835301115282056980129)
  ·
    refine ⟨8486126475836461542735097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11314835301115282056980129 8486126475836461542735097)
    ·
      refine ⟨6364594856877346157051323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8486126475836461542735097 6364594856877346157051323)
      ·
        refine ⟨9546892285316019235576985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364594856877346157051323 9546892285316019235576985)
        ·
          refine ⟨7160169213987014426682739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9546892285316019235576985 7160169213987014426682739)
          ·
            refine ⟨10740253820980521640024109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160169213987014426682739 10740253820980521640024109)
            ·
              refine ⟨4027595182867695615009041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10740253820980521640024109 4027595182867695615009041)
              ·
                refine ⟨3020696387150771711256781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027595182867695615009041 3020696387150771711256781)
                ·
                  refine ⟨1132761145181539391721293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3020696387150771711256781 1132761145181539391721293)
                  ·
                    refine ⟨424785429443077271895485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1132761145181539391721293 424785429443077271895485)
                    ·
                      refine ⟨159294536041153976960807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 424785429443077271895485 159294536041153976960807)
                      ·
                        rfl

theorem cell23_310225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_310225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310225 prefixEnd_310225 := by exact prefixLift 310225
  have htrace : WordTrace (prefixWord ++ tailWord_310225) baseStart_310225 baseEnd_310225 := by
    simpa [prefixWord, tailWord_310225, baseEnd_310225] using wordTrace_append hprefix tailTrace_310225
  have hstable : (prefixWord ++ tailWord_310225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310225).length < 2 ^ (prefixWord ++ tailWord_310225).sum := by decide
  have hdescent : baseEnd_310225 < baseStart_310225 := by decide
  rcases family_descends (prefixWord ++ tailWord_310225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310260 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_310260 : Nat := 118140960795 + 310260 * 2 ^ 59
def prefixEnd_310260 : Nat := 4983230072969 + 3 ^ 40 * 310260 * 2
def baseEnd_310260 : Nat := 159312507864061340023147

theorem tailTrace_310260 : CollatzResearch.WordTrace tailWord_310260 prefixEnd_310260 159312507864061340023147 := by
  unfold tailWord_310260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658055927994241517252117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7544074570658988689669489 5658055927994241517252117)
  ·
    refine ⟨265221371624730071121193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5658055927994241517252117 265221371624730071121193)
    ·
      refine ⟨198916028718547553340895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265221371624730071121193 198916028718547553340895)
      ·
        refine ⟨298374043077821330011343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198916028718547553340895 298374043077821330011343)
        ·
          refine ⟨447561064616731995017015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298374043077821330011343 447561064616731995017015)
          ·
            refine ⟨671341596925097992525523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447561064616731995017015 671341596925097992525523)
            ·
              refine ⟨1007012395387646988788285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671341596925097992525523 1007012395387646988788285)
              ·
                refine ⟨377629648270367620795607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007012395387646988788285 377629648270367620795607)
                ·
                  refine ⟨566444472405551431193411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377629648270367620795607 566444472405551431193411)
                  ·
                    refine ⟨849666708608327146790117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 566444472405551431193411 849666708608327146790117)
                    ·
                      refine ⟨159312507864061340023147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 849666708608327146790117 159312507864061340023147)
                      ·
                        rfl

theorem cell23_310260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_310260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310260 prefixEnd_310260 := by exact prefixLift 310260
  have htrace : WordTrace (prefixWord ++ tailWord_310260) baseStart_310260 baseEnd_310260 := by
    simpa [prefixWord, tailWord_310260, baseEnd_310260] using wordTrace_append hprefix tailTrace_310260
  have hstable : (prefixWord ++ tailWord_310260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310260).length < 2 ^ (prefixWord ++ tailWord_310260).sum := by decide
  have hdescent : baseEnd_310260 < baseStart_310260 := by decide
  rcases family_descends (prefixWord ++ tailWord_310260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310290 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_310290 : Nat := 118140960795 + 310290 * 2 ^ 59
def prefixEnd_310290 : Nat := 4983230072969 + 3 ^ 40 * 310290 * 2
def baseEnd_310290 : Nat := 159327912283696222648009

theorem tailTrace_310290 : CollatzResearch.WordTrace tailWord_310290 prefixEnd_310290 159327912283696222648009 := by
  unfold tailWord_310290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829301511469949539524081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7544804030586532105397549 2829301511469949539524081)
  ·
    refine ⟨2121976133602462154643061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2829301511469949539524081 2121976133602462154643061)
    ·
      refine ⟨198935262525230826997787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2121976133602462154643061 198935262525230826997787)
      ·
        refine ⟨298402893787846240496681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198935262525230826997787 298402893787846240496681)
        ·
          refine ⟨223802170340884680372511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298402893787846240496681 223802170340884680372511)
          ·
            refine ⟨335703255511327020558767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223802170340884680372511 335703255511327020558767)
            ·
              refine ⟨503554883266990530838151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335703255511327020558767 503554883266990530838151)
              ·
                refine ⟨755332324900485796257227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503554883266990530838151 755332324900485796257227)
                ·
                  refine ⟨1132998487350728694385841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755332324900485796257227 1132998487350728694385841)
                  ·
                    refine ⟨849748865513046520789381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132998487350728694385841 849748865513046520789381)
                    ·
                      refine ⟨159327912283696222648009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 849748865513046520789381 159327912283696222648009)
                      ·
                        rfl

theorem cell23_310290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_310290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310290 prefixEnd_310290 := by exact prefixLift 310290
  have htrace : WordTrace (prefixWord ++ tailWord_310290) baseStart_310290 baseEnd_310290 := by
    simpa [prefixWord, tailWord_310290, baseEnd_310290] using wordTrace_append hprefix tailTrace_310290
  have hstable : (prefixWord ++ tailWord_310290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310290).length < 2 ^ (prefixWord ++ tailWord_310290).sum := by decide
  have hdescent : baseEnd_310290 < baseStart_310290 := by decide
  rcases family_descends (prefixWord ++ tailWord_310290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310339 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 5]
def baseStart_310339 : Nat := 118140960795 + 310339 * 2 ^ 59
def prefixEnd_310339 : Nat := 4983230072969 + 3 ^ 40 * 310339 * 2
def baseEnd_310339 : Nat := 17705896981751836770587

theorem tailTrace_310339 : CollatzResearch.WordTrace tailWord_310339 prefixEnd_310339 17705896981751836770587 := by
  unfold tailWord_310339
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318993222702279526630071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7545995481801519684420047 11318993222702279526630071)
  ·
    refine ⟨16978489834053419289945107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11318993222702279526630071 16978489834053419289945107)
    ·
      refine ⟨25467734751080128934917661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16978489834053419289945107 25467734751080128934917661)
      ·
        refine ⟨9550400531655048350594123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25467734751080128934917661 9550400531655048350594123)
        ·
          refine ⟨14325600797482572525891185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9550400531655048350594123 14325600797482572525891185)
          ·
            refine ⟨10744200598111929394418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14325600797482572525891185 10744200598111929394418389)
            ·
              refine ⟨251817201518248345181681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10744200598111929394418389 251817201518248345181681)
              ·
                refine ⟨188862901138686258886261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251817201518248345181681 188862901138686258886261)
                ·
                  refine ⟨17705896981751836770587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188862901138686258886261 17705896981751836770587)
                  ·
                    rfl

theorem cell23_310339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 5].length) (baseStart_310339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310339 prefixEnd_310339 := by exact prefixLift 310339
  have htrace : WordTrace (prefixWord ++ tailWord_310339) baseStart_310339 baseEnd_310339 := by
    simpa [prefixWord, tailWord_310339, baseEnd_310339] using wordTrace_append hprefix tailTrace_310339
  have hstable : (prefixWord ++ tailWord_310339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310339).length < 2 ^ (prefixWord ++ tailWord_310339).sum := by decide
  have hdescent : baseEnd_310339 < baseStart_310339 := by decide
  rcases family_descends (prefixWord ++ tailWord_310339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310395 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 8]
def baseStart_310395 : Nat := 118140960795 + 310395 * 2 ^ 59
def prefixEnd_310395 : Nat := 4983230072969 + 3 ^ 40 * 310395 * 2
def baseEnd_310395 : Nat := 17709091972490923537225

theorem tailTrace_310395 : CollatzResearch.WordTrace tailWord_310395 prefixEnd_310395 17709091972490923537225 := by
  unfold tailWord_310395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321035710499401090668639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7547357140332934060445759 11321035710499401090668639)
  ·
    refine ⟨16981553565749101636002959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321035710499401090668639 16981553565749101636002959)
    ·
      refine ⟨25472330348623652454004439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16981553565749101636002959 25472330348623652454004439)
      ·
        refine ⟨38208495522935478681006659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25472330348623652454004439 38208495522935478681006659)
        ·
          refine ⟨57312743284403218021509989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38208495522935478681006659 57312743284403218021509989)
          ·
            refine ⟨10746139365825603379033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57312743284403218021509989 10746139365825603379033123)
            ·
              refine ⟨16119209048738405068549685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746139365825603379033123 16119209048738405068549685)
              ·
                refine ⟨1511175848319225475176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16119209048738405068549685 1511175848319225475176533)
                ·
                  refine ⟨17709091972490923537225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1511175848319225475176533 17709091972490923537225)
                  ·
                    rfl

theorem cell23_310395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 8].length) (baseStart_310395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310395 prefixEnd_310395 := by exact prefixLift 310395
  have htrace : WordTrace (prefixWord ++ tailWord_310395) baseStart_310395 baseEnd_310395 := by
    simpa [prefixWord, tailWord_310395, baseEnd_310395] using wordTrace_append hprefix tailTrace_310395
  have hstable : (prefixWord ++ tailWord_310395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310395).length < 2 ^ (prefixWord ++ tailWord_310395).sum := by decide
  have hdescent : baseEnd_310395 < baseStart_310395 := by decide
  rcases family_descends (prefixWord ++ tailWord_310395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310426 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_310426 : Nat := 118140960795 + 310426 * 2 ^ 59
def prefixEnd_310426 : Nat := 4983230072969 + 3 ^ 40 * 310426 * 2
def baseEnd_310426 : Nat := 159397745652707690547383

theorem tailTrace_310426 : CollatzResearch.WordTrace tailWord_310426 prefixEnd_310426 159397745652707690547383 := by
  unfold tailWord_310426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830541593346773346261783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7548110915591395590031421 2830541593346773346261783)
  ·
    refine ⟨4245812390020160019392675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2830541593346773346261783 4245812390020160019392675)
    ·
      refine ⟨6368718585030240029089013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245812390020160019392675 6368718585030240029089013)
      ·
        refine ⟨597067367346585002727095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6368718585030240029089013 597067367346585002727095)
        ·
          refine ⟨895601051019877504090643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597067367346585002727095 895601051019877504090643)
          ·
            refine ⟨1343401576529816256135965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895601051019877504090643 1343401576529816256135965)
            ·
              refine ⟨503775591198681096050987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1343401576529816256135965 503775591198681096050987)
              ·
                refine ⟨755663386798021644076481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503775591198681096050987 755663386798021644076481)
                ·
                  refine ⟨566747540098516233057361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755663386798021644076481 566747540098516233057361)
                  ·
                    refine ⟨425060655073887174793021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 566747540098516233057361 425060655073887174793021)
                    ·
                      refine ⟨159397745652707690547383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425060655073887174793021 159397745652707690547383)
                      ·
                        rfl

theorem cell23_310426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_310426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310426 prefixEnd_310426 := by exact prefixLift 310426
  have htrace : WordTrace (prefixWord ++ tailWord_310426) baseStart_310426 baseEnd_310426 := by
    simpa [prefixWord, tailWord_310426, baseEnd_310426] using wordTrace_append hprefix tailTrace_310426
  have hstable : (prefixWord ++ tailWord_310426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310426).length < 2 ^ (prefixWord ++ tailWord_310426).sum := by decide
  have hdescent : baseEnd_310426 < baseStart_310426 := by decide
  rcases family_descends (prefixWord ++ tailWord_310426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310509 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_310509 : Nat := 118140960795 + 310509 * 2 ^ 59
def prefixEnd_310509 : Nat := 4983230072969 + 3 ^ 40 * 310509 * 2
def baseEnd_310509 : Nat := 159440364547030865809501

theorem tailTrace_310509 : CollatzResearch.WordTrace tailWord_310509 prefixEnd_310509 159440364547030865809501 := by
  unfold tailWord_310509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11325193632086398560318581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7550129088057599040212387 11325193632086398560318581)
  ·
    refine ⟨1061736903008099865029867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11325193632086398560318581 1061736903008099865029867)
    ·
      refine ⟨1592605354512149797544801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061736903008099865029867 1592605354512149797544801)
      ·
        refine ⟨1194454015884112348158601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1592605354512149797544801 1194454015884112348158601)
        ·
          refine ⟨895840511913084261118951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194454015884112348158601 895840511913084261118951)
          ·
            refine ⟨1343760767869626391678427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895840511913084261118951 1343760767869626391678427)
            ·
              refine ⟨2015641151804439587517641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343760767869626391678427 2015641151804439587517641)
              ·
                refine ⟨1511730863853329690638231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015641151804439587517641 1511730863853329690638231)
                ·
                  refine ⟨2267596295779994535957347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511730863853329690638231 2267596295779994535957347)
                  ·
                    refine ⟨3401394443669991803936021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267596295779994535957347 3401394443669991803936021)
                    ·
                      refine ⟨159440364547030865809501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3401394443669991803936021 159440364547030865809501)
                      ·
                        rfl

theorem cell23_310509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_310509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310509 prefixEnd_310509 := by exact prefixLift 310509
  have htrace : WordTrace (prefixWord ++ tailWord_310509) baseStart_310509 baseEnd_310509 := by
    simpa [prefixWord, tailWord_310509, baseEnd_310509] using wordTrace_append hprefix tailTrace_310509
  have hstable : (prefixWord ++ tailWord_310509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310509).length < 2 ^ (prefixWord ++ tailWord_310509).sum := by decide
  have hdescent : baseEnd_310509 < baseStart_310509 := by decide
  rcases family_descends (prefixWord ++ tailWord_310509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310522 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_310522 : Nat := 118140960795 + 310522 * 2 ^ 59
def prefixEnd_310522 : Nat := 4983230072969 + 3 ^ 40 * 310522 * 2
def baseEnd_310522 : Nat := 159447039795539314946941

theorem tailTrace_310522 : CollatzResearch.WordTrace tailWord_310522 prefixEnd_310522 159447039795539314946941 := by
  unfold tailWord_310522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831416945259825445135455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7550445187359534520361213 2831416945259825445135455)
  ·
    refine ⟨4247125417889738167703183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2831416945259825445135455 4247125417889738167703183)
    ·
      refine ⟨6370688126834607251554775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247125417889738167703183 6370688126834607251554775)
      ·
        refine ⟨9556032190251910877332163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370688126834607251554775 9556032190251910877332163)
        ·
          refine ⟨14334048285377866315998245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9556032190251910877332163 14334048285377866315998245)
          ·
            refine ⟨2687634053508349934249671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14334048285377866315998245 2687634053508349934249671)
            ·
              refine ⟨4031451080262524901374507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687634053508349934249671 4031451080262524901374507)
              ·
                refine ⟨6047176620393787352061761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031451080262524901374507 6047176620393787352061761)
                ·
                  refine ⟨4535382465295340514046321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047176620393787352061761 4535382465295340514046321)
                  ·
                    refine ⟨3401536848971505385534741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535382465295340514046321 3401536848971505385534741)
                    ·
                      refine ⟨159447039795539314946941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3401536848971505385534741 159447039795539314946941)
                      ·
                        rfl

theorem cell23_310522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_310522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310522 prefixEnd_310522 := by exact prefixLift 310522
  have htrace : WordTrace (prefixWord ++ tailWord_310522) baseStart_310522 baseEnd_310522 := by
    simpa [prefixWord, tailWord_310522, baseEnd_310522] using wordTrace_append hprefix tailTrace_310522
  have hstable : (prefixWord ++ tailWord_310522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310522).length < 2 ^ (prefixWord ++ tailWord_310522).sum := by decide
  have hdescent : baseEnd_310522 < baseStart_310522 := by decide
  rcases family_descends (prefixWord ++ tailWord_310522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310530 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_310530 : Nat := 118140960795 + 310530 * 2 ^ 59
def prefixEnd_310530 : Nat := 4983230072969 + 3 ^ 40 * 310530 * 2
def baseEnd_310530 : Nat := 159451147640775283646905

theorem tailTrace_310530 : CollatzResearch.WordTrace tailWord_310530 prefixEnd_310530 159451147640775283646905 := by
  unfold tailWord_310530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831489891252579786708261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7550639710006879431222029 2831489891252579786708261)
  ·
    refine ⟨530904354609858710007799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2831489891252579786708261 530904354609858710007799)
    ·
      refine ⟨796356531914788065011699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530904354609858710007799 796356531914788065011699)
      ·
        refine ⟨1194534797872182097517549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796356531914788065011699 1194534797872182097517549)
        ·
          refine ⟨447950549202068286569081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1194534797872182097517549 447950549202068286569081)
          ·
            refine ⟨335962911901551214926811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447950549202068286569081 335962911901551214926811)
            ·
              refine ⟨503944367852326822390217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335962911901551214926811 503944367852326822390217)
              ·
                refine ⟨377958275889245116792663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503944367852326822390217 377958275889245116792663)
                ·
                  refine ⟨566937413833867675188995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377958275889245116792663 566937413833867675188995)
                  ·
                    refine ⟨850406120750801512783493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 566937413833867675188995 850406120750801512783493)
                    ·
                      refine ⟨159451147640775283646905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 850406120750801512783493 159451147640775283646905)
                      ·
                        rfl

theorem cell23_310530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_310530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310530 prefixEnd_310530 := by exact prefixLift 310530
  have htrace : WordTrace (prefixWord ++ tailWord_310530) baseStart_310530 baseEnd_310530 := by
    simpa [prefixWord, tailWord_310530, baseEnd_310530] using wordTrace_append hprefix tailTrace_310530
  have hstable : (prefixWord ++ tailWord_310530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310530).length < 2 ^ (prefixWord ++ tailWord_310530).sum := by decide
  have hdescent : baseEnd_310530 < baseStart_310530 := by decide
  rcases family_descends (prefixWord ++ tailWord_310530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310563 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 3]
def baseStart_310563 : Nat := 118140960795 + 310563 * 2 ^ 59
def prefixEnd_310563 : Nat := 4983230072969 + 3 ^ 40 * 310563 * 2
def baseEnd_310563 : Nat := 159468092502373654534253

theorem tailTrace_310563 : CollatzResearch.WordTrace tailWord_310563 prefixEnd_310563 159468092502373654534253 := by
  unfold tailWord_310563
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327163173890765782784343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7551442115927177188522895 11327163173890765782784343)
  ·
    refine ⟨16990744760836148674176515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327163173890765782784343 16990744760836148674176515)
    ·
      refine ⟨25486117141254223011264773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16990744760836148674176515 25486117141254223011264773)
      ·
        refine ⟨4778646963985166814612145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25486117141254223011264773 4778646963985166814612145)
        ·
          refine ⟨3583985222988875110959109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778646963985166814612145 3583985222988875110959109)
          ·
            refine ⟨671997229310414083304833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3583985222988875110959109 671997229310414083304833)
            ·
              refine ⟨503997921982810562478625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671997229310414083304833 503997921982810562478625)
              ·
                refine ⟨377998441487107921858969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503997921982810562478625 377998441487107921858969)
                ·
                  refine ⟨283498831115330941394227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377998441487107921858969 283498831115330941394227)
                  ·
                    refine ⟨425248246672996412091341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 283498831115330941394227 425248246672996412091341)
                    ·
                      refine ⟨159468092502373654534253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425248246672996412091341 159468092502373654534253)
                      ·
                        rfl

theorem cell23_310563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_310563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310563 prefixEnd_310563 := by exact prefixLift 310563
  have htrace : WordTrace (prefixWord ++ tailWord_310563) baseStart_310563 baseEnd_310563 := by
    simpa [prefixWord, tailWord_310563, baseEnd_310563] using wordTrace_append hprefix tailTrace_310563
  have hstable : (prefixWord ++ tailWord_310563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310563).length < 2 ^ (prefixWord ++ tailWord_310563).sum := by decide
  have hdescent : baseEnd_310563 < baseStart_310563 := by decide
  rcases family_descends (prefixWord ++ tailWord_310563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310579 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 2, 6]
def baseStart_310579 : Nat := 118140960795 + 310579 * 2 ^ 59
def prefixEnd_310579 : Nat := 4983230072969 + 3 ^ 40 * 310579 * 2
def baseEnd_310579 : Nat := 53158769397615197311393

theorem tailTrace_310579 : CollatzResearch.WordTrace tailWord_310579 prefixEnd_310579 53158769397615197311393 := by
  unfold tailWord_310579
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327746741832800515366791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7551831161221867010244527 11327746741832800515366791)
  ·
    refine ⟨16991620112749200773050187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327746741832800515366791 16991620112749200773050187)
    ·
      refine ⟨25487430169123801159575281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16991620112749200773050187 25487430169123801159575281)
      ·
        refine ⟨19115572626842850869681461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25487430169123801159575281 19115572626842850869681461)
        ·
          refine ⟨1792084933766517269032637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19115572626842850869681461 1792084933766517269032637)
          ·
            refine ⟨672031850162443975887239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792084933766517269032637 672031850162443975887239)
            ·
              refine ⟨1008047775243665963830859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672031850162443975887239 1008047775243665963830859)
              ·
                refine ⟨1512071662865498945746289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008047775243665963830859 1512071662865498945746289)
                ·
                  refine ⟨1134053747149124209309717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512071662865498945746289 1134053747149124209309717)
                  ·
                    refine ⟨53158769397615197311393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1134053747149124209309717 53158769397615197311393)
                    ·
                      rfl

theorem cell23_310579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 6].length) (baseStart_310579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310579 prefixEnd_310579 := by exact prefixLift 310579
  have htrace : WordTrace (prefixWord ++ tailWord_310579) baseStart_310579 baseEnd_310579 := by
    simpa [prefixWord, tailWord_310579, baseEnd_310579] using wordTrace_append hprefix tailTrace_310579
  have hstable : (prefixWord ++ tailWord_310579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310579).length < 2 ^ (prefixWord ++ tailWord_310579).sum := by decide
  have hdescent : baseEnd_310579 < baseStart_310579 := by decide
  rcases family_descends (prefixWord ++ tailWord_310579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310614 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_310614 : Nat := 118140960795 + 310614 * 2 ^ 59
def prefixEnd_310614 : Nat := 4983230072969 + 3 ^ 40 * 310614 * 2
def baseEnd_310614 : Nat := 159494280015752954996519

theorem tailTrace_310614 : CollatzResearch.WordTrace tailWord_310614 prefixEnd_310614 159494280015752954996519 := by
  unfold tailWord_310614
  simp only [CollatzResearch.WordTrace]
  refine ⟨708063956044125093305681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7552682197804000995260597 708063956044125093305681)
  ·
    refine ⟨531047967033093819979261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708063956044125093305681 531047967033093819979261)
    ·
      refine ⟨199142987637410182492223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 531047967033093819979261 199142987637410182492223)
      ·
        refine ⟨298714481456115273738335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199142987637410182492223 298714481456115273738335)
        ·
          refine ⟨448071722184172910607503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298714481456115273738335 448071722184172910607503)
          ·
            refine ⟨672107583276259365911255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448071722184172910607503 672107583276259365911255)
            ·
              refine ⟨1008161374914389048866883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672107583276259365911255 1008161374914389048866883)
              ·
                refine ⟨1512242062371583573300325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008161374914389048866883 1512242062371583573300325)
                ·
                  refine ⟨283545386694671919993811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1512242062371583573300325 283545386694671919993811)
                  ·
                    refine ⟨425318080042007879990717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 283545386694671919993811 425318080042007879990717)
                    ·
                      refine ⟨159494280015752954996519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425318080042007879990717 159494280015752954996519)
                      ·
                        rfl

theorem cell23_310614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_310614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310614 prefixEnd_310614 := by exact prefixLift 310614
  have htrace : WordTrace (prefixWord ++ tailWord_310614) baseStart_310614 baseEnd_310614 := by
    simpa [prefixWord, tailWord_310614, baseEnd_310614] using wordTrace_append hprefix tailTrace_310614
  have hstable : (prefixWord ++ tailWord_310614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310614).length < 2 ^ (prefixWord ++ tailWord_310614).sum := by decide
  have hdescent : baseEnd_310614 < baseStart_310614 := by decide
  rcases family_descends (prefixWord ++ tailWord_310614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310626 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_310626 : Nat := 118140960795 + 310626 * 2 ^ 59
def prefixEnd_310626 : Nat := 4983230072969 + 3 ^ 40 * 310626 * 2
def baseEnd_310626 : Nat := 17722271309289656449607

theorem tailTrace_310626 : CollatzResearch.WordTrace tailWord_310626 prefixEnd_310626 17722271309289656449607 := by
  unfold tailWord_310626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832365243165631885581933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7552973981775018361551821 2832365243165631885581933)
  ·
    refine ⟨1062136966187111957093225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2832365243165631885581933 1062136966187111957093225)
    ·
      refine ⟨796602724640333967819919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1062136966187111957093225 796602724640333967819919)
      ·
        refine ⟨1194904086960500951729879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796602724640333967819919 1194904086960500951729879)
        ·
          refine ⟨1792356130440751427594819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194904086960500951729879 1792356130440751427594819)
          ·
            refine ⟨2688534195661127141392229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792356130440751427594819 2688534195661127141392229)
            ·
              refine ⟨504100161686461339011043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2688534195661127141392229 504100161686461339011043)
              ·
                refine ⟨756150242529692008516565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504100161686461339011043 756150242529692008516565)
                ·
                  refine ⟨17722271309289656449607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 756150242529692008516565 17722271309289656449607)
                  ·
                    rfl

theorem cell23_310626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_310626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310626 prefixEnd_310626 := by exact prefixLift 310626
  have htrace : WordTrace (prefixWord ++ tailWord_310626) baseStart_310626 baseEnd_310626 := by
    simpa [prefixWord, tailWord_310626, baseEnd_310626] using wordTrace_append hprefix tailTrace_310626
  have hstable : (prefixWord ++ tailWord_310626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310626).length < 2 ^ (prefixWord ++ tailWord_310626).sum := by decide
  have hdescent : baseEnd_310626 < baseStart_310626 := by decide
  rcases family_descends (prefixWord ++ tailWord_310626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310636 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_310636 : Nat := 118140960795 + 310636 * 2 ^ 59
def prefixEnd_310636 : Nat := 4983230072969 + 3 ^ 40 * 310636 * 2
def baseEnd_310636 : Nat := 159505576590151868921417

theorem tailTrace_310636 : CollatzResearch.WordTrace tailWord_310636 prefixEnd_310636 159505576590151868921417 := by
  unfold tailWord_310636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664912851313149625095881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7553217135084199500127841 5664912851313149625095881)
  ·
    refine ⟨4248684638484862218821911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5664912851313149625095881 4248684638484862218821911)
    ·
      refine ⟨6373026957727293328232867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248684638484862218821911 6373026957727293328232867)
      ·
        refine ⟨9559540436590939992349301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373026957727293328232867 9559540436590939992349301)
        ·
          refine ⟨896206915930400624282747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9559540436590939992349301 896206915930400624282747)
          ·
            refine ⟨1344310373895600936424121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896206915930400624282747 1344310373895600936424121)
            ·
              refine ⟨1008232780421700702318091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344310373895600936424121 1008232780421700702318091)
              ·
                refine ⟨1512349170632551053477137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008232780421700702318091 1512349170632551053477137)
                ·
                  refine ⟨1134261877974413290107853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512349170632551053477137 1134261877974413290107853)
                  ·
                    refine ⟨425348204240404983790445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1134261877974413290107853 425348204240404983790445)
                    ·
                      refine ⟨159505576590151868921417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425348204240404983790445 159505576590151868921417)
                      ·
                        rfl

theorem cell23_310636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_310636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310636 prefixEnd_310636 := by exact prefixLift 310636
  have htrace : WordTrace (prefixWord ++ tailWord_310636) baseStart_310636 baseEnd_310636 := by
    simpa [prefixWord, tailWord_310636, baseEnd_310636] using wordTrace_append hprefix tailTrace_310636
  have hstable : (prefixWord ++ tailWord_310636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310636).length < 2 ^ (prefixWord ++ tailWord_310636).sum := by decide
  have hdescent : baseEnd_310636 < baseStart_310636 := by decide
  rcases family_descends (prefixWord ++ tailWord_310636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310637 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_310637 : Nat := 118140960795 + 310637 * 2 ^ 59
def prefixEnd_310637 : Nat := 4983230072969 + 3 ^ 40 * 310637 * 2
def baseEnd_310637 : Nat := 159506090070806365008913

theorem tailTrace_310637 : CollatzResearch.WordTrace tailWord_310637 prefixEnd_310637 159506090070806365008913 := by
  unfold tailWord_310637
  simp only [CollatzResearch.WordTrace]
  refine ⟨11329862175622676420978165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7553241450415117613985443 11329862175622676420978165)
  ·
    refine ⟨1062174578964625914466703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11329862175622676420978165 1062174578964625914466703)
    ·
      refine ⟨1593261868446938871700055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062174578964625914466703 1593261868446938871700055)
      ·
        refine ⟨2389892802670408307550083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593261868446938871700055 2389892802670408307550083)
        ·
          refine ⟨3584839204005612461325125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389892802670408307550083 3584839204005612461325125)
          ·
            refine ⟨672157350751052336498461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3584839204005612461325125 672157350751052336498461)
            ·
              refine ⟨252059006531644626186923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 672157350751052336498461 252059006531644626186923)
              ·
                refine ⟨378088509797466939280385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252059006531644626186923 378088509797466939280385)
                ·
                  refine ⟨283566382348100204460289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378088509797466939280385 283566382348100204460289)
                  ·
                    refine ⟨212674786761075153345217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 283566382348100204460289 212674786761075153345217)
                    ·
                      refine ⟨159506090070806365008913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212674786761075153345217 159506090070806365008913)
                      ·
                        rfl

theorem cell23_310637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_310637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310637 prefixEnd_310637 := by exact prefixLift 310637
  have htrace : WordTrace (prefixWord ++ tailWord_310637) baseStart_310637 baseEnd_310637 := by
    simpa [prefixWord, tailWord_310637, baseEnd_310637] using wordTrace_append hprefix tailTrace_310637
  have hstable : (prefixWord ++ tailWord_310637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310637).length < 2 ^ (prefixWord ++ tailWord_310637).sum := by decide
  have hdescent : baseEnd_310637 < baseStart_310637 := by decide
  rcases family_descends (prefixWord ++ tailWord_310637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310746 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_310746 : Nat := 118140960795 + 310746 * 2 ^ 59
def prefixEnd_310746 : Nat := 4983230072969 + 3 ^ 40 * 310746 * 2
def baseEnd_310746 : Nat := 53187353154048812848637

theorem tailTrace_310746 : CollatzResearch.WordTrace tailWord_310746 prefixEnd_310746 53187353154048812848637 := by
  unfold tailWord_310746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833459433056947009174023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7555891821485192024464061 2833459433056947009174023)
  ·
    refine ⟨4250189149585420513761035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2833459433056947009174023 4250189149585420513761035)
    ·
      refine ⟨6375283724378130770641553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4250189149585420513761035 6375283724378130770641553)
      ·
        refine ⟨4781462793283598077981165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6375283724378130770641553 4781462793283598077981165)
        ·
          refine ⟨1793048547481349279242937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4781462793283598077981165 1793048547481349279242937)
          ·
            refine ⟨1344786410611011959432203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1793048547481349279242937 1344786410611011959432203)
            ·
              refine ⟨2017179615916517939148305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344786410611011959432203 2017179615916517939148305)
              ·
                refine ⟨1512884711937388454361229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017179615916517939148305 1512884711937388454361229)
                ·
                  refine ⟨567331766976520670385461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1512884711937388454361229 567331766976520670385461)
                  ·
                    refine ⟨53187353154048812848637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 567331766976520670385461 53187353154048812848637)
                    ·
                      rfl

theorem cell23_310746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_310746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310746 prefixEnd_310746 := by exact prefixLift 310746
  have htrace : WordTrace (prefixWord ++ tailWord_310746) baseStart_310746 baseEnd_310746 := by
    simpa [prefixWord, tailWord_310746, baseEnd_310746] using wordTrace_append hprefix tailTrace_310746
  have hstable : (prefixWord ++ tailWord_310746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310746).length < 2 ^ (prefixWord ++ tailWord_310746).sum := by decide
  have hdescent : baseEnd_310746 < baseStart_310746 := by decide
  rcases family_descends (prefixWord ++ tailWord_310746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310770 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_310770 : Nat := 118140960795 + 310770 * 2 ^ 59
def prefixEnd_310770 : Nat := 4983230072969 + 3 ^ 40 * 310770 * 2
def baseEnd_310770 : Nat := 159574382997854344645801

theorem tailTrace_310770 : CollatzResearch.WordTrace tailWord_310770 prefixEnd_310770 159574382997854344645801 := by
  unfold tailWord_310770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833678271035210033892441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7556475389427226757046509 2833678271035210033892441)
  ·
    refine ⟨2125258703276407525419331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2833678271035210033892441 2125258703276407525419331)
    ·
      refine ⟨3187888054914611288128997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125258703276407525419331 3187888054914611288128997)
      ·
        refine ⟨597729010296489616524187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3187888054914611288128997 597729010296489616524187)
        ·
          refine ⟨896593515444734424786281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597729010296489616524187 896593515444734424786281)
          ·
            refine ⟨672445136583550818589711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896593515444734424786281 672445136583550818589711)
            ·
              refine ⟨1008667704875326227884567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672445136583550818589711 1008667704875326227884567)
              ·
                refine ⟨1513001557312989341826851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008667704875326227884567 1513001557312989341826851)
                ·
                  refine ⟨2269502335969484012740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513001557312989341826851 2269502335969484012740277)
                  ·
                    refine ⟨212765843997139126194401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2269502335969484012740277 212765843997139126194401)
                    ·
                      refine ⟨159574382997854344645801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212765843997139126194401 159574382997854344645801)
                      ·
                        rfl

theorem cell23_310770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_310770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310770 prefixEnd_310770 := by exact prefixLift 310770
  have htrace : WordTrace (prefixWord ++ tailWord_310770) baseStart_310770 baseEnd_310770 := by
    simpa [prefixWord, tailWord_310770, baseEnd_310770] using wordTrace_append hprefix tailTrace_310770
  have hstable : (prefixWord ++ tailWord_310770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310770).length < 2 ^ (prefixWord ++ tailWord_310770).sum := by decide
  have hdescent : baseEnd_310770 < baseStart_310770 := by decide
  rcases family_descends (prefixWord ++ tailWord_310770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310776 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_310776 : Nat := 118140960795 + 310776 * 2 ^ 59
def prefixEnd_310776 : Nat := 4983230072969 + 3 ^ 40 * 310776 * 2
def baseEnd_310776 : Nat := 53192487960593773723591

theorem tailTrace_310776 : CollatzResearch.WordTrace tailWord_310776 prefixEnd_310776 53192487960593773723591 := by
  unfold tailWord_310776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667465961059551580144091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7556621281412735440192121 5667465961059551580144091)
  ·
    refine ⟨8501198941589327370216137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5667465961059551580144091 8501198941589327370216137)
    ·
      refine ⟨6375899206191995527662103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8501198941589327370216137 6375899206191995527662103)
      ·
        refine ⟨9563848809287993291493155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6375899206191995527662103 9563848809287993291493155)
        ·
          refine ⟨14345773213931989937239733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9563848809287993291493155 14345773213931989937239733)
          ·
            refine ⟨1344916238806124056616225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14345773213931989937239733 1344916238806124056616225)
            ·
              refine ⟨1008687179104593042462169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344916238806124056616225 1008687179104593042462169)
              ·
                refine ⟨756515384328444781846627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008687179104593042462169 756515384328444781846627)
                ·
                  refine ⟨1134773076492667172769941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756515384328444781846627 1134773076492667172769941)
                  ·
                    refine ⟨53192487960593773723591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1134773076492667172769941 53192487960593773723591)
                    ·
                      rfl

theorem cell23_310776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_310776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310776 prefixEnd_310776 := by exact prefixLift 310776
  have htrace : WordTrace (prefixWord ++ tailWord_310776) baseStart_310776 baseEnd_310776 := by
    simpa [prefixWord, tailWord_310776, baseEnd_310776] using wordTrace_append hprefix tailTrace_310776
  have hstable : (prefixWord ++ tailWord_310776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310776).length < 2 ^ (prefixWord ++ tailWord_310776).sum := by decide
  have hdescent : baseEnd_310776 < baseStart_310776 := by decide
  rcases family_descends (prefixWord ++ tailWord_310776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310861 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_310861 : Nat := 118140960795 + 310861 * 2 ^ 59
def prefixEnd_310861 : Nat := 4983230072969 + 3 ^ 40 * 310861 * 2
def baseEnd_310861 : Nat := 53207036579137829535961

theorem tailTrace_310861 : CollatzResearch.WordTrace tailWord_310861 prefixEnd_310861 53207036579137829535961 := by
  unfold tailWord_310861
  simp only [CollatzResearch.WordTrace]
  refine ⟨11338032126811162677132437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7558688084540775118088291 11338032126811162677132437)
  ·
    refine ⟨531470255944273250490583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11338032126811162677132437 531470255944273250490583)
    ·
      refine ⟨797205383916409875735875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531470255944273250490583 797205383916409875735875)
      ·
        refine ⟨1195808075874614813603813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797205383916409875735875 1195808075874614813603813)
        ·
          refine ⟨224214014226490277550715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1195808075874614813603813 224214014226490277550715)
          ·
            refine ⟨336321021339735416326073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224214014226490277550715 336321021339735416326073)
            ·
              refine ⟨252240766004801562244555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336321021339735416326073 252240766004801562244555)
              ·
                refine ⟨378361149007202343366833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252240766004801562244555 378361149007202343366833)
                ·
                  refine ⟨283770861755401757525125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378361149007202343366833 283770861755401757525125)
                  ·
                    refine ⟨53207036579137829535961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283770861755401757525125 53207036579137829535961)
                    ·
                      rfl

theorem cell23_310861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_310861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310861 prefixEnd_310861 := by exact prefixLift 310861
  have htrace : WordTrace (prefixWord ++ tailWord_310861) baseStart_310861 baseEnd_310861 := by
    simpa [prefixWord, tailWord_310861, baseEnd_310861] using wordTrace_append hprefix tailTrace_310861
  have hstable : (prefixWord ++ tailWord_310861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310861).length < 2 ^ (prefixWord ++ tailWord_310861).sum := by decide
  have hdescent : baseEnd_310861 < baseStart_310861 := by decide
  rcases family_descends (prefixWord ++ tailWord_310861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310873 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 5, 4, 2]
def baseStart_310873 : Nat := 118140960795 + 310873 * 2 ^ 59
def prefixEnd_310873 : Nat := 4983230072969 + 3 ^ 40 * 310873 * 2
def baseEnd_310873 : Nat := 159627271505267441657827

theorem tailTrace_310873 : CollatzResearch.WordTrace tailWord_310873 prefixEnd_310873 159627271505267441657827 := by
  unfold tailWord_310873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11338469802767688726569273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7558979868511792484379515 11338469802767688726569273)
  ·
    refine ⟨8503852352075766544926955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11338469802767688726569273 8503852352075766544926955)
    ·
      refine ⟨12755778528113649817390433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8503852352075766544926955 12755778528113649817390433)
      ·
        refine ⟨9566833896085237363042825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12755778528113649817390433 9566833896085237363042825)
        ·
          refine ⟨7175125422063928022282119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9566833896085237363042825 7175125422063928022282119)
          ·
            refine ⟨10762688133095892033423179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175125422063928022282119 10762688133095892033423179)
            ·
              refine ⟨16144032199643838050134769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762688133095892033423179 16144032199643838050134769)
              ·
                refine ⟨12108024149732878537601077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16144032199643838050134769 12108024149732878537601077)
                ·
                  refine ⟨1135127264037457362900101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12108024149732878537601077 1135127264037457362900101)
                  ·
                    refine ⟨212836362007023255543769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1135127264037457362900101 212836362007023255543769)
                    ·
                      refine ⟨159627271505267441657827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212836362007023255543769 159627271505267441657827)
                      ·
                        rfl

theorem cell23_310873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_310873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310873 prefixEnd_310873 := by exact prefixLift 310873
  have htrace : WordTrace (prefixWord ++ tailWord_310873) baseStart_310873 baseEnd_310873 := by
    simpa [prefixWord, tailWord_310873, baseEnd_310873] using wordTrace_append hprefix tailTrace_310873
  have hstable : (prefixWord ++ tailWord_310873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310873).length < 2 ^ (prefixWord ++ tailWord_310873).sum := by decide
  have hdescent : baseEnd_310873 < baseStart_310873 := by decide
  rcases family_descends (prefixWord ++ tailWord_310873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310890 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_310890 : Nat := 118140960795 + 310890 * 2 ^ 59
def prefixEnd_310890 : Nat := 4983230072969 + 3 ^ 40 * 310890 * 2
def baseEnd_310890 : Nat := 159636000676393875145249

theorem tailTrace_310890 : CollatzResearch.WordTrace tailWord_310890 prefixEnd_310890 159636000676393875145249 := by
  unfold tailWord_310890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834772460926525157484531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7559393229137400419958749 2834772460926525157484531)
  ·
    refine ⟨4252158691389787736226797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2834772460926525157484531 4252158691389787736226797)
    ·
      refine ⟨1594559509271170401085049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4252158691389787736226797 1594559509271170401085049)
      ·
        refine ⟨1195919631953377800813787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594559509271170401085049 1195919631953377800813787)
        ·
          refine ⟨1793879447930066701220681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195919631953377800813787 1793879447930066701220681)
          ·
            refine ⟨1345409585947550025915511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1793879447930066701220681 1345409585947550025915511)
            ·
              refine ⟨2018114378921325038873267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345409585947550025915511 2018114378921325038873267)
              ·
                refine ⟨3027171568381987558309901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018114378921325038873267 3027171568381987558309901)
                ·
                  refine ⟨1135189338143245334366213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3027171568381987558309901 1135189338143245334366213)
                  ·
                    refine ⟨212848000901858500193665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1135189338143245334366213 212848000901858500193665)
                    ·
                      refine ⟨159636000676393875145249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212848000901858500193665 159636000676393875145249)
                      ·
                        rfl

theorem cell23_310890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_310890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310890 prefixEnd_310890 := by exact prefixLift 310890
  have htrace : WordTrace (prefixWord ++ tailWord_310890) baseStart_310890 baseEnd_310890 := by
    simpa [prefixWord, tailWord_310890, baseEnd_310890] using wordTrace_append hprefix tailTrace_310890
  have hstable : (prefixWord ++ tailWord_310890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310890).length < 2 ^ (prefixWord ++ tailWord_310890).sum := by decide
  have hdescent : baseEnd_310890 < baseStart_310890 := by decide
  rcases family_descends (prefixWord ++ tailWord_310890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310907 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 2, 2, 2]
def baseStart_310907 : Nat := 118140960795 + 310907 * 2 ^ 59
def prefixEnd_310907 : Nat := 4983230072969 + 3 ^ 40 * 310907 * 2
def baseEnd_310907 : Nat := 159644729847520308632671

theorem tailTrace_310907 : CollatzResearch.WordTrace tailWord_310907 prefixEnd_310907 159644729847520308632671 := by
  unfold tailWord_310907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339709884644512533306975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7559806589763008355537983 11339709884644512533306975)
  ·
    refine ⟨17009564826966768799960463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11339709884644512533306975 17009564826966768799960463)
    ·
      refine ⟨25514347240450153199940695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17009564826966768799960463 25514347240450153199940695)
      ·
        refine ⟨38271520860675229799911043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25514347240450153199940695 38271520860675229799911043)
        ·
          refine ⟨57407281291012844699866565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38271520860675229799911043 57407281291012844699866565)
          ·
            refine ⟨10763865242064908381224981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57407281291012844699866565 10763865242064908381224981)
            ·
              refine ⟨504556183221792580369921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10763865242064908381224981 504556183221792580369921)
              ·
                refine ⟨378417137416344435277441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504556183221792580369921 378417137416344435277441)
                ·
                  refine ⟨283812853062258326458081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378417137416344435277441 283812853062258326458081)
                  ·
                    refine ⟨212859639796693744843561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 283812853062258326458081 212859639796693744843561)
                    ·
                      refine ⟨159644729847520308632671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212859639796693744843561 159644729847520308632671)
                      ·
                        rfl

theorem cell23_310907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2, 2].length) (baseStart_310907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310907 prefixEnd_310907 := by exact prefixLift 310907
  have htrace : WordTrace (prefixWord ++ tailWord_310907) baseStart_310907 baseEnd_310907 := by
    simpa [prefixWord, tailWord_310907, baseEnd_310907] using wordTrace_append hprefix tailTrace_310907
  have hstable : (prefixWord ++ tailWord_310907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310907).length < 2 ^ (prefixWord ++ tailWord_310907).sum := by decide
  have hdescent : baseEnd_310907 < baseStart_310907 := by decide
  rcases family_descends (prefixWord ++ tailWord_310907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310923 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3]
def baseStart_310923 : Nat := 118140960795 + 310923 * 2 ^ 59
def prefixEnd_310923 : Nat := 4983230072969 + 3 ^ 40 * 310923 * 2
def baseEnd_310923 : Nat := 159652945537992246032597

theorem tailTrace_310923 : CollatzResearch.WordTrace tailWord_310923 prefixEnd_310923 159652945537992246032597 := by
  unfold tailWord_310923
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340293452586547265889423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7560195635057698177259615 11340293452586547265889423)
  ·
    refine ⟨17010440178879820898834135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11340293452586547265889423 17010440178879820898834135)
    ·
      refine ⟨25515660268319731348251203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17010440178879820898834135 25515660268319731348251203)
      ·
        refine ⟨38273490402479597022376805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25515660268319731348251203 38273490402479597022376805)
        ·
          refine ⟨7176279450464924441695651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38273490402479597022376805 7176279450464924441695651)
          ·
            refine ⟨10764419175697386662543477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176279450464924441695651 10764419175697386662543477)
            ·
              refine ⟨1009164297721629999613451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10764419175697386662543477 1009164297721629999613451)
              ·
                refine ⟨1513746446582444999420177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009164297721629999613451 1513746446582444999420177)
                ·
                  refine ⟨1135309834936833749565133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1513746446582444999420177 1135309834936833749565133)
                  ·
                    refine ⟨425741188101312656086925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135309834936833749565133 425741188101312656086925)
                    ·
                      refine ⟨159652945537992246032597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425741188101312656086925 159652945537992246032597)
                      ·
                        rfl

theorem cell23_310923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3].length) (baseStart_310923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310923 prefixEnd_310923 := by exact prefixLift 310923
  have htrace : WordTrace (prefixWord ++ tailWord_310923) baseStart_310923 baseEnd_310923 := by
    simpa [prefixWord, tailWord_310923, baseEnd_310923] using wordTrace_append hprefix tailTrace_310923
  have hstable : (prefixWord ++ tailWord_310923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310923).length < 2 ^ (prefixWord ++ tailWord_310923).sum := by decide
  have hdescent : baseEnd_310923 < baseStart_310923 := by decide
  rcases family_descends (prefixWord ++ tailWord_310923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310930 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_310930 : Nat := 118140960795 + 310930 * 2 ^ 59
def prefixEnd_310930 : Nat := 4983230072969 + 3 ^ 40 * 310930 * 2
def baseEnd_310930 : Nat := 17739615544730413182785

theorem tailTrace_310930 : CollatzResearch.WordTrace tailWord_310930 prefixEnd_310930 17739615544730413182785 := by
  unfold tailWord_310930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835137190890296865348561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7560365842374124974262829 2835137190890296865348561)
  ·
    refine ⟨2126352893167722649011421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2835137190890296865348561 2126352893167722649011421)
    ·
      refine ⟨797382334937895993379283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2126352893167722649011421 797382334937895993379283)
      ·
        refine ⟨1196073502406843990068925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797382334937895993379283 1196073502406843990068925)
        ·
          refine ⟨448527563402566496275847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1196073502406843990068925 448527563402566496275847)
          ·
            refine ⟨672791345103849744413771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448527563402566496275847 672791345103849744413771)
            ·
              refine ⟨1009187017655774616620657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672791345103849744413771 1009187017655774616620657)
              ·
                refine ⟨756890263241830962465493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009187017655774616620657 756890263241830962465493)
                ·
                  refine ⟨17739615544730413182785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 756890263241830962465493 17739615544730413182785)
                  ·
                    rfl

theorem cell23_310930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_310930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310930 prefixEnd_310930 := by exact prefixLift 310930
  have htrace : WordTrace (prefixWord ++ tailWord_310930) baseStart_310930 baseEnd_310930 := by
    simpa [prefixWord, tailWord_310930, baseEnd_310930] using wordTrace_append hprefix tailTrace_310930
  have hstable : (prefixWord ++ tailWord_310930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310930).length < 2 ^ (prefixWord ++ tailWord_310930).sum := by decide
  have hdescent : baseEnd_310930 < baseStart_310930 := by decide
  rcases family_descends (prefixWord ++ tailWord_310930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310956 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_310956 : Nat := 118140960795 + 310956 * 2 ^ 59
def prefixEnd_310956 : Nat := 4983230072969 + 3 ^ 40 * 310956 * 2
def baseEnd_310956 : Nat := 53223296799863538973315

theorem tailTrace_310956 : CollatzResearch.WordTrace tailWord_310956 prefixEnd_310956 53223296799863538973315 := by
  unfold tailWord_310956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670748530733496950920361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7560998040977995934560481 5670748530733496950920361)
  ·
    refine ⟨4253061398050122713190271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5670748530733496950920361 4253061398050122713190271)
    ·
      refine ⟨6379592097075184069785407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253061398050122713190271 6379592097075184069785407)
      ·
        refine ⟨9569388145612776104678111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379592097075184069785407 9569388145612776104678111)
        ·
          refine ⟨14354082218419164157017167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569388145612776104678111 14354082218419164157017167)
          ·
            refine ⟨21531123327628746235525751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14354082218419164157017167 21531123327628746235525751)
            ·
              refine ⟨32296684991443119353288627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21531123327628746235525751 32296684991443119353288627)
              ·
                refine ⟨48445027487164679029932941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32296684991443119353288627 48445027487164679029932941)
                ·
                  refine ⟨18166885307686754636224853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48445027487164679029932941 18166885307686754636224853)
                  ·
                    refine ⟨53223296799863538973315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 18166885307686754636224853 53223296799863538973315)
                    ·
                      rfl

theorem cell23_310956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_310956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310956 prefixEnd_310956 := by exact prefixLift 310956
  have htrace : WordTrace (prefixWord ++ tailWord_310956) baseStart_310956 baseEnd_310956 := by
    simpa [prefixWord, tailWord_310956, baseEnd_310956] using wordTrace_append hprefix tailTrace_310956
  have hstable : (prefixWord ++ tailWord_310956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310956).length < 2 ^ (prefixWord ++ tailWord_310956).sum := by decide
  have hdescent : baseEnd_310956 < baseStart_310956 := by decide
  rcases family_descends (prefixWord ++ tailWord_310956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310958 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_310958 : Nat := 118140960795 + 310958 * 2 ^ 59
def prefixEnd_310958 : Nat := 4983230072969 + 3 ^ 40 * 310958 * 2
def baseEnd_310958 : Nat := 159670917360899609094937

theorem tailTrace_310958 : CollatzResearch.WordTrace tailWord_310958 prefixEnd_310958 159670917360899609094937 := by
  unfold tailWord_310958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417696250932468530426691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7561046671639832162275685 1417696250932468530426691)
  ·
    refine ⟨2126544376398702795640037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417696250932468530426691 2126544376398702795640037)
    ·
      refine ⟨398727070574756774182507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2126544376398702795640037 398727070574756774182507)
      ·
        refine ⟨598090605862135161273761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398727070574756774182507 598090605862135161273761)
        ·
          refine ⟨448567954396601370955321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598090605862135161273761 448567954396601370955321)
          ·
            refine ⟨336425965797451028216491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448567954396601370955321 336425965797451028216491)
            ·
              refine ⟨504638948696176542324737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336425965797451028216491 504638948696176542324737)
              ·
                refine ⟨378479211522132406743553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504638948696176542324737 378479211522132406743553)
                ·
                  refine ⟨283859408641599305057665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378479211522132406743553 283859408641599305057665)
                  ·
                    refine ⟨212894556481199478793249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 283859408641599305057665 212894556481199478793249)
                    ·
                      refine ⟨159670917360899609094937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 212894556481199478793249 159670917360899609094937)
                      ·
                        rfl

theorem cell23_310958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_310958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310958 prefixEnd_310958 := by exact prefixLift 310958
  have htrace : WordTrace (prefixWord ++ tailWord_310958) baseStart_310958 baseEnd_310958 := by
    simpa [prefixWord, tailWord_310958, baseEnd_310958] using wordTrace_append hprefix tailTrace_310958
  have hstable : (prefixWord ++ tailWord_310958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310958).length < 2 ^ (prefixWord ++ tailWord_310958).sum := by decide
  have hdescent : baseEnd_310958 < baseStart_310958 := by decide
  rcases family_descends (prefixWord ++ tailWord_310958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310963 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4]
def baseStart_310963 : Nat := 118140960795 + 310963 * 2 ^ 59
def prefixEnd_310963 : Nat := 4983230072969 + 3 ^ 40 * 310963 * 2
def baseEnd_310963 : Nat := 159673484764172089532413

theorem tailTrace_310963 : CollatzResearch.WordTrace tailWord_310963 prefixEnd_310963 159673484764172089532413 := by
  unfold tailWord_310963
  simp only [CollatzResearch.WordTrace]
  refine ⟨11341752372441634097345543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7561168248294422731563695 11341752372441634097345543)
  ·
    refine ⟨17012628558662451146018315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11341752372441634097345543 17012628558662451146018315)
    ·
      refine ⟨25518942837993676719027473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17012628558662451146018315 25518942837993676719027473)
      ·
        refine ⟨19139207128495257539270605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25518942837993676719027473 19139207128495257539270605)
        ·
          refine ⟨7177202673185721577226477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19139207128495257539270605 7177202673185721577226477)
          ·
            refine ⟨2691451002444645591459929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7177202673185721577226477 2691451002444645591459929)
            ·
              refine ⟨2018588251833484193594947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691451002444645591459929 2018588251833484193594947)
              ·
                refine ⟨3027882377750226290392421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018588251833484193594947 3027882377750226290392421)
                ·
                  refine ⟨567727945828167429448579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3027882377750226290392421 567727945828167429448579)
                  ·
                    refine ⟨851591918742251144172869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567727945828167429448579 851591918742251144172869)
                    ·
                      refine ⟨159673484764172089532413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 851591918742251144172869 159673484764172089532413)
                      ·
                        rfl

theorem cell23_310963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_310963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310963 prefixEnd_310963 := by exact prefixLift 310963
  have htrace : WordTrace (prefixWord ++ tailWord_310963) baseStart_310963 baseEnd_310963 := by
    simpa [prefixWord, tailWord_310963, baseEnd_310963] using wordTrace_append hprefix tailTrace_310963
  have hstable : (prefixWord ++ tailWord_310963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310963).length < 2 ^ (prefixWord ++ tailWord_310963).sum := by decide
  have hdescent : baseEnd_310963 < baseStart_310963 := by decide
  rcases family_descends (prefixWord ++ tailWord_310963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310983 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_310983 : Nat := 118140960795 + 310983 * 2 ^ 59
def prefixEnd_310983 : Nat := 4983230072969 + 3 ^ 40 * 310983 * 2
def baseEnd_310983 : Nat := 159683754377262011282321

theorem tailTrace_310983 : CollatzResearch.WordTrace tailWord_310983 prefixEnd_310983 159683754377262011282321 := by
  unfold tailWord_310983
  simp only [CollatzResearch.WordTrace]
  refine ⟨11342481832369177513073603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7561654554912785008715735 11342481832369177513073603)
  ·
    refine ⟨17013722748553766269610405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11342481832369177513073603 17013722748553766269610405)
    ·
      refine ⟨3190073015353831175551951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17013722748553766269610405 3190073015353831175551951)
      ·
        refine ⟨4785109523030746763327927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190073015353831175551951 4785109523030746763327927)
        ·
          refine ⟨7177664284546120144991891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785109523030746763327927 7177664284546120144991891)
          ·
            refine ⟨10766496426819180217487837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177664284546120144991891 10766496426819180217487837)
            ·
              refine ⟨4037436160057192581557939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10766496426819180217487837 4037436160057192581557939)
              ·
                refine ⟨6056154240085788872336909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037436160057192581557939 6056154240085788872336909)
                ·
                  refine ⟨2271057840032170827126341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6056154240085788872336909 2271057840032170827126341)
                  ·
                    refine ⟨425823345006032030086189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271057840032170827126341 425823345006032030086189)
                    ·
                      refine ⟨159683754377262011282321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425823345006032030086189 159683754377262011282321)
                      ·
                        rfl

theorem cell23_310983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_310983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310983 prefixEnd_310983 := by exact prefixLift 310983
  have htrace : WordTrace (prefixWord ++ tailWord_310983) baseStart_310983 baseEnd_310983 := by
    simpa [prefixWord, tailWord_310983, baseEnd_310983] using wordTrace_append hprefix tailTrace_310983
  have hstable : (prefixWord ++ tailWord_310983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310983).length < 2 ^ (prefixWord ++ tailWord_310983).sum := by decide
  have hdescent : baseEnd_310983 < baseStart_310983 := by decide
  rcases family_descends (prefixWord ++ tailWord_310983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310990 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_310990 : Nat := 118140960795 + 310990 * 2 ^ 59
def prefixEnd_310990 : Nat := 4983230072969 + 3 ^ 40 * 310990 * 2
def baseEnd_310990 : Nat := 53229116247281161298263

theorem tailTrace_310990 : CollatzResearch.WordTrace tailWord_310990 prefixEnd_310990 53229116247281161298263 := by
  unfold tailWord_310990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417842142917977213572303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7561824762229211805718949 1417842142917977213572303)
  ·
    refine ⟨2126763214376965820358455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417842142917977213572303 2126763214376965820358455)
    ·
      refine ⟨3190144821565448730537683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126763214376965820358455 3190144821565448730537683)
      ·
        refine ⟨4785217232348173095806525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190144821565448730537683 4785217232348173095806525)
        ·
          refine ⟨1794456462130564910927447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4785217232348173095806525 1794456462130564910927447)
          ·
            refine ⟨2691684693195847366391171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794456462130564910927447 2691684693195847366391171)
            ·
              refine ⟨4037527039793771049586757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691684693195847366391171 4037527039793771049586757)
              ·
                refine ⟨757036319961332071797517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4037527039793771049586757 757036319961332071797517)
                ·
                  refine ⟨283888619985499526924069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757036319961332071797517 283888619985499526924069)
                  ·
                    refine ⟨53229116247281161298263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283888619985499526924069 53229116247281161298263)
                    ·
                      rfl

theorem cell23_310990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_310990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310990 prefixEnd_310990 := by exact prefixLift 310990
  have htrace : WordTrace (prefixWord ++ tailWord_310990) baseStart_310990 baseEnd_310990 := by
    simpa [prefixWord, tailWord_310990, baseEnd_310990] using wordTrace_append hprefix tailTrace_310990
  have hstable : (prefixWord ++ tailWord_310990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310990).length < 2 ^ (prefixWord ++ tailWord_310990).sum := by decide
  have hdescent : baseEnd_310990 < baseStart_310990 := by decide
  rcases family_descends (prefixWord ++ tailWord_310990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310998 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_310998 : Nat := 118140960795 + 310998 * 2 ^ 59
def prefixEnd_310998 : Nat := 4983230072969 + 3 ^ 40 * 310998 * 2
def baseEnd_310998 : Nat := 17743495176342161399417

theorem tailTrace_310998 : CollatzResearch.WordTrace tailWord_310998 prefixEnd_310998 17743495176342161399417 := by
  unfold tailWord_310998
  simp only [CollatzResearch.WordTrace]
  refine ⟨708939307957177192179353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7562019284876556716579765 708939307957177192179353)
  ·
    refine ⟨531704480967882894134515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708939307957177192179353 531704480967882894134515)
    ·
      refine ⟨797556721451824341201773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531704480967882894134515 797556721451824341201773)
      ·
        refine ⟨299083770544434127950665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 797556721451824341201773 299083770544434127950665)
        ·
          refine ⟨224312827908325595962999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299083770544434127950665 224312827908325595962999)
          ·
            refine ⟨336469241862488393944499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224312827908325595962999 336469241862488393944499)
            ·
              refine ⟨504703862793732590916749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336469241862488393944499 504703862793732590916749)
              ·
                refine ⟨189263948547649721593781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504703862793732590916749 189263948547649721593781)
                ·
                  refine ⟨17743495176342161399417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189263948547649721593781 17743495176342161399417)
                  ·
                    rfl

theorem cell23_310998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_310998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_310998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_310998 prefixEnd_310998 := by exact prefixLift 310998
  have htrace : WordTrace (prefixWord ++ tailWord_310998) baseStart_310998 baseEnd_310998 := by
    simpa [prefixWord, tailWord_310998, baseEnd_310998] using wordTrace_append hprefix tailTrace_310998
  have hstable : (prefixWord ++ tailWord_310998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310998).length < 2 ^ (prefixWord ++ tailWord_310998).sum := by decide
  have hdescent : baseEnd_310998 < baseStart_310998 := by decide
  rcases family_descends (prefixWord ++ tailWord_310998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311000 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_311000 : Nat := 118140960795 + 311000 * 2 ^ 59
def prefixEnd_311000 : Nat := 4983230072969 + 3 ^ 40 * 311000 * 2
def baseEnd_311000 : Nat := 159692483548388444769743

theorem tailTrace_311000 : CollatzResearch.WordTrace tailWord_311000 prefixEnd_311000 159692483548388444769743 := by
  unfold tailWord_311000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671550936653794708221227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7562067915538392944294969 5671550936653794708221227)
  ·
    refine ⟨8507326404980692062331841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671550936653794708221227 8507326404980692062331841)
    ·
      refine ⟨6380494803735519046748881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8507326404980692062331841 6380494803735519046748881)
      ·
        refine ⟨4785371102801639285061661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6380494803735519046748881 4785371102801639285061661)
        ·
          refine ⟨1794514163550614731898123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4785371102801639285061661 1794514163550614731898123)
          ·
            refine ⟨2691771245325922097847185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794514163550614731898123 2691771245325922097847185)
            ·
              refine ⟨2018828433994441573385389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691771245325922097847185 2018828433994441573385389)
              ·
                refine ⟨757060662747915590019521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018828433994441573385389 757060662747915590019521)
                ·
                  refine ⟨567795497060936692514641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757060662747915590019521 567795497060936692514641)
                  ·
                    refine ⟨425846622795702519385981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 567795497060936692514641 425846622795702519385981)
                    ·
                      refine ⟨159692483548388444769743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 425846622795702519385981 159692483548388444769743)
                      ·
                        rfl

theorem cell23_311000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_311000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311000 prefixEnd_311000 := by exact prefixLift 311000
  have htrace : WordTrace (prefixWord ++ tailWord_311000) baseStart_311000 baseEnd_311000 := by
    simpa [prefixWord, tailWord_311000, baseEnd_311000] using wordTrace_append hprefix tailTrace_311000
  have hstable : (prefixWord ++ tailWord_311000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311000).length < 2 ^ (prefixWord ++ tailWord_311000).sum := by decide
  have hdescent : baseEnd_311000 < baseStart_311000 := by decide
  rcases family_descends (prefixWord ++ tailWord_311000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311050 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_311050 : Nat := 118140960795 + 311050 * 2 ^ 59
def prefixEnd_311050 : Nat := 4983230072969 + 3 ^ 40 * 311050 * 2
def baseEnd_311050 : Nat := 53239385860371083048171

theorem tailTrace_311050 : CollatzResearch.WordTrace tailWord_311050 prefixEnd_311050 53239385860371083048171 := by
  unfold tailWord_311050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836231380781611988940651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7563283682084298637175069 2836231380781611988940651)
  ·
    refine ⟨4254347071172417983410977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836231380781611988940651 4254347071172417983410977)
    ·
      refine ⟨3190760303379313487558233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4254347071172417983410977 3190760303379313487558233)
      ·
        refine ⟨2393070227534485115668675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3190760303379313487558233 2393070227534485115668675)
        ·
          refine ⟨3589605341301727673503013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393070227534485115668675 3589605341301727673503013)
          ·
            refine ⟨673051001494073938781815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3589605341301727673503013 673051001494073938781815)
            ·
              refine ⟨1009576502241110908172723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673051001494073938781815 1009576502241110908172723)
              ·
                refine ⟨1514364753361666362259085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009576502241110908172723 1514364753361666362259085)
                ·
                  refine ⟨567886782510624885847157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1514364753361666362259085 567886782510624885847157)
                  ·
                    refine ⟨53239385860371083048171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 567886782510624885847157 53239385860371083048171)
                    ·
                      rfl

theorem cell23_311050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_311050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311050 prefixEnd_311050 := by exact prefixLift 311050
  have htrace : WordTrace (prefixWord ++ tailWord_311050) baseStart_311050 baseEnd_311050 := by
    simpa [prefixWord, tailWord_311050, baseEnd_311050] using wordTrace_append hprefix tailTrace_311050
  have hstable : (prefixWord ++ tailWord_311050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311050).length < 2 ^ (prefixWord ++ tailWord_311050).sum := by decide
  have hdescent : baseEnd_311050 < baseStart_311050 := by decide
  rcases family_descends (prefixWord ++ tailWord_311050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311100 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_311100 : Nat := 118140960795 + 311100 * 2 ^ 59
def prefixEnd_311100 : Nat := 4983230072969 + 3 ^ 40 * 311100 * 2
def baseEnd_311100 : Nat := 159743831613838053519283

theorem tailTrace_311100 : CollatzResearch.WordTrace tailWord_311100 prefixEnd_311100 159743831613838053519283 := by
  unfold tailWord_311100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673374586472653247541377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7564499448630204330055169 5673374586472653247541377)
  ·
    refine ⟨4255030939854489935656033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5673374586472653247541377 4255030939854489935656033)
    ·
      refine ⟨3191273204890867451742025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4255030939854489935656033 3191273204890867451742025)
      ·
        refine ⟨2393454903668150588806519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3191273204890867451742025 2393454903668150588806519)
        ·
          refine ⟨3590182355502225883209779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393454903668150588806519 3590182355502225883209779)
          ·
            refine ⟨5385273533253338824814669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590182355502225883209779 5385273533253338824814669)
            ·
              refine ⟨2019477574970002059305501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5385273533253338824814669 2019477574970002059305501)
              ·
                refine ⟨757304090613750772239563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2019477574970002059305501 757304090613750772239563)
                ·
                  refine ⟨1135956135920626158359345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757304090613750772239563 1135956135920626158359345)
                  ·
                    refine ⟨851967101940469618769509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135956135920626158359345 851967101940469618769509)
                    ·
                      refine ⟨159743831613838053519283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 851967101940469618769509 159743831613838053519283)
                      ·
                        rfl

theorem cell23_311100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_311100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311100 prefixEnd_311100 := by exact prefixLift 311100
  have htrace : WordTrace (prefixWord ++ tailWord_311100) baseStart_311100 baseEnd_311100 := by
    simpa [prefixWord, tailWord_311100, baseEnd_311100] using wordTrace_append hprefix tailTrace_311100
  have hstable : (prefixWord ++ tailWord_311100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311100).length < 2 ^ (prefixWord ++ tailWord_311100).sum := by decide
  have hdescent : baseEnd_311100 < baseStart_311100 := by decide
  rcases family_descends (prefixWord ++ tailWord_311100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311121 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 1, 2, 2]
def baseStart_311121 : Nat := 118140960795 + 311121 * 2 ^ 59
def prefixEnd_311121 : Nat := 4983230072969 + 3 ^ 40 * 311121 * 2
def baseEnd_311121 : Nat := 159754614707582471356687

theorem tailTrace_311121 : CollatzResearch.WordTrace tailWord_311121 prefixEnd_311121 159754614707582471356687 := by
  unfold tailWord_311121
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347515105869227081597217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7565010070579484721064811 11347515105869227081597217)
  ·
    refine ⟨8510636329401920311197913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11347515105869227081597217 8510636329401920311197913)
    ·
      refine ⟨6382977247051440233398435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8510636329401920311197913 6382977247051440233398435)
      ·
        refine ⟨9574465870577160350097653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6382977247051440233398435 9574465870577160350097653)
        ·
          refine ⟨897606175366608782821655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9574465870577160350097653 897606175366608782821655)
          ·
            refine ⟨1346409263049913174232483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897606175366608782821655 1346409263049913174232483)
            ·
              refine ⟨2019613894574869761348725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346409263049913174232483 2019613894574869761348725)
              ·
                refine ⟨189338802616394040126443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2019613894574869761348725 189338802616394040126443)
                ·
                  refine ⟨284008203924591060189665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189338802616394040126443 284008203924591060189665)
                  ·
                    refine ⟨213006152943443295142249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284008203924591060189665 213006152943443295142249)
                    ·
                      refine ⟨159754614707582471356687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213006152943443295142249 159754614707582471356687)
                      ·
                        rfl

theorem cell23_311121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_311121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311121 prefixEnd_311121 := by exact prefixLift 311121
  have htrace : WordTrace (prefixWord ++ tailWord_311121) baseStart_311121 baseEnd_311121 := by
    simpa [prefixWord, tailWord_311121, baseEnd_311121] using wordTrace_append hprefix tailTrace_311121
  have hstable : (prefixWord ++ tailWord_311121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311121).length < 2 ^ (prefixWord ++ tailWord_311121).sum := by decide
  have hdescent : baseEnd_311121 < baseStart_311121 := by decide
  rcases family_descends (prefixWord ++ tailWord_311121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311124 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_311124 : Nat := 118140960795 + 311124 * 2 ^ 59
def prefixEnd_311124 : Nat := 4983230072969 + 3 ^ 40 * 311124 * 2
def baseEnd_311124 : Nat := 159756155149545959619173

theorem tailTrace_311124 : CollatzResearch.WordTrace tailWord_311124 prefixEnd_311124 159756155149545959619173 := by
  unfold tailWord_311124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673812262429179296978213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7565083016572239062637617 5673812262429179296978213)
  ·
    refine ⟨1063839799205471118183415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5673812262429179296978213 1063839799205471118183415)
    ·
      refine ⟨1595759698808206677275123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063839799205471118183415 1595759698808206677275123)
      ·
        refine ⟨2393639548212310015912685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595759698808206677275123 2393639548212310015912685)
        ·
          refine ⟨897614830579616255967257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2393639548212310015912685 897614830579616255967257)
          ·
            refine ⟨673211122934712191975443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897614830579616255967257 673211122934712191975443)
            ·
              refine ⟨1009816684402068287963165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673211122934712191975443 1009816684402068287963165)
              ·
                refine ⟨378681256650775607986187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009816684402068287963165 378681256650775607986187)
                ·
                  refine ⟨568021884976163411979281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378681256650775607986187 568021884976163411979281)
                  ·
                    refine ⟨426016413732122558984461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 568021884976163411979281 426016413732122558984461)
                    ·
                      refine ⟨159756155149545959619173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426016413732122558984461 159756155149545959619173)
                      ·
                        rfl

theorem cell23_311124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_311124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311124 prefixEnd_311124 := by exact prefixLift 311124
  have htrace : WordTrace (prefixWord ++ tailWord_311124) baseStart_311124 baseEnd_311124 := by
    simpa [prefixWord, tailWord_311124, baseEnd_311124] using wordTrace_append hprefix tailTrace_311124
  have hstable : (prefixWord ++ tailWord_311124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311124).length < 2 ^ (prefixWord ++ tailWord_311124).sum := by decide
  have hdescent : baseEnd_311124 < baseStart_311124 := by decide
  rcases family_descends (prefixWord ++ tailWord_311124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311137 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_311137 : Nat := 118140960795 + 311137 * 2 ^ 59
def prefixEnd_311137 : Nat := 4983230072969 + 3 ^ 40 * 311137 * 2
def baseEnd_311137 : Nat := 159762830398054408756613

theorem tailTrace_311137 : CollatzResearch.WordTrace tailWord_311137 prefixEnd_311137 159762830398054408756613 := by
  unfold tailWord_311137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348098673811261814179665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7565399115874174542786443 11348098673811261814179665)
  ·
    refine ⟨8511074005358446360634749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11348098673811261814179665 8511074005358446360634749)
    ·
      refine ⟨3191652752009417385238031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8511074005358446360634749 3191652752009417385238031)
      ·
        refine ⟨4787479128014126077857047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191652752009417385238031 4787479128014126077857047)
        ·
          refine ⟨7181218692021189116785571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787479128014126077857047 7181218692021189116785571)
          ·
            refine ⟨10771828038031783675178357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181218692021189116785571 10771828038031783675178357)
            ·
              refine ⟨1009858878565479719547971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10771828038031783675178357 1009858878565479719547971)
              ·
                refine ⟨1514788317848219579321957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009858878565479719547971 1514788317848219579321957)
                ·
                  refine ⟨284022809596541171122867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1514788317848219579321957 284022809596541171122867)
                  ·
                    refine ⟨426034214394811756684301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 284022809596541171122867 426034214394811756684301)
                    ·
                      refine ⟨159762830398054408756613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426034214394811756684301 159762830398054408756613)
                      ·
                        rfl

theorem cell23_311137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_311137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311137 prefixEnd_311137 := by exact prefixLift 311137
  have htrace : WordTrace (prefixWord ++ tailWord_311137) baseStart_311137 baseEnd_311137 := by
    simpa [prefixWord, tailWord_311137, baseEnd_311137] using wordTrace_append hprefix tailTrace_311137
  have hstable : (prefixWord ++ tailWord_311137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311137).length < 2 ^ (prefixWord ++ tailWord_311137).sum := by decide
  have hdescent : baseEnd_311137 < baseStart_311137 := by decide
  rcases family_descends (prefixWord ++ tailWord_311137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311138 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_311138 : Nat := 118140960795 + 311138 * 2 ^ 59
def prefixEnd_311138 : Nat := 4983230072969 + 3 ^ 40 * 311138 * 2
def baseEnd_311138 : Nat := 159763343878708904844109

theorem tailTrace_311138 : CollatzResearch.WordTrace tailWord_311138 prefixEnd_311138 159763343878708904844109 := by
  unfold tailWord_311138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837033786701909746241517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7565423431205092656644045 2837033786701909746241517)
  ·
    refine ⟨1063887670013216154840569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2837033786701909746241517 1063887670013216154840569)
    ·
      refine ⟨797915752509912116130427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1063887670013216154840569 797915752509912116130427)
      ·
        refine ⟨1196873628764868174195641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797915752509912116130427 1196873628764868174195641)
        ·
          refine ⟨897655221573651130646731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196873628764868174195641 897655221573651130646731)
          ·
            refine ⟨1346482832360476695970097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897655221573651130646731 1346482832360476695970097)
            ·
              refine ⟨1009862124270357521977573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346482832360476695970097 1009862124270357521977573)
              ·
                refine ⟨189349148300692035370795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1009862124270357521977573 189349148300692035370795)
                ·
                  refine ⟨284023722451038053056193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189349148300692035370795 284023722451038053056193)
                  ·
                    refine ⟨213017791838278539792145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284023722451038053056193 213017791838278539792145)
                    ·
                      refine ⟨159763343878708904844109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213017791838278539792145 159763343878708904844109)
                      ·
                        rfl

theorem cell23_311138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_311138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311138 prefixEnd_311138 := by exact prefixLift 311138
  have htrace : WordTrace (prefixWord ++ tailWord_311138) baseStart_311138 baseEnd_311138 := by
    simpa [prefixWord, tailWord_311138, baseEnd_311138] using wordTrace_append hprefix tailTrace_311138
  have hstable : (prefixWord ++ tailWord_311138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311138).length < 2 ^ (prefixWord ++ tailWord_311138).sum := by decide
  have hdescent : baseEnd_311138 < baseStart_311138 := by decide
  rcases family_descends (prefixWord ++ tailWord_311138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311177 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 3, 4, 2]
def baseStart_311177 : Nat := 118140960795 + 311177 * 2 ^ 59
def prefixEnd_311177 : Nat := 4983230072969 + 3 ^ 40 * 311177 * 2
def baseEnd_311177 : Nat := 159783369624234252256429

theorem tailTrace_311177 : CollatzResearch.WordTrace tailWord_311177 prefixEnd_311177 159783369624234252256429 := by
  unfold tailWord_311177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349557593666348645635785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7566371729110899097090523 11349557593666348645635785)
  ·
    refine ⟨8512168195249761484226839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11349557593666348645635785 8512168195249761484226839)
    ·
      refine ⟨12768252292874642226340259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8512168195249761484226839 12768252292874642226340259)
      ·
        refine ⟨19152378439311963339510389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12768252292874642226340259 19152378439311963339510389)
        ·
          refine ⟨1795535478685496563079099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19152378439311963339510389 1795535478685496563079099)
          ·
            refine ⟨2693303218028244844618649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795535478685496563079099 2693303218028244844618649)
            ·
              refine ⟨2019977413521183633463987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693303218028244844618649 2019977413521183633463987)
              ·
                refine ⟨3029966120281775450195981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019977413521183633463987 3029966120281775450195981)
                ·
                  refine ⟨1136237295105665793823493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3029966120281775450195981 1136237295105665793823493)
                  ·
                    refine ⟨213044492832312336341905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136237295105665793823493 213044492832312336341905)
                    ·
                      refine ⟨159783369624234252256429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213044492832312336341905 159783369624234252256429)
                      ·
                        rfl

theorem cell23_311177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4, 2].length) (baseStart_311177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311177 prefixEnd_311177 := by exact prefixLift 311177
  have htrace : WordTrace (prefixWord ++ tailWord_311177) baseStart_311177 baseEnd_311177 := by
    simpa [prefixWord, tailWord_311177, baseEnd_311177] using wordTrace_append hprefix tailTrace_311177
  have hstable : (prefixWord ++ tailWord_311177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311177).length < 2 ^ (prefixWord ++ tailWord_311177).sum := by decide
  have hdescent : baseEnd_311177 < baseStart_311177 := by decide
  rcases family_descends (prefixWord ++ tailWord_311177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311180 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_311180 : Nat := 118140960795 + 311180 * 2 ^ 59
def prefixEnd_311180 : Nat := 4983230072969 + 3 ^ 40 * 311180 * 2
def baseEnd_311180 : Nat := 159784910066197740518915

theorem tailTrace_311180 : CollatzResearch.WordTrace tailWord_311180 prefixEnd_311180 159784910066197740518915 := by
  unfold tailWord_311180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674833506327740078997497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7566444675103653438663329 5674833506327740078997497)
  ·
    refine ⟨4256125129745805059248123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5674833506327740078997497 4256125129745805059248123)
    ·
      refine ⟨6384187694618707588872185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256125129745805059248123 6384187694618707588872185)
      ·
        refine ⟨4788140770964030691654139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384187694618707588872185 4788140770964030691654139)
        ·
          refine ⟨7182211156446046037481209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788140770964030691654139 7182211156446046037481209)
          ·
            refine ⟨5386658367334534528110907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7182211156446046037481209 5386658367334534528110907)
            ·
              refine ⟨8079987551001801792166361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386658367334534528110907 8079987551001801792166361)
              ·
                refine ⟨6059990663251351344124771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8079987551001801792166361 6059990663251351344124771)
                ·
                  refine ⟨9089985994877027016187157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059990663251351344124771 9089985994877027016187157)
                  ·
                    refine ⟨426093093509860641383773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9089985994877027016187157 426093093509860641383773)
                    ·
                      refine ⟨159784910066197740518915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426093093509860641383773 159784910066197740518915)
                      ·
                        rfl

theorem cell23_311180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_311180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311180 prefixEnd_311180 := by exact prefixLift 311180
  have htrace : WordTrace (prefixWord ++ tailWord_311180) baseStart_311180 baseEnd_311180 := by
    simpa [prefixWord, tailWord_311180, baseEnd_311180] using wordTrace_append hprefix tailTrace_311180
  have hstable : (prefixWord ++ tailWord_311180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311180).length < 2 ^ (prefixWord ++ tailWord_311180).sum := by decide
  have hdescent : baseEnd_311180 < baseStart_311180 := by decide
  rcases family_descends (prefixWord ++ tailWord_311180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311281 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 2, 5]
def baseStart_311281 : Nat := 118140960795 + 311281 * 2 ^ 59
def prefixEnd_311281 : Nat := 4983230072969 + 3 ^ 40 * 311281 * 2
def baseEnd_311281 : Nat := 53278923870767281785317

theorem tailTrace_311281 : CollatzResearch.WordTrace tailWord_311281 prefixEnd_311281 53278923870767281785317 := by
  unfold tailWord_311281
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353350785289574407421697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7568900523526382938281131 11353350785289574407421697)
  ·
    refine ⟨8515013088967180805566273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11353350785289574407421697 8515013088967180805566273)
    ·
      refine ⟨6386259816725385604174705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8515013088967180805566273 6386259816725385604174705)
      ·
        refine ⟨4789694862544039203131029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6386259816725385604174705 4789694862544039203131029)
        ·
          refine ⟨224516946681751837646767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4789694862544039203131029 224516946681751837646767)
          ·
            refine ⟨336775420022627756470151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224516946681751837646767 336775420022627756470151)
            ·
              refine ⟨505163130033941634705227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336775420022627756470151 505163130033941634705227)
              ·
                refine ⟨757744695050912452057841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505163130033941634705227 757744695050912452057841)
                ·
                  refine ⟨568308521288184339043381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757744695050912452057841 568308521288184339043381)
                  ·
                    refine ⟨53278923870767281785317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 568308521288184339043381 53278923870767281785317)
                    ·
                      rfl

theorem cell23_311281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_311281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311281 prefixEnd_311281 := by exact prefixLift 311281
  have htrace : WordTrace (prefixWord ++ tailWord_311281) baseStart_311281 baseEnd_311281 := by
    simpa [prefixWord, tailWord_311281, baseEnd_311281] using wordTrace_append hprefix tailTrace_311281
  have hstable : (prefixWord ++ tailWord_311281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311281).length < 2 ^ (prefixWord ++ tailWord_311281).sum := by decide
  have hdescent : baseEnd_311281 < baseStart_311281 := by decide
  rcases family_descends (prefixWord ++ tailWord_311281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311344 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2]
def baseStart_311344 : Nat := 118140960795 + 311344 * 2 ^ 59
def prefixEnd_311344 : Nat := 4983230072969 + 3 ^ 40 * 311344 * 2
def baseEnd_311344 : Nat := 159869120893535098868161

theorem tailTrace_311344 : CollatzResearch.WordTrace tailWord_311344 prefixEnd_311344 159869120893535098868161 := by
  unfold tailWord_311344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677824292030668083482543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7570432389374224111310057 5677824292030668083482543)
  ·
    refine ⟨8516736438046002125223815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5677824292030668083482543 8516736438046002125223815)
    ·
      refine ⟨12775104657069003187835723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516736438046002125223815 12775104657069003187835723)
      ·
        refine ⟨19162656985603504781753585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12775104657069003187835723 19162656985603504781753585)
        ·
          refine ⟨14371992739202628586315189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19162656985603504781753585 14371992739202628586315189)
          ·
            refine ⟨1347374319300246429967049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14371992739202628586315189 1347374319300246429967049)
            ·
              refine ⟨1010530739475184822475287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347374319300246429967049 1010530739475184822475287)
              ·
                refine ⟨1515796109212777233712931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010530739475184822475287 1515796109212777233712931)
                ·
                  refine ⟨2273694163819165850569397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515796109212777233712931 2273694163819165850569397)
                  ·
                    refine ⟨213158827858046798490881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2273694163819165850569397 213158827858046798490881)
                    ·
                      refine ⟨159869120893535098868161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213158827858046798490881 159869120893535098868161)
                      ·
                        rfl

theorem cell23_311344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2].length) (baseStart_311344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311344 prefixEnd_311344 := by exact prefixLift 311344
  have htrace : WordTrace (prefixWord ++ tailWord_311344) baseStart_311344 baseEnd_311344 := by
    simpa [prefixWord, tailWord_311344, baseEnd_311344] using wordTrace_append hprefix tailTrace_311344
  have hstable : (prefixWord ++ tailWord_311344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311344).length < 2 ^ (prefixWord ++ tailWord_311344).sum := by decide
  have hdescent : baseEnd_311344 < baseStart_311344 := by decide
  rcases family_descends (prefixWord ++ tailWord_311344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311361 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_311361 : Nat := 118140960795 + 311361 * 2 ^ 59
def prefixEnd_311361 : Nat := 4983230072969 + 3 ^ 40 * 311361 * 2
def baseEnd_311361 : Nat := 159877850064661532355583

theorem tailTrace_311361 : CollatzResearch.WordTrace tailWord_311361 prefixEnd_311361 159877850064661532355583 := by
  unfold tailWord_311361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356268624999748070333937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7570845749999832046889291 11356268624999748070333937)
  ·
    refine ⟨8517201468749811052750453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11356268624999748070333937 8517201468749811052750453)
    ·
      refine ⟨798487637695294786195355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8517201468749811052750453 798487637695294786195355)
      ·
        refine ⟨1197731456542942179293033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798487637695294786195355 1197731456542942179293033)
        ·
          refine ⟨898298592407206634469775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197731456542942179293033 898298592407206634469775)
          ·
            refine ⟨1347447888610809951704663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898298592407206634469775 1347447888610809951704663)
            ·
              refine ⟨2021171832916214927556995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347447888610809951704663 2021171832916214927556995)
              ·
                refine ⟨3031757749374322391335493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021171832916214927556995 3031757749374322391335493)
                ·
                  refine ⟨568454578007685448375405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3031757749374322391335493 568454578007685448375405)
                  ·
                    refine ⟨213170466752882043140777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568454578007685448375405 213170466752882043140777)
                    ·
                      refine ⟨159877850064661532355583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213170466752882043140777 159877850064661532355583)
                      ·
                        rfl

theorem cell23_311361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_311361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311361 prefixEnd_311361 := by exact prefixLift 311361
  have htrace : WordTrace (prefixWord ++ tailWord_311361) baseStart_311361 baseEnd_311361 := by
    simpa [prefixWord, tailWord_311361, baseEnd_311361] using wordTrace_append hprefix tailTrace_311361
  have hstable : (prefixWord ++ tailWord_311361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311361).length < 2 ^ (prefixWord ++ tailWord_311361).sum := by decide
  have hdescent : baseEnd_311361 < baseStart_311361 := by decide
  rcases family_descends (prefixWord ++ tailWord_311361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311377 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_311377 : Nat := 118140960795 + 311377 * 2 ^ 59
def prefixEnd_311377 : Nat := 4983230072969 + 3 ^ 40 * 311377 * 2
def baseEnd_311377 : Nat := 159886065755133469755509

theorem tailTrace_311377 : CollatzResearch.WordTrace tailWord_311377 prefixEnd_311377 159886065755133469755509 := by
  unfold tailWord_311377
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356852192941782802916385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7571234795294521868610923 11356852192941782802916385)
  ·
    refine ⟨8517639144706337102187289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11356852192941782802916385 8517639144706337102187289)
    ·
      refine ⟨6388229358529752826640467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8517639144706337102187289 6388229358529752826640467)
      ·
        refine ⟨9582344037794629239960701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388229358529752826640467 9582344037794629239960701)
        ·
          refine ⟨3593379014172985964985263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9582344037794629239960701 3593379014172985964985263)
          ·
            refine ⟨5390068521259478947477895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593379014172985964985263 5390068521259478947477895)
            ·
              refine ⟨8085102781889218421216843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5390068521259478947477895 8085102781889218421216843)
              ·
                refine ⟨12127654172833827631825265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8085102781889218421216843 12127654172833827631825265)
                ·
                  refine ⟨9095740629625370723868949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12127654172833827631825265 9095740629625370723868949)
                  ·
                    refine ⟨426362842013689252681357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9095740629625370723868949 426362842013689252681357)
                    ·
                      refine ⟨159886065755133469755509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426362842013689252681357 159886065755133469755509)
                      ·
                        rfl

theorem cell23_311377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_311377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311377 prefixEnd_311377 := by exact prefixLift 311377
  have htrace : WordTrace (prefixWord ++ tailWord_311377) baseStart_311377 baseEnd_311377 := by
    simpa [prefixWord, tailWord_311377, baseEnd_311377] using wordTrace_append hprefix tailTrace_311377
  have hstable : (prefixWord ++ tailWord_311377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311377).length < 2 ^ (prefixWord ++ tailWord_311377).sum := by decide
  have hdescent : baseEnd_311377 < baseStart_311377 := by decide
  rcases family_descends (prefixWord ++ tailWord_311377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311397 : List Nat := [1, 3, 1, 3, 2, 2, 2, 9]
def baseStart_311397 : Nat := 118140960795 + 311397 * 2 ^ 59
def prefixEnd_311397 : Nat := 4983230072969 + 3 ^ 40 * 311397 * 2
def baseEnd_311397 : Nat := 5922086495119384870571

theorem tailTrace_311397 : CollatzResearch.WordTrace tailWord_311397 prefixEnd_311397 5922086495119384870571 := by
  unfold tailWord_311397
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357581652869326218644445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7571721101912884145762963 11357581652869326218644445)
  ·
    refine ⟨4259093119825997331991667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11357581652869326218644445 4259093119825997331991667)
    ·
      refine ⟨6388639679738995997987501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259093119825997331991667 6388639679738995997987501)
      ·
        refine ⟨2395739879902123499245313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6388639679738995997987501 2395739879902123499245313)
        ·
          refine ⟨1796804909926592624433985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395739879902123499245313 1796804909926592624433985)
          ·
            refine ⟨1347603682444944468325489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1796804909926592624433985 1347603682444944468325489)
            ·
              refine ⟨1010702761833708351244117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347603682444944468325489 1010702761833708351244117)
              ·
                refine ⟨5922086495119384870571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1010702761833708351244117 5922086495119384870571)
                ·
                  rfl

theorem cell23_311397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 9].length) (baseStart_311397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311397 prefixEnd_311397 := by exact prefixLift 311397
  have htrace : WordTrace (prefixWord ++ tailWord_311397) baseStart_311397 baseEnd_311397 := by
    simpa [prefixWord, tailWord_311397, baseEnd_311397] using wordTrace_append hprefix tailTrace_311397
  have hstable : (prefixWord ++ tailWord_311397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311397).length < 2 ^ (prefixWord ++ tailWord_311397).sum := by decide
  have hdescent : baseEnd_311397 < baseStart_311397 := by decide
  rcases family_descends (prefixWord ++ tailWord_311397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311404 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_311404 : Nat := 118140960795 + 311404 * 2 ^ 59
def prefixEnd_311404 : Nat := 4983230072969 + 3 ^ 40 * 311404 * 2
def baseEnd_311404 : Nat := 159899929732804864117885

theorem tailTrace_311404 : CollatzResearch.WordTrace tailWord_311404 prefixEnd_311404 159899929732804864117885 := by
  unfold tailWord_311404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678918481921983207074633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7571891309229310942766177 5678918481921983207074633)
  ·
    refine ⟨4259188861441487405305975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5678918481921983207074633 4259188861441487405305975)
    ·
      refine ⟨6388783292162231107958963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259188861441487405305975 6388783292162231107958963)
      ·
        refine ⟨9583174938243346661938445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388783292162231107958963 9583174938243346661938445)
        ·
          refine ⟨3593690601841254998226917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9583174938243346661938445 3593690601841254998226917)
          ·
            refine ⟨673816987845235312167547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3593690601841254998226917 673816987845235312167547)
            ·
              refine ⟨1010725481767852968251321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673816987845235312167547 1010725481767852968251321)
              ·
                refine ⟨758044111325889726188491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010725481767852968251321 758044111325889726188491)
                ·
                  refine ⟨1137066166988834589282737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758044111325889726188491 1137066166988834589282737)
                  ·
                    refine ⟨852799625241625941962053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1137066166988834589282737 852799625241625941962053)
                    ·
                      refine ⟨159899929732804864117885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 852799625241625941962053 159899929732804864117885)
                      ·
                        rfl

theorem cell23_311404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_311404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311404 prefixEnd_311404 := by exact prefixLift 311404
  have htrace : WordTrace (prefixWord ++ tailWord_311404) baseStart_311404 baseEnd_311404 := by
    simpa [prefixWord, tailWord_311404, baseEnd_311404] using wordTrace_append hprefix tailTrace_311404
  have hstable : (prefixWord ++ tailWord_311404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311404).length < 2 ^ (prefixWord ++ tailWord_311404).sum := by decide
  have hdescent : baseEnd_311404 < baseStart_311404 := by decide
  rcases family_descends (prefixWord ++ tailWord_311404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311427 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 7]
def baseStart_311427 : Nat := 118140960795 + 311427 * 2 ^ 59
def prefixEnd_311427 : Nat := 4983230072969 + 3 ^ 40 * 311427 * 2
def baseEnd_311427 : Nat := 53303913262619424710093

theorem tailTrace_311427 : CollatzResearch.WordTrace tailWord_311427 prefixEnd_311427 53303913262619424710093 := by
  unfold tailWord_311427
  simp only [CollatzResearch.WordTrace]
  refine ⟨11358675842760641342236535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7572450561840427561491023 11358675842760641342236535)
  ·
    refine ⟨17038013764140962013354803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11358675842760641342236535 17038013764140962013354803)
    ·
      refine ⟨25557020646211443020032205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17038013764140962013354803 25557020646211443020032205)
      ·
        refine ⟨9583882742329291132512077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25557020646211443020032205 9583882742329291132512077)
        ·
          refine ⟨3593956028373484174692029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9583882742329291132512077 3593956028373484174692029)
          ·
            refine ⟨1347733510640056565509511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3593956028373484174692029 1347733510640056565509511)
            ·
              refine ⟨2021600265960084848264267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347733510640056565509511 2021600265960084848264267)
              ·
                refine ⟨3032400398940127272396401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021600265960084848264267 3032400398940127272396401)
                ·
                  refine ⟨2274300299205095454297301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032400398940127272396401 2274300299205095454297301)
                  ·
                    refine ⟨53303913262619424710093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2274300299205095454297301 53303913262619424710093)
                    ·
                      rfl

theorem cell23_311427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_311427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311427 prefixEnd_311427 := by exact prefixLift 311427
  have htrace : WordTrace (prefixWord ++ tailWord_311427) baseStart_311427 baseEnd_311427 := by
    simpa [prefixWord, tailWord_311427, baseEnd_311427] using wordTrace_append hprefix tailTrace_311427
  have hstable : (prefixWord ++ tailWord_311427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311427).length < 2 ^ (prefixWord ++ tailWord_311427).sum := by decide
  have hdescent : baseEnd_311427 < baseStart_311427 := by decide
  rcases family_descends (prefixWord ++ tailWord_311427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311446 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_311446 : Nat := 118140960795 + 311446 * 2 ^ 59
def prefixEnd_311446 : Nat := 4983230072969 + 3 ^ 40 * 311446 * 2
def baseEnd_311446 : Nat := 159921495920293699792693

theorem tailTrace_311446 : CollatzResearch.WordTrace tailWord_311446 prefixEnd_311446 159921495920293699792693 := by
  unfold tailWord_311446
  simp only [CollatzResearch.WordTrace]
  refine ⟨709960551855737974198637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7572912553127871724785461 709960551855737974198637)
  ·
    refine ⟨266235206945901740324489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 709960551855737974198637 266235206945901740324489)
    ·
      refine ⟨199676405209426305243367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266235206945901740324489 199676405209426305243367)
      ·
        refine ⟨299514607814139457865051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199676405209426305243367 299514607814139457865051)
        ·
          refine ⟨449271911721209186797577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299514607814139457865051 449271911721209186797577)
          ·
            refine ⟨336953933790906890098183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449271911721209186797577 336953933790906890098183)
            ·
              refine ⟨505430900686360335147275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336953933790906890098183 505430900686360335147275)
              ·
                refine ⟨758146351029540502720913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505430900686360335147275 758146351029540502720913)
                ·
                  refine ⟨568609763272155377040685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 758146351029540502720913 568609763272155377040685)
                  ·
                    refine ⟨213228661227058266390257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568609763272155377040685 213228661227058266390257)
                    ·
                      refine ⟨159921495920293699792693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213228661227058266390257 159921495920293699792693)
                      ·
                        rfl

theorem cell23_311446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_311446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311446 prefixEnd_311446 := by exact prefixLift 311446
  have htrace : WordTrace (prefixWord ++ tailWord_311446) baseStart_311446 baseEnd_311446 := by
    simpa [prefixWord, tailWord_311446, baseEnd_311446] using wordTrace_append hprefix tailTrace_311446
  have hstable : (prefixWord ++ tailWord_311446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311446).length < 2 ^ (prefixWord ++ tailWord_311446).sum := by decide
  have hdescent : baseEnd_311446 < baseStart_311446 := by decide
  rcases family_descends (prefixWord ++ tailWord_311446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311467 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_311467 : Nat := 118140960795 + 311467 * 2 ^ 59
def prefixEnd_311467 : Nat := 4983230072969 + 3 ^ 40 * 311467 * 2
def baseEnd_311467 : Nat := 159932279014038117630095

theorem tailTrace_311467 : CollatzResearch.WordTrace tailWord_311467 prefixEnd_311467 159932279014038117630095 := by
  unfold tailWord_311467
  simp only [CollatzResearch.WordTrace]
  refine ⟨11360134762615728173692655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7573423175077152115795103 11360134762615728173692655)
  ·
    refine ⟨17040202143923592260538983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11360134762615728173692655 17040202143923592260538983)
    ·
      refine ⟨25560303215885388390808475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17040202143923592260538983 25560303215885388390808475)
      ·
        refine ⟨38340454823828082586212713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25560303215885388390808475 38340454823828082586212713)
        ·
          refine ⟨28755341117871061939659535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38340454823828082586212713 28755341117871061939659535)
          ·
            refine ⟨43133011676806592909489303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28755341117871061939659535 43133011676806592909489303)
            ·
              refine ⟨64699517515209889364233955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43133011676806592909489303 64699517515209889364233955)
              ·
                refine ⟨97049276272814834046350933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64699517515209889364233955 97049276272814834046350933)
                ·
                  refine ⟨1137296206322048836480675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 97049276272814834046350933 1137296206322048836480675)
                  ·
                    refine ⟨1705944309483073254721013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137296206322048836480675 1705944309483073254721013)
                    ·
                      refine ⟨159932279014038117630095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1705944309483073254721013 159932279014038117630095)
                      ·
                        rfl

theorem cell23_311467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_311467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311467 prefixEnd_311467 := by exact prefixLift 311467
  have htrace : WordTrace (prefixWord ++ tailWord_311467) baseStart_311467 baseEnd_311467 := by
    simpa [prefixWord, tailWord_311467, baseEnd_311467] using wordTrace_append hprefix tailTrace_311467
  have hstable : (prefixWord ++ tailWord_311467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311467).length < 2 ^ (prefixWord ++ tailWord_311467).sum := by decide
  have hdescent : baseEnd_311467 < baseStart_311467 := by decide
  rcases family_descends (prefixWord ++ tailWord_311467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311514 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_311514 : Nat := 118140960795 + 311514 * 2 ^ 59
def prefixEnd_311514 : Nat := 4983230072969 + 3 ^ 40 * 311514 * 2
def baseEnd_311514 : Nat := 159956412604799433742379

theorem tailTrace_311514 : CollatzResearch.WordTrace tailWord_311514 prefixEnd_311514 159956412604799433742379 := by
  unfold tailWord_311514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840462248361363800163399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7574565995630303467102397 2840462248361363800163399)
  ·
    refine ⟨4260693372542045700245099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2840462248361363800163399 4260693372542045700245099)
    ·
      refine ⟨6391040058813068550367649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260693372542045700245099 6391040058813068550367649)
      ·
        refine ⟨4793280044109801412775737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6391040058813068550367649 4793280044109801412775737)
        ·
          refine ⟨3594960033082351059581803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4793280044109801412775737 3594960033082351059581803)
          ·
            refine ⟨5392440049623526589372705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594960033082351059581803 5392440049623526589372705)
            ·
              refine ⟨4044330037217644942029529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392440049623526589372705 4044330037217644942029529)
              ·
                refine ⟨3033247527913233706522147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4044330037217644942029529 3033247527913233706522147)
                ·
                  refine ⟨4549871291869850559783221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033247527913233706522147 4549871291869850559783221)
                  ·
                    refine ⟨426550433612798489979677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4549871291869850559783221 426550433612798489979677)
                    ·
                      refine ⟨159956412604799433742379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426550433612798489979677 159956412604799433742379)
                      ·
                        rfl

theorem cell23_311514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_311514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311514 prefixEnd_311514 := by exact prefixLift 311514
  have htrace : WordTrace (prefixWord ++ tailWord_311514) baseStart_311514 baseEnd_311514 := by
    simpa [prefixWord, tailWord_311514, baseEnd_311514] using wordTrace_append hprefix tailTrace_311514
  have hstable : (prefixWord ++ tailWord_311514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311514).length < 2 ^ (prefixWord ++ tailWord_311514).sum := by decide
  have hdescent : baseEnd_311514 < baseStart_311514 := by decide
  rcases family_descends (prefixWord ++ tailWord_311514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311655 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_311655 : Nat := 118140960795 + 311655 * 2 ^ 59
def prefixEnd_311655 : Nat := 4983230072969 + 3 ^ 40 * 311655 * 2
def baseEnd_311655 : Nat := 160028813377083382079231

theorem tailTrace_311655 : CollatzResearch.WordTrace tailWord_311655 prefixEnd_311655 160028813377083382079231 := by
  unfold tailWord_311655
  simp only [CollatzResearch.WordTrace]
  refine ⟨11366991685934636281536419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7577994457289757521024279 11366991685934636281536419)
  ·
    refine ⟨17050487528901954422304629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11366991685934636281536419 17050487528901954422304629)
    ·
      refine ⟨1598483205834558227091059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17050487528901954422304629 1598483205834558227091059)
      ·
        refine ⟨2397724808751837340636589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598483205834558227091059 2397724808751837340636589)
        ·
          refine ⟨899146803281939002738721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2397724808751837340636589 899146803281939002738721)
          ·
            refine ⟨674360102461454252054041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899146803281939002738721 674360102461454252054041)
            ·
              refine ⟨505770076846090689040531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674360102461454252054041 505770076846090689040531)
              ·
                refine ⟨758655115269136033560797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505770076846090689040531 758655115269136033560797)
                ·
                  refine ⟨284495668225926012585299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758655115269136033560797 284495668225926012585299)
                  ·
                    refine ⟨426743502338889018877949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 284495668225926012585299 426743502338889018877949)
                    ·
                      refine ⟨160028813377083382079231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426743502338889018877949 160028813377083382079231)
                      ·
                        rfl

theorem cell23_311655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_311655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311655 prefixEnd_311655 := by exact prefixLift 311655
  have htrace : WordTrace (prefixWord ++ tailWord_311655) baseStart_311655 baseEnd_311655 := by
    simpa [prefixWord, tailWord_311655, baseEnd_311655] using wordTrace_append hprefix tailTrace_311655
  have hstable : (prefixWord ++ tailWord_311655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311655).length < 2 ^ (prefixWord ++ tailWord_311655).sum := by decide
  have hdescent : baseEnd_311655 < baseStart_311655 := by decide
  rcases family_descends (prefixWord ++ tailWord_311655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311712 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2]
def baseStart_311712 : Nat := 118140960795 + 311712 * 2 ^ 59
def prefixEnd_311712 : Nat := 4983230072969 + 3 ^ 40 * 311712 * 2
def baseEnd_311712 : Nat := 160058081774389659066469

theorem tailTrace_311712 : CollatzResearch.WordTrace tailWord_311712 prefixEnd_311712 160058081774389659066469 := by
  unfold tailWord_311712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684535323364067508180695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7579380431152090010907593 5684535323364067508180695)
  ·
    refine ⟨8526802985046101262271043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5684535323364067508180695 8526802985046101262271043)
    ·
      refine ⟨12790204477569151893406565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8526802985046101262271043 12790204477569151893406565)
      ·
        refine ⟨2398163339544215980013731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12790204477569151893406565 2398163339544215980013731)
        ·
          refine ⟨3597245009316323970020597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398163339544215980013731 3597245009316323970020597)
          ·
            refine ⟨337241719623405372189431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3597245009316323970020597 337241719623405372189431)
            ·
              refine ⟨505862579435108058284147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337241719623405372189431 505862579435108058284147)
              ·
                refine ⟨758793869152662087426221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505862579435108058284147 758793869152662087426221)
                ·
                  refine ⟨284547700932248282784833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758793869152662087426221 284547700932248282784833)
                  ·
                    refine ⟨213410775699186212088625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284547700932248282784833 213410775699186212088625)
                    ·
                      refine ⟨160058081774389659066469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213410775699186212088625 160058081774389659066469)
                      ·
                        rfl

theorem cell23_311712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_311712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311712 prefixEnd_311712 := by exact prefixLift 311712
  have htrace : WordTrace (prefixWord ++ tailWord_311712) baseStart_311712 baseEnd_311712 := by
    simpa [prefixWord, tailWord_311712, baseEnd_311712] using wordTrace_append hprefix tailTrace_311712
  have hstable : (prefixWord ++ tailWord_311712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311712).length < 2 ^ (prefixWord ++ tailWord_311712).sum := by decide
  have hdescent : baseEnd_311712 < baseStart_311712 := by decide
  rcases family_descends (prefixWord ++ tailWord_311712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311768 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_311768 : Nat := 118140960795 + 311768 * 2 ^ 59
def prefixEnd_311768 : Nat := 4983230072969 + 3 ^ 40 * 311768 * 2
def baseEnd_311768 : Nat := 160086836691041439966211

theorem tailTrace_311768 : CollatzResearch.WordTrace tailWord_311768 prefixEnd_311768 160086836691041439966211 := by
  unfold tailWord_311768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685556567262628290199979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7580742089683504386933305 5685556567262628290199979)
  ·
    refine ⟨8528334850893942435299969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5685556567262628290199979 8528334850893942435299969)
    ·
      refine ⟨6396251138170456826474977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8528334850893942435299969 6396251138170456826474977)
      ·
        refine ⟨4797188353627842619856233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6396251138170456826474977 4797188353627842619856233)
        ·
          refine ⟨3597891265220881964892175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4797188353627842619856233 3597891265220881964892175)
          ·
            refine ⟨5396836897831322947338263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597891265220881964892175 5396836897831322947338263)
            ·
              refine ⟨8095255346746984421007395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396836897831322947338263 8095255346746984421007395)
              ·
                refine ⟨12142883020120476631511093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095255346746984421007395 12142883020120476631511093)
                ·
                  refine ⟨1138395283136294684204165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12142883020120476631511093 1138395283136294684204165)
                  ·
                    refine ⟨213449115588055253288281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1138395283136294684204165 213449115588055253288281)
                    ·
                      refine ⟨160086836691041439966211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213449115588055253288281 160086836691041439966211)
                      ·
                        rfl

theorem cell23_311768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_311768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311768 prefixEnd_311768 := by exact prefixLift 311768
  have htrace : WordTrace (prefixWord ++ tailWord_311768) baseStart_311768 baseEnd_311768 := by
    simpa [prefixWord, tailWord_311768, baseEnd_311768] using wordTrace_append hprefix tailTrace_311768
  have hstable : (prefixWord ++ tailWord_311768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311768).length < 2 ^ (prefixWord ++ tailWord_311768).sum := by decide
  have hdescent : baseEnd_311768 < baseStart_311768 := by decide
  rcases family_descends (prefixWord ++ tailWord_311768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311798 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_311798 : Nat := 118140960795 + 311798 * 2 ^ 59
def prefixEnd_311798 : Nat := 4983230072969 + 3 ^ 40 * 311798 * 2
def baseEnd_311798 : Nat := 160102241110676322591073

theorem tailTrace_311798 : CollatzResearch.WordTrace tailWord_311798 prefixEnd_311798 160102241110676322591073 := by
  unfold tailWord_311798
  simp only [CollatzResearch.WordTrace]
  refine ⟨710762957776035731499503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7581471549611047802661365 710762957776035731499503)
  ·
    refine ⟨1066144436664053597249255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 710762957776035731499503 1066144436664053597249255)
    ·
      refine ⟨1599216654996080395873883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066144436664053597249255 1599216654996080395873883)
      ·
        refine ⟨2398824982494120593810825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599216654996080395873883 2398824982494120593810825)
        ·
          refine ⟨1799118736870590445358119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398824982494120593810825 1799118736870590445358119)
          ·
            refine ⟨2698678105305885668037179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799118736870590445358119 2698678105305885668037179)
            ·
              refine ⟨4048017157958828502055769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698678105305885668037179 4048017157958828502055769)
              ·
                refine ⟨3036012868469121376541827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048017157958828502055769 3036012868469121376541827)
                ·
                  refine ⟨4554019302703682064812741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036012868469121376541827 4554019302703682064812741)
                  ·
                    refine ⟨853878619256940387152389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4554019302703682064812741 853878619256940387152389)
                    ·
                      refine ⟨160102241110676322591073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 853878619256940387152389 160102241110676322591073)
                      ·
                        rfl

theorem cell23_311798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_311798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311798 prefixEnd_311798 := by exact prefixLift 311798
  have htrace : WordTrace (prefixWord ++ tailWord_311798) baseStart_311798 baseEnd_311798 := by
    simpa [prefixWord, tailWord_311798, baseEnd_311798] using wordTrace_append hprefix tailTrace_311798
  have hstable : (prefixWord ++ tailWord_311798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311798).length < 2 ^ (prefixWord ++ tailWord_311798).sum := by decide
  have hdescent : baseEnd_311798 < baseStart_311798 := by decide
  rcases family_descends (prefixWord ++ tailWord_311798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311818 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_311818 : Nat := 118140960795 + 311818 * 2 ^ 59
def prefixEnd_311818 : Nat := 4983230072969 + 3 ^ 40 * 311818 * 2
def baseEnd_311818 : Nat := 160112510723766244340981

theorem tailTrace_311818 : CollatzResearch.WordTrace tailWord_311818 prefixEnd_311818 160112510723766244340981 := by
  unfold tailWord_311818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843234196086028779930027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7581957856229410079813405 2843234196086028779930027)
  ·
    refine ⟨4264851294129043169895041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2843234196086028779930027 4264851294129043169895041)
    ·
      refine ⟨3198638470596782377421281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4264851294129043169895041 3198638470596782377421281)
      ·
        refine ⟨2398978852947586783065961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3198638470596782377421281 2398978852947586783065961)
        ·
          refine ⟨1799234139710690087299471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398978852947586783065961 1799234139710690087299471)
          ·
            refine ⟨2698851209566035130949207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799234139710690087299471 2698851209566035130949207)
            ·
              refine ⟨4048276814349052696423811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698851209566035130949207 4048276814349052696423811)
              ·
                refine ⟨6072415221523579044635717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048276814349052696423811 6072415221523579044635717)
                ·
                  refine ⟨1138577854035671070869197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6072415221523579044635717 1138577854035671070869197)
                  ·
                    refine ⟨426966695263376651575949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138577854035671070869197 426966695263376651575949)
                    ·
                      refine ⟨160112510723766244340981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 426966695263376651575949 160112510723766244340981)
                      ·
                        rfl

theorem cell23_311818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_311818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311818 prefixEnd_311818 := by exact prefixLift 311818
  have htrace : WordTrace (prefixWord ++ tailWord_311818) baseStart_311818 baseEnd_311818 := by
    simpa [prefixWord, tailWord_311818, baseEnd_311818] using wordTrace_append hprefix tailTrace_311818
  have hstable : (prefixWord ++ tailWord_311818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311818).length < 2 ^ (prefixWord ++ tailWord_311818).sum := by decide
  have hdescent : baseEnd_311818 < baseStart_311818 := by decide
  rcases family_descends (prefixWord ++ tailWord_311818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311819 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 2, 2, 2]
def baseStart_311819 : Nat := 118140960795 + 311819 * 2 ^ 59
def prefixEnd_311819 : Nat := 4983230072969 + 3 ^ 40 * 311819 * 2
def baseEnd_311819 : Nat := 160113024204420740428477

theorem tailTrace_311819 : CollatzResearch.WordTrace tailWord_311819 prefixEnd_311819 160113024204420740428477 := by
  unfold tailWord_311819
  simp only [CollatzResearch.WordTrace]
  refine ⟨11372973257340492290506511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7581982171560328193671007 11372973257340492290506511)
  ·
    refine ⟨17059459886010738435759767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11372973257340492290506511 17059459886010738435759767)
    ·
      refine ⟨25589189829016107653639651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17059459886010738435759767 25589189829016107653639651)
      ·
        refine ⟨38383784743524161480459477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25589189829016107653639651 38383784743524161480459477)
        ·
          refine ⟨899619954926347534698269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38383784743524161480459477 899619954926347534698269)
          ·
            refine ⟨337357483097380325511851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 899619954926347534698269 337357483097380325511851)
            ·
              refine ⟨506036224646070488267777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337357483097380325511851 506036224646070488267777)
              ·
                refine ⟨379527168484552866200833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506036224646070488267777 379527168484552866200833)
                ·
                  refine ⟨284645376363414649650625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379527168484552866200833 284645376363414649650625)
                  ·
                    refine ⟨213484032272560987237969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284645376363414649650625 213484032272560987237969)
                    ·
                      refine ⟨160113024204420740428477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213484032272560987237969 160113024204420740428477)
                      ·
                        rfl

theorem cell23_311819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2, 2].length) (baseStart_311819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311819 prefixEnd_311819 := by exact prefixLift 311819
  have htrace : WordTrace (prefixWord ++ tailWord_311819) baseStart_311819 baseEnd_311819 := by
    simpa [prefixWord, tailWord_311819, baseEnd_311819] using wordTrace_append hprefix tailTrace_311819
  have hstable : (prefixWord ++ tailWord_311819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311819).length < 2 ^ (prefixWord ++ tailWord_311819).sum := by decide
  have hdescent : baseEnd_311819 < baseStart_311819 := by decide
  rcases family_descends (prefixWord ++ tailWord_311819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311858 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_311858 : Nat := 118140960795 + 311858 * 2 ^ 59
def prefixEnd_311858 : Nat := 4983230072969 + 3 ^ 40 * 311858 * 2
def baseEnd_311858 : Nat := 160133049949946087840797

theorem tailTrace_311858 : CollatzResearch.WordTrace tailWord_311858 prefixEnd_311858 160133049949946087840797 := by
  unfold tailWord_311858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843598926049800487794057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7582930469466134634117485 2843598926049800487794057)
  ·
    refine ⟨2132699194537350365845543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2843598926049800487794057 2132699194537350365845543)
    ·
      refine ⟨3199048791806025548768315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2132699194537350365845543 3199048791806025548768315)
      ·
        refine ⟨4798573187709038323152473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199048791806025548768315 4798573187709038323152473)
        ·
          refine ⟨3598929890781778742364355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4798573187709038323152473 3598929890781778742364355)
          ·
            refine ⟨5398394836172668113546533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598929890781778742364355 5398394836172668113546533)
            ·
              refine ⟨1012199031782375271289975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5398394836172668113546533 1012199031782375271289975)
              ·
                refine ⟨1518298547673562906934963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012199031782375271289975 1518298547673562906934963)
                ·
                  refine ⟨2277447821510344360402445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518298547673562906934963 2277447821510344360402445)
                  ·
                    refine ⟨854042933066379135150917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277447821510344360402445 854042933066379135150917)
                    ·
                      refine ⟨160133049949946087840797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 854042933066379135150917 160133049949946087840797)
                      ·
                        rfl

theorem cell23_311858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_311858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311858 prefixEnd_311858 := by exact prefixLift 311858
  have htrace : WordTrace (prefixWord ++ tailWord_311858) baseStart_311858 baseEnd_311858 := by
    simpa [prefixWord, tailWord_311858, baseEnd_311858] using wordTrace_append hprefix tailTrace_311858
  have hstable : (prefixWord ++ tailWord_311858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311858).length < 2 ^ (prefixWord ++ tailWord_311858).sum := by decide
  have hdescent : baseEnd_311858 < baseStart_311858 := by decide
  rcases family_descends (prefixWord ++ tailWord_311858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311876 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 7]
def baseStart_311876 : Nat := 118140960795 + 311876 * 2 ^ 59
def prefixEnd_311876 : Nat := 4983230072969 + 3 ^ 40 * 311876 * 2
def baseEnd_311876 : Nat := 17793588066858557490635

theorem tailTrace_311876 : CollatzResearch.WordTrace tailWord_311876 prefixEnd_311876 17793588066858557490635 := by
  unfold tailWord_311876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687526109066995512665741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7583368145422660683554321 5687526109066995512665741)
  ·
    refine ⟨2132822290900123317249653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5687526109066995512665741 2132822290900123317249653)
    ·
      refine ⟨199952089771886560992155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2132822290900123317249653 199952089771886560992155)
      ·
        refine ⟨299928134657829841488233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199952089771886560992155 299928134657829841488233)
        ·
          refine ⟨224946100993372381116175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299928134657829841488233 224946100993372381116175)
          ·
            refine ⟨337419151490058571674263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224946100993372381116175 337419151490058571674263)
            ·
              refine ⟨506128727235087857511395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337419151490058571674263 506128727235087857511395)
              ·
                refine ⟨759193090852631786267093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506128727235087857511395 759193090852631786267093)
                ·
                  refine ⟨17793588066858557490635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 759193090852631786267093 17793588066858557490635)
                  ·
                    rfl

theorem cell23_311876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_311876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311876 prefixEnd_311876 := by exact prefixLift 311876
  have htrace : WordTrace (prefixWord ++ tailWord_311876) baseStart_311876 baseEnd_311876 := by
    simpa [prefixWord, tailWord_311876, baseEnd_311876] using wordTrace_append hprefix tailTrace_311876
  have hstable : (prefixWord ++ tailWord_311876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311876).length < 2 ^ (prefixWord ++ tailWord_311876).sum := by decide
  have hdescent : baseEnd_311876 < baseStart_311876 := by decide
  rcases family_descends (prefixWord ++ tailWord_311876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311935 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 4, 3, 2]
def baseStart_311935 : Nat := 118140960795 + 311935 * 2 ^ 59
def prefixEnd_311935 : Nat := 4983230072969 + 3 ^ 40 * 311935 * 2
def baseEnd_311935 : Nat := 160172587960342286577943

theorem tailTrace_311935 : CollatzResearch.WordTrace tailWord_311935 prefixEnd_311935 160172587960342286577943 := by
  unfold tailWord_311935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377204124920244101729259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7584802749946829401152839 11377204124920244101729259)
  ·
    refine ⟨17065806187380366152593889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11377204124920244101729259 17065806187380366152593889)
    ·
      refine ⟨12799354640535274614445417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17065806187380366152593889 12799354640535274614445417)
      ·
        refine ⟨9599515980401455960834063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12799354640535274614445417 9599515980401455960834063)
        ·
          refine ⟨14399273970602183941251095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9599515980401455960834063 14399273970602183941251095)
          ·
            refine ⟨21598910955903275911876643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14399273970602183941251095 21598910955903275911876643)
            ·
              refine ⟨32398366433854913867814965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21598910955903275911876643 32398366433854913867814965)
              ·
                refine ⟨3037346853173898175107653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32398366433854913867814965 3037346853173898175107653)
                ·
                  refine ⟨569502534970105907832685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3037346853173898175107653 569502534970105907832685)
                  ·
                    refine ⟨213563450613789715437257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569502534970105907832685 213563450613789715437257)
                    ·
                      refine ⟨160172587960342286577943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213563450613789715437257 160172587960342286577943)
                      ·
                        rfl

theorem cell23_311935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_311935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311935 prefixEnd_311935 := by exact prefixLift 311935
  have htrace : WordTrace (prefixWord ++ tailWord_311935) baseStart_311935 baseEnd_311935 := by
    simpa [prefixWord, tailWord_311935, baseEnd_311935] using wordTrace_append hprefix tailTrace_311935
  have hstable : (prefixWord ++ tailWord_311935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311935).length < 2 ^ (prefixWord ++ tailWord_311935).sum := by decide
  have hdescent : baseEnd_311935 < baseStart_311935 := by decide
  rcases family_descends (prefixWord ++ tailWord_311935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311965 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_311965 : Nat := 118140960795 + 311965 * 2 ^ 59
def prefixEnd_311965 : Nat := 4983230072969 + 3 ^ 40 * 311965 * 2
def baseEnd_311965 : Nat := 160187992379977169202805

theorem tailTrace_311965 : CollatzResearch.WordTrace tailWord_311965 prefixEnd_311965 160187992379977169202805 := by
  unfold tailWord_311965
  simp only [CollatzResearch.WordTrace]
  refine ⟨11378298314811559225321349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7585532209874372816880899 11378298314811559225321349)
  ·
    refine ⟨2133430934027167354747753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11378298314811559225321349 2133430934027167354747753)
    ·
      refine ⟨1600073200520375516060815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2133430934027167354747753 1600073200520375516060815)
      ·
        refine ⟨2400109800780563274091223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600073200520375516060815 2400109800780563274091223)
        ·
          refine ⟨3600164701170844911136835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400109800780563274091223 3600164701170844911136835)
          ·
            refine ⟨5400247051756267366705253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600164701170844911136835 5400247051756267366705253)
            ·
              refine ⟨1012546322204300131257235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5400247051756267366705253 1012546322204300131257235)
              ·
                refine ⟨1518819483306450196885853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012546322204300131257235 1518819483306450196885853)
                ·
                  refine ⟨569557306239918823832195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1518819483306450196885853 569557306239918823832195)
                  ·
                    refine ⟨854335959359878235748293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 569557306239918823832195 854335959359878235748293)
                    ·
                      refine ⟨160187992379977169202805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 854335959359878235748293 160187992379977169202805)
                      ·
                        rfl

theorem cell23_311965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_311965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311965 prefixEnd_311965 := by exact prefixLift 311965
  have htrace : WordTrace (prefixWord ++ tailWord_311965) baseStart_311965 baseEnd_311965 := by
    simpa [prefixWord, tailWord_311965, baseEnd_311965] using wordTrace_append hprefix tailTrace_311965
  have hstable : (prefixWord ++ tailWord_311965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311965).length < 2 ^ (prefixWord ++ tailWord_311965).sum := by decide
  have hdescent : baseEnd_311965 < baseStart_311965 := by decide
  rcases family_descends (prefixWord ++ tailWord_311965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311999 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 3, 2, 2]
def baseStart_311999 : Nat := 118140960795 + 311999 * 2 ^ 59
def prefixEnd_311999 : Nat := 4983230072969 + 3 ^ 40 * 311999 * 2
def baseEnd_311999 : Nat := 160205450722230036177649

theorem tailTrace_311999 : CollatzResearch.WordTrace tailWord_311999 prefixEnd_311999 160205450722230036177649 := by
  unfold tailWord_311999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11379538396688383032059051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7586358931125588688039367 11379538396688383032059051)
  ·
    refine ⟨17069307595032574548088577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11379538396688383032059051 17069307595032574548088577)
    ·
      refine ⟨12801980696274430911066433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17069307595032574548088577 12801980696274430911066433)
      ·
        refine ⟨9601485522205823183299825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12801980696274430911066433 9601485522205823183299825)
        ·
          refine ⟨7201114141654367387474869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9601485522205823183299825 7201114141654367387474869)
          ·
            refine ⟨675104450780096942575769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7201114141654367387474869 675104450780096942575769)
            ·
              refine ⟨506328338085072706931827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675104450780096942575769 506328338085072706931827)
              ·
                refine ⟨759492507127609060397741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506328338085072706931827 759492507127609060397741)
                ·
                  refine ⟨284809690172853397649153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759492507127609060397741 284809690172853397649153)
                  ·
                    refine ⟨213607267629640048236865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284809690172853397649153 213607267629640048236865)
                    ·
                      refine ⟨160205450722230036177649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213607267629640048236865 160205450722230036177649)
                      ·
                        rfl

theorem cell23_311999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_311999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_311999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_311999 prefixEnd_311999 := by exact prefixLift 311999
  have htrace : WordTrace (prefixWord ++ tailWord_311999) baseStart_311999 baseEnd_311999 := by
    simpa [prefixWord, tailWord_311999, baseEnd_311999] using wordTrace_append hprefix tailTrace_311999
  have hstable : (prefixWord ++ tailWord_311999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311999).length < 2 ^ (prefixWord ++ tailWord_311999).sum := by decide
  have hdescent : baseEnd_311999 < baseStart_311999 := by decide
  rcases family_descends (prefixWord ++ tailWord_311999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312012 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_312012 : Nat := 118140960795 + 312012 * 2 ^ 59
def prefixEnd_312012 : Nat := 4983230072969 + 3 ^ 40 * 312012 * 2
def baseEnd_312012 : Nat := 160212125970738485315089

theorem tailTrace_312012 : CollatzResearch.WordTrace tailWord_312012 prefixEnd_312012 160212125970738485315089 := by
  unfold tailWord_312012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690006272820643126141145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7586675030427524168188193 5690006272820643126141145)
  ·
    refine ⟨4267504704615482344605859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5690006272820643126141145 4267504704615482344605859)
    ·
      refine ⟨6401257056923223516908789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267504704615482344605859 6401257056923223516908789)
      ·
        refine ⟨600117849086552204710199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6401257056923223516908789 600117849086552204710199)
        ·
          refine ⟨900176773629828307065299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600117849086552204710199 900176773629828307065299)
          ·
            refine ⟨1350265160444742460597949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900176773629828307065299 1350265160444742460597949)
            ·
              refine ⟨506349435166778422724231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1350265160444742460597949 506349435166778422724231)
              ·
                refine ⟨759524152750167634086347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506349435166778422724231 759524152750167634086347)
                ·
                  refine ⟨1139286229125251451129521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759524152750167634086347 1139286229125251451129521)
                  ·
                    refine ⟨854464671843938588347141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139286229125251451129521 854464671843938588347141)
                    ·
                      refine ⟨160212125970738485315089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 854464671843938588347141 160212125970738485315089)
                      ·
                        rfl

theorem cell23_312012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_312012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312012 prefixEnd_312012 := by exact prefixLift 312012
  have htrace : WordTrace (prefixWord ++ tailWord_312012) baseStart_312012 baseEnd_312012 := by
    simpa [prefixWord, tailWord_312012, baseEnd_312012] using wordTrace_append hprefix tailTrace_312012
  have hstable : (prefixWord ++ tailWord_312012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312012).length < 2 ^ (prefixWord ++ tailWord_312012).sum := by decide
  have hdescent : baseEnd_312012 < baseStart_312012 := by decide
  rcases family_descends (prefixWord ++ tailWord_312012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312033 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_312033 : Nat := 118140960795 + 312033 * 2 ^ 59
def prefixEnd_312033 : Nat := 4983230072969 + 3 ^ 40 * 312033 * 2
def baseEnd_312033 : Nat := 160222909064482903152493

theorem tailTrace_312033 : CollatzResearch.WordTrace tailWord_312033 prefixEnd_312033 160222909064482903152493 := by
  unfold tailWord_312033
  simp only [CollatzResearch.WordTrace]
  refine ⟨11380778478565206838796753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7587185652376804559197835 11380778478565206838796753)
  ·
    refine ⟨8535583858923905129097565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11380778478565206838796753 8535583858923905129097565)
    ·
      refine ⟨3200843947096464423411587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8535583858923905129097565 3200843947096464423411587)
      ·
        refine ⟨4801265920644696635117381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200843947096464423411587 4801265920644696635117381)
        ·
          refine ⟨900237360120880619084509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4801265920644696635117381 900237360120880619084509)
          ·
            refine ⟨337589010045330232156691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 900237360120880619084509 337589010045330232156691)
            ·
              refine ⟨506383515067995348235037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337589010045330232156691 506383515067995348235037)
              ·
                refine ⟨189893818150498255588139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506383515067995348235037 189893818150498255588139)
                ·
                  refine ⟨284840727225747383382209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189893818150498255588139 284840727225747383382209)
                  ·
                    refine ⟨213630545419310537536657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284840727225747383382209 213630545419310537536657)
                    ·
                      refine ⟨160222909064482903152493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213630545419310537536657 160222909064482903152493)
                      ·
                        rfl

theorem cell23_312033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_312033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312033 prefixEnd_312033 := by exact prefixLift 312033
  have htrace : WordTrace (prefixWord ++ tailWord_312033) baseStart_312033 baseEnd_312033 := by
    simpa [prefixWord, tailWord_312033, baseEnd_312033] using wordTrace_append hprefix tailTrace_312033
  have hstable : (prefixWord ++ tailWord_312033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312033).length < 2 ^ (prefixWord ++ tailWord_312033).sum := by decide
  have hdescent : baseEnd_312033 < baseStart_312033 := by decide
  rcases family_descends (prefixWord ++ tailWord_312033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312042 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_312042 : Nat := 118140960795 + 312042 * 2 ^ 59
def prefixEnd_312042 : Nat := 4983230072969 + 3 ^ 40 * 312042 * 2
def baseEnd_312042 : Nat := 160227530390373367939951

theorem tailTrace_312042 : CollatzResearch.WordTrace tailWord_312042 prefixEnd_312042 160227530390373367939951 := by
  unfold tailWord_312042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845276683883150343968595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7587404490355067583916253 2845276683883150343968595)
  ·
    refine ⟨4267915025824725515952893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845276683883150343968595 4267915025824725515952893)
    ·
      refine ⟨1600468134684272068482335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4267915025824725515952893 1600468134684272068482335)
      ·
        refine ⟨2400702202026408102723503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600468134684272068482335 2400702202026408102723503)
        ·
          refine ⟨3601053303039612154085255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400702202026408102723503 3601053303039612154085255)
          ·
            refine ⟨5401579954559418231127883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601053303039612154085255 5401579954559418231127883)
            ·
              refine ⟨8102369931839127346691825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401579954559418231127883 8102369931839127346691825)
              ·
                refine ⟨6076777448879345510018869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8102369931839127346691825 6076777448879345510018869)
                ·
                  refine ⟨569697885832438641564269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6076777448879345510018869 569697885832438641564269)
                  ·
                    refine ⟨213636707187164490586601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569697885832438641564269 213636707187164490586601)
                    ·
                      refine ⟨160227530390373367939951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213636707187164490586601 160227530390373367939951)
                      ·
                        rfl

theorem cell23_312042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_312042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312042 prefixEnd_312042 := by exact prefixLift 312042
  have htrace : WordTrace (prefixWord ++ tailWord_312042) baseStart_312042 baseEnd_312042 := by
    simpa [prefixWord, tailWord_312042, baseEnd_312042] using wordTrace_append hprefix tailTrace_312042
  have hstable : (prefixWord ++ tailWord_312042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312042).length < 2 ^ (prefixWord ++ tailWord_312042).sum := by decide
  have hdescent : baseEnd_312042 < baseStart_312042 := by decide
  rcases family_descends (prefixWord ++ tailWord_312042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312045 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_312045 : Nat := 118140960795 + 312045 * 2 ^ 59
def prefixEnd_312045 : Nat := 4983230072969 + 3 ^ 40 * 312045 * 2
def baseEnd_312045 : Nat := 160229070832336856202437

theorem tailTrace_312045 : CollatzResearch.WordTrace tailWord_312045 prefixEnd_312045 160229070832336856202437 := by
  unfold tailWord_312045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11381216154521732888233589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7587477436347821925489059 11381216154521732888233589)
  ·
    refine ⟨1066989014486412458271899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11381216154521732888233589 1066989014486412458271899)
    ·
      refine ⟨1600483521729618687407849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066989014486412458271899 1600483521729618687407849)
      ·
        refine ⟨1200362641297214015555887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1600483521729618687407849 1200362641297214015555887)
        ·
          refine ⟨1800543961945821023333831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200362641297214015555887 1800543961945821023333831)
          ·
            refine ⟨2700815942918731535000747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800543961945821023333831 2700815942918731535000747)
            ·
              refine ⟨4051223914378097302501121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700815942918731535000747 4051223914378097302501121)
              ·
                refine ⟨3038417935783572976875841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4051223914378097302501121 3038417935783572976875841)
                ·
                  refine ⟨2278813451837679732656881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038417935783572976875841 2278813451837679732656881)
                  ·
                    refine ⟨1709110088878259799492661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278813451837679732656881 1709110088878259799492661)
                    ·
                      refine ⟨160229070832336856202437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1709110088878259799492661 160229070832336856202437)
                      ·
                        rfl

theorem cell23_312045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_312045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312045 prefixEnd_312045 := by exact prefixLift 312045
  have htrace : WordTrace (prefixWord ++ tailWord_312045) baseStart_312045 baseEnd_312045 := by
    simpa [prefixWord, tailWord_312045, baseEnd_312045] using wordTrace_append hprefix tailTrace_312045
  have hstable : (prefixWord ++ tailWord_312045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312045).length < 2 ^ (prefixWord ++ tailWord_312045).sum := by decide
  have hdescent : baseEnd_312045 < baseStart_312045 := by decide
  rcases family_descends (prefixWord ++ tailWord_312045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312066 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_312066 : Nat := 118140960795 + 312066 * 2 ^ 59
def prefixEnd_312066 : Nat := 4983230072969 + 3 ^ 40 * 312066 * 2
def baseEnd_312066 : Nat := 160239853926081274039841

theorem tailTrace_312066 : CollatzResearch.WordTrace tailWord_312066 prefixEnd_312066 160239853926081274039841 := by
  unfold tailWord_312066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845495521861413368687013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7587988058297102316498701 2845495521861413368687013)
  ·
    refine ⟨533530410349015006628815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2845495521861413368687013 533530410349015006628815)
    ·
      refine ⟨800295615523522509943223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533530410349015006628815 800295615523522509943223)
      ·
        refine ⟨1200443423285283764914835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800295615523522509943223 1200443423285283764914835)
        ·
          refine ⟨1800665134927925647372253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200443423285283764914835 1800665134927925647372253)
          ·
            refine ⟨675249425597972117764595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1800665134927925647372253 675249425597972117764595)
            ·
              refine ⟨1012874138396958176646893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675249425597972117764595 1012874138396958176646893)
              ·
                refine ⟨379827801898859316242585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1012874138396958176646893 379827801898859316242585)
                ·
                  refine ⟨284870851424144487181939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379827801898859316242585 284870851424144487181939)
                  ·
                    refine ⟨427306277136216730772909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 284870851424144487181939 427306277136216730772909)
                    ·
                      refine ⟨160239853926081274039841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 427306277136216730772909 160239853926081274039841)
                      ·
                        rfl

theorem cell23_312066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_312066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312066 prefixEnd_312066 := by exact prefixLift 312066
  have htrace : WordTrace (prefixWord ++ tailWord_312066) baseStart_312066 baseEnd_312066 := by
    simpa [prefixWord, tailWord_312066, baseEnd_312066] using wordTrace_append hprefix tailTrace_312066
  have hstable : (prefixWord ++ tailWord_312066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312066).length < 2 ^ (prefixWord ++ tailWord_312066).sum := by decide
  have hdescent : baseEnd_312066 < baseStart_312066 := by decide
  rcases family_descends (prefixWord ++ tailWord_312066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_312105 : Nat := 118140960795 + 312105 * 2 ^ 59
def prefixEnd_312105 : Nat := 4983230072969 + 3 ^ 40 * 312105 * 2
def baseEnd_312105 : Nat := 160259879671606621452161

theorem tailTrace_312105 : CollatzResearch.WordTrace tailWord_312105 prefixEnd_312105 160259879671606621452161 := by
  unfold tailWord_312105
  simp only [CollatzResearch.WordTrace]
  refine ⟨11383404534304363135417769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7588936356202908756945179 11383404534304363135417769)
  ·
    refine ⟨8537553400728272351563327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11383404534304363135417769 8537553400728272351563327)
    ·
      refine ⟨12806330101092408527344991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8537553400728272351563327 12806330101092408527344991)
      ·
        refine ⟨19209495151638612791017487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12806330101092408527344991 19209495151638612791017487)
        ·
          refine ⟨28814242727457919186526231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19209495151638612791017487 28814242727457919186526231)
          ·
            refine ⟨43221364091186878779789347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28814242727457919186526231 43221364091186878779789347)
            ·
              refine ⟨64832046136780318169684021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43221364091186878779789347 64832046136780318169684021)
              ·
                refine ⟨6078004325323154828407877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64832046136780318169684021 6078004325323154828407877)
                ·
                  refine ⟨1139625810998091530326477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6078004325323154828407877 1139625810998091530326477)
                  ·
                    refine ⟨427359679124284323872429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1139625810998091530326477 427359679124284323872429)
                    ·
                      refine ⟨160259879671606621452161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 427359679124284323872429 160259879671606621452161)
                      ·
                        rfl

theorem cell23_312105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_312105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312105 prefixEnd_312105 := by exact prefixLift 312105
  have htrace : WordTrace (prefixWord ++ tailWord_312105) baseStart_312105 baseEnd_312105 := by
    simpa [prefixWord, tailWord_312105, baseEnd_312105] using wordTrace_append hprefix tailTrace_312105
  have hstable : (prefixWord ++ tailWord_312105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312105).length < 2 ^ (prefixWord ++ tailWord_312105).sum := by decide
  have hdescent : baseEnd_312105 < baseStart_312105 := by decide
  rcases family_descends (prefixWord ++ tailWord_312105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312129 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 7]
def baseStart_312129 : Nat := 118140960795 + 312129 * 2 ^ 59
def prefixEnd_312129 : Nat := 4983230072969 + 3 ^ 40 * 312129 * 2
def baseEnd_312129 : Nat := 17808022578590503061339

theorem tailTrace_312129 : CollatzResearch.WordTrace tailWord_312129 prefixEnd_312129 17808022578590503061339 := by
  unfold tailWord_312129
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384279886217415234291441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7589519924144943489527627 11384279886217415234291441)
  ·
    refine ⟨8538209914663061425718581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11384279886217415234291441 8538209914663061425718581)
    ·
      refine ⟨800457179499662008661117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8538209914663061425718581 800457179499662008661117)
      ·
        refine ⟨300171442312373253247919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 800457179499662008661117 300171442312373253247919)
        ·
          refine ⟨450257163468559879871879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300171442312373253247919 450257163468559879871879)
          ·
            refine ⟨675385745202839819807819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450257163468559879871879 675385745202839819807819)
            ·
              refine ⟨1013078617804259729711729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675385745202839819807819 1013078617804259729711729)
              ·
                refine ⟨759808963353194797283797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013078617804259729711729 759808963353194797283797)
                ·
                  refine ⟨17808022578590503061339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 759808963353194797283797 17808022578590503061339)
                  ·
                    rfl

theorem cell23_312129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_312129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312129 prefixEnd_312129 := by exact prefixLift 312129
  have htrace : WordTrace (prefixWord ++ tailWord_312129) baseStart_312129 baseEnd_312129 := by
    simpa [prefixWord, tailWord_312129, baseEnd_312129] using wordTrace_append hprefix tailTrace_312129
  have hstable : (prefixWord ++ tailWord_312129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312129).length < 2 ^ (prefixWord ++ tailWord_312129).sum := by decide
  have hdescent : baseEnd_312129 < baseStart_312129 := by decide
  rcases family_descends (prefixWord ++ tailWord_312129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312165 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_312165 : Nat := 118140960795 + 312165 * 2 ^ 59
def prefixEnd_312165 : Nat := 4983230072969 + 3 ^ 40 * 312165 * 2
def baseEnd_312165 : Nat := 160290688510876386701885

theorem tailTrace_312165 : CollatzResearch.WordTrace tailWord_312165 prefixEnd_312165 160290688510876386701885 := by
  unfold tailWord_312165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11385592914086993382601949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7590395276057995588401299 11385592914086993382601949)
  ·
    refine ⟨4269597342782622518475731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11385592914086993382601949 4269597342782622518475731)
    ·
      refine ⟨6404396014173933777713597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4269597342782622518475731 6404396014173933777713597)
      ·
        refine ⟨2401648505315225166642599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6404396014173933777713597 2401648505315225166642599)
        ·
          refine ⟨3602472757972837749963899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401648505315225166642599 3602472757972837749963899)
          ·
            refine ⟨5403709136959256624945849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602472757972837749963899 5403709136959256624945849)
            ·
              refine ⟨4052781852719442468709387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403709136959256624945849 4052781852719442468709387)
              ·
                refine ⟨6079172779079163703064081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052781852719442468709387 6079172779079163703064081)
                ·
                  refine ⟨4559379584309372777298061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079172779079163703064081 4559379584309372777298061)
                  ·
                    refine ⟨1709767344116014791486773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4559379584309372777298061 1709767344116014791486773)
                    ·
                      refine ⟨160290688510876386701885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1709767344116014791486773 160290688510876386701885)
                      ·
                        rfl

theorem cell23_312165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_312165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312165 prefixEnd_312165 := by exact prefixLift 312165
  have htrace : WordTrace (prefixWord ++ tailWord_312165) baseStart_312165 baseEnd_312165 := by
    simpa [prefixWord, tailWord_312165, baseEnd_312165] using wordTrace_append hprefix tailTrace_312165
  have hstable : (prefixWord ++ tailWord_312165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312165).length < 2 ^ (prefixWord ++ tailWord_312165).sum := by decide
  have hdescent : baseEnd_312165 < baseStart_312165 := by decide
  rcases family_descends (prefixWord ++ tailWord_312165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312202 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_312202 : Nat := 118140960795 + 312202 * 2 ^ 59
def prefixEnd_312202 : Nat := 4983230072969 + 3 ^ 40 * 312202 * 2
def baseEnd_312202 : Nat := 17812187477232526882135

theorem tailTrace_312202 : CollatzResearch.WordTrace tailWord_312202 prefixEnd_312202 17812187477232526882135 := by
  unfold tailWord_312202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846735603738237175424715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7591294943301965801132573 2846735603738237175424715)
  ·
    refine ⟨4270103405607355763137073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2846735603738237175424715 4270103405607355763137073)
    ·
      refine ⟨3202577554205516822352805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4270103405607355763137073 3202577554205516822352805)
      ·
        refine ⟨600483291413534404191151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3202577554205516822352805 600483291413534404191151)
        ·
          refine ⟨900724937120301606286727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600483291413534404191151 900724937120301606286727)
          ·
            refine ⟨1351087405680452409430091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900724937120301606286727 1351087405680452409430091)
            ·
              refine ⟨2026631108520678614145137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351087405680452409430091 2026631108520678614145137)
              ·
                refine ⟨1519973331390508960608853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026631108520678614145137 1519973331390508960608853)
                ·
                  refine ⟨17812187477232526882135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1519973331390508960608853 17812187477232526882135)
                  ·
                    rfl

theorem cell23_312202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_312202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312202 prefixEnd_312202 := by exact prefixLift 312202
  have htrace : WordTrace (prefixWord ++ tailWord_312202) baseStart_312202 baseEnd_312202 := by
    simpa [prefixWord, tailWord_312202, baseEnd_312202] using wordTrace_append hprefix tailTrace_312202
  have hstable : (prefixWord ++ tailWord_312202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312202).length < 2 ^ (prefixWord ++ tailWord_312202).sum := by decide
  have hdescent : baseEnd_312202 < baseStart_312202 := by decide
  rcases family_descends (prefixWord ++ tailWord_312202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312223 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 1, 4]
def baseStart_312223 : Nat := 118140960795 + 312223 * 2 ^ 59
def prefixEnd_312223 : Nat := 4983230072969 + 3 ^ 40 * 312223 * 2
def baseEnd_312223 : Nat := 53440156796279053258873

theorem tailTrace_312223 : CollatzResearch.WordTrace tailWord_312223 prefixEnd_312223 53440156796279053258873 := by
  unfold tailWord_312223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11387708347876869288213323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7591805565251246192142215 11387708347876869288213323)
  ·
    refine ⟨17081562521815303932319985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11387708347876869288213323 17081562521815303932319985)
    ·
      refine ⟨12811171891361477949239989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17081562521815303932319985 12811171891361477949239989)
      ·
        refine ⟨1201047364815138557741249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12811171891361477949239989 1201047364815138557741249)
        ·
          refine ⟨900785523611353918305937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201047364815138557741249 900785523611353918305937)
          ·
            refine ⟨675589142708515438729453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900785523611353918305937 675589142708515438729453)
            ·
              refine ⟨253345928515693289523545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675589142708515438729453 253345928515693289523545)
              ·
                refine ⟨190009446386769967142659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253345928515693289523545 190009446386769967142659)
                ·
                  refine ⟨285014169580154950713989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190009446386769967142659 285014169580154950713989)
                  ·
                    refine ⟨53440156796279053258873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285014169580154950713989 53440156796279053258873)
                    ·
                      rfl

theorem cell23_312223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 4].length) (baseStart_312223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312223 prefixEnd_312223 := by exact prefixLift 312223
  have htrace : WordTrace (prefixWord ++ tailWord_312223) baseStart_312223 baseEnd_312223 := by
    simpa [prefixWord, tailWord_312223, baseEnd_312223] using wordTrace_append hprefix tailTrace_312223
  have hstable : (prefixWord ++ tailWord_312223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312223).length < 2 ^ (prefixWord ++ tailWord_312223).sum := by decide
  have hdescent : baseEnd_312223 < baseStart_312223 := by decide
  rcases family_descends (prefixWord ++ tailWord_312223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312249 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_312249 : Nat := 118140960795 + 312249 * 2 ^ 59
def prefixEnd_312249 : Nat := 4983230072969 + 3 ^ 40 * 312249 * 2
def baseEnd_312249 : Nat := 53444606961951352683833

theorem tailTrace_312249 : CollatzResearch.WordTrace tailWord_312249 prefixEnd_312249 53444606961951352683833 := by
  unfold tailWord_312249
  simp only [CollatzResearch.WordTrace]
  refine ⟨11388656645782675728659801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7592437763855117152439867 11388656645782675728659801)
  ·
    refine ⟨8541492484337006796494851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11388656645782675728659801 8541492484337006796494851)
    ·
      refine ⟨12812238726505510194742277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541492484337006796494851 12812238726505510194742277)
      ·
        refine ⟨2402294761219783161514177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12812238726505510194742277 2402294761219783161514177)
        ·
          refine ⟨1801721070914837371135633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402294761219783161514177 1801721070914837371135633)
          ·
            refine ⟨1351290803186128028351725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801721070914837371135633 1351290803186128028351725)
            ·
              refine ⟨506734051194798010631897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351290803186128028351725 506734051194798010631897)
              ·
                refine ⟨380050538396098507973923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506734051194798010631897 380050538396098507973923)
                ·
                  refine ⟨570075807594147761960885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380050538396098507973923 570075807594147761960885)
                  ·
                    refine ⟨53444606961951352683833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 570075807594147761960885 53444606961951352683833)
                    ·
                      rfl

theorem cell23_312249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_312249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312249 prefixEnd_312249 := by exact prefixLift 312249
  have htrace : WordTrace (prefixWord ++ tailWord_312249) baseStart_312249 baseEnd_312249 := by
    simpa [prefixWord, tailWord_312249, baseEnd_312249] using wordTrace_append hprefix tailTrace_312249
  have hstable : (prefixWord ++ tailWord_312249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312249).length < 2 ^ (prefixWord ++ tailWord_312249).sum := by decide
  have hdescent : baseEnd_312249 < baseStart_312249 := by decide
  rcases family_descends (prefixWord ++ tailWord_312249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312256 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2]
def baseStart_312256 : Nat := 118140960795 + 312256 * 2 ^ 59
def prefixEnd_312256 : Nat := 4983230072969 + 3 ^ 40 * 312256 * 2
def baseEnd_312256 : Nat := 160337415250435530663967

theorem tailTrace_312256 : CollatzResearch.WordTrace tailWord_312256 prefixEnd_312256 160337415250435530663967 := by
  unfold tailWord_312256
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694455978378657962082311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7592607971171543949443081 5694455978378657962082311)
  ·
    refine ⟨8541683967567986943123467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5694455978378657962082311 8541683967567986943123467)
    ·
      refine ⟨12812525951351980414685201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541683967567986943123467 12812525951351980414685201)
      ·
        refine ⟨9609394463513985311013901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12812525951351980414685201 9609394463513985311013901)
        ·
          refine ⟨3603522923817744491630213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9609394463513985311013901 3603522923817744491630213)
          ·
            refine ⟨675660548215827092180665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3603522923817744491630213 675660548215827092180665)
            ·
              refine ⟨506745411161870319135499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675660548215827092180665 506745411161870319135499)
              ·
                refine ⟨760118116742805478703249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506745411161870319135499 760118116742805478703249)
                ·
                  refine ⟨570088587557104109027437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 760118116742805478703249 570088587557104109027437)
                  ·
                    refine ⟨213783220333914040885289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570088587557104109027437 213783220333914040885289)
                    ·
                      refine ⟨160337415250435530663967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213783220333914040885289 160337415250435530663967)
                      ·
                        rfl

theorem cell23_312256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_312256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312256 prefixEnd_312256 := by exact prefixLift 312256
  have htrace : WordTrace (prefixWord ++ tailWord_312256) baseStart_312256 baseEnd_312256 := by
    simpa [prefixWord, tailWord_312256, baseEnd_312256] using wordTrace_append hprefix tailTrace_312256
  have hstable : (prefixWord ++ tailWord_312256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312256).length < 2 ^ (prefixWord ++ tailWord_312256).sum := by decide
  have hdescent : baseEnd_312256 < baseStart_312256 := by decide
  rcases family_descends (prefixWord ++ tailWord_312256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312280 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 1, 1, 3]
def baseStart_312280 : Nat := 118140960795 + 312280 * 2 ^ 59
def prefixEnd_312280 : Nat := 4983230072969 + 3 ^ 40 * 312280 * 2
def baseEnd_312280 : Nat := 160349738786143436763857

theorem tailTrace_312280 : CollatzResearch.WordTrace tailWord_312280 prefixEnd_312280 160349738786143436763857 := by
  unfold tailWord_312280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694893654335184011519147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7593191539113578682025529 5694893654335184011519147)
  ·
    refine ⟨8542340481502776017278721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5694893654335184011519147 8542340481502776017278721)
    ·
      refine ⟨6406755361127082012959041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8542340481502776017278721 6406755361127082012959041)
      ·
        refine ⟨4805066520845311509719281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6406755361127082012959041 4805066520845311509719281)
        ·
          refine ⟨3603799890633983632289461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4805066520845311509719281 3603799890633983632289461)
          ·
            refine ⟨337856239746935965527137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3603799890633983632289461 337856239746935965527137)
            ·
              refine ⟨253392179810201974145353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337856239746935965527137 253392179810201974145353)
              ·
                refine ⟨190044134857651480609015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253392179810201974145353 190044134857651480609015)
                ·
                  refine ⟨285066202286477220913523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190044134857651480609015 285066202286477220913523)
                  ·
                    refine ⟨427599303429715831370285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285066202286477220913523 427599303429715831370285)
                    ·
                      refine ⟨160349738786143436763857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 427599303429715831370285 160349738786143436763857)
                      ·
                        rfl

theorem cell23_312280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_312280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312280 prefixEnd_312280 := by exact prefixLift 312280
  have htrace : WordTrace (prefixWord ++ tailWord_312280) baseStart_312280 baseEnd_312280 := by
    simpa [prefixWord, tailWord_312280, baseEnd_312280] using wordTrace_append hprefix tailTrace_312280
  have hstable : (prefixWord ++ tailWord_312280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312280).length < 2 ^ (prefixWord ++ tailWord_312280).sum := by decide
  have hdescent : baseEnd_312280 < baseStart_312280 := by decide
  rcases family_descends (prefixWord ++ tailWord_312280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312392 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_312392 : Nat := 118140960795 + 312392 * 2 ^ 59
def prefixEnd_312392 : Nat := 4983230072969 + 3 ^ 40 * 312392 * 2
def baseEnd_312392 : Nat := 160407248619446998563341

theorem tailTrace_312392 : CollatzResearch.WordTrace tailWord_312392 prefixEnd_312392 160407248619446998563341 := by
  unfold tailWord_312392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696936142132305575557715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7595914856176407434076953 5696936142132305575557715)
  ·
    refine ⟨8545404213198458363336573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5696936142132305575557715 8545404213198458363336573)
    ·
      refine ⟨3204526579949421886251215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8545404213198458363336573 3204526579949421886251215)
      ·
        refine ⟨4806789869924132829376823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204526579949421886251215 4806789869924132829376823)
        ·
          refine ⟨7210184804886199244065235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806789869924132829376823 7210184804886199244065235)
          ·
            refine ⟨10815277207329298866097853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210184804886199244065235 10815277207329298866097853)
            ·
              refine ⟨4055728952748487074786695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10815277207329298866097853 4055728952748487074786695)
              ·
                refine ⟨6083593429122730612180043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055728952748487074786695 6083593429122730612180043)
                ·
                  refine ⟨9125390143684095918270065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083593429122730612180043 9125390143684095918270065)
                  ·
                    refine ⟨6844042607763071938702549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9125390143684095918270065 6844042607763071938702549)
                    ·
                      refine ⟨160407248619446998563341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6844042607763071938702549 160407248619446998563341)
                      ·
                        rfl

theorem cell23_312392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_312392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312392 prefixEnd_312392 := by exact prefixLift 312392
  have htrace : WordTrace (prefixWord ++ tailWord_312392) baseStart_312392 baseEnd_312392 := by
    simpa [prefixWord, tailWord_312392, baseEnd_312392] using wordTrace_append hprefix tailTrace_312392
  have hstable : (prefixWord ++ tailWord_312392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312392).length < 2 ^ (prefixWord ++ tailWord_312392).sum := by decide
  have hdescent : baseEnd_312392 < baseStart_312392 := by decide
  rcases family_descends (prefixWord ++ tailWord_312392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312414 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_312414 : Nat := 118140960795 + 312414 * 2 ^ 59
def prefixEnd_312414 : Nat := 4983230072969 + 3 ^ 40 * 312414 * 2
def baseEnd_312414 : Nat := 160418545193845912488241

theorem tailTrace_312414 : CollatzResearch.WordTrace tailWord_312414 prefixEnd_312414 160418545193845912488241 := by
  unfold tailWord_312414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424334336273113613552037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7596449793456605938944197 1424334336273113613552037)
  ·
    refine ⟨267062688051208802541007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1424334336273113613552037 267062688051208802541007)
    ·
      refine ⟨400594032076813203811511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267062688051208802541007 400594032076813203811511)
      ·
        refine ⟨600891048115219805717267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400594032076813203811511 600891048115219805717267)
        ·
          refine ⟨901336572172829708575901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600891048115219805717267 901336572172829708575901)
          ·
            refine ⟨338001214564811140715963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 901336572172829708575901 338001214564811140715963)
            ·
              refine ⟨507001821847216711073945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338001214564811140715963 507001821847216711073945)
              ·
                refine ⟨380251366385412533305459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507001821847216711073945 380251366385412533305459)
                ·
                  refine ⟨570377049578118799958189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380251366385412533305459 570377049578118799958189)
                  ·
                    refine ⟨213891393591794549984321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570377049578118799958189 213891393591794549984321)
                    ·
                      refine ⟨160418545193845912488241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 213891393591794549984321 160418545193845912488241)
                      ·
                        rfl

theorem cell23_312414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_312414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312414 prefixEnd_312414 := by exact prefixLift 312414
  have htrace : WordTrace (prefixWord ++ tailWord_312414) baseStart_312414 baseEnd_312414 := by
    simpa [prefixWord, tailWord_312414, baseEnd_312414] using wordTrace_append hprefix tailTrace_312414
  have hstable : (prefixWord ++ tailWord_312414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312414).length < 2 ^ (prefixWord ++ tailWord_312414).sum := by decide
  have hdescent : baseEnd_312414 < baseStart_312414 := by decide
  rcases family_descends (prefixWord ++ tailWord_312414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312459 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 7, 4]
def baseStart_312459 : Nat := 118140960795 + 312459 * 2 ^ 59
def prefixEnd_312459 : Nat := 4983230072969 + 3 ^ 40 * 312459 * 2
def baseEnd_312459 : Nat := 53480550607766078808511

theorem tailTrace_312459 : CollatzResearch.WordTrace tailWord_312459 prefixEnd_312459 53480550607766078808511 := by
  unfold tailWord_312459
  simp only [CollatzResearch.WordTrace]
  refine ⟨11396315975021881593804431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7597543983347921062536287 11396315975021881593804431)
  ·
    refine ⟨17094473962532822390706647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11396315975021881593804431 17094473962532822390706647)
    ·
      refine ⟨25641710943799233586059971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17094473962532822390706647 25641710943799233586059971)
      ·
        refine ⟨38462566415698850379089957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25641710943799233586059971 38462566415698850379089957)
        ·
          refine ⟨7211731202943534446079367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38462566415698850379089957 7211731202943534446079367)
          ·
            refine ⟨10817596804415301669119051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7211731202943534446079367 10817596804415301669119051)
            ·
              refine ⟨16226395206622952503678577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10817596804415301669119051 16226395206622952503678577)
              ·
                refine ⟨12169796404967214377758933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16226395206622952503678577 12169796404967214377758933)
                ·
                  refine ⟨285229603241419086978725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12169796404967214377758933 285229603241419086978725)
                  ·
                    refine ⟨53480550607766078808511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285229603241419086978725 53480550607766078808511)
                    ·
                      rfl

theorem cell23_312459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 4].length) (baseStart_312459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312459 prefixEnd_312459 := by exact prefixLift 312459
  have htrace : WordTrace (prefixWord ++ tailWord_312459) baseStart_312459 baseEnd_312459 := by
    simpa [prefixWord, tailWord_312459, baseEnd_312459] using wordTrace_append hprefix tailTrace_312459
  have hstable : (prefixWord ++ tailWord_312459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312459).length < 2 ^ (prefixWord ++ tailWord_312459).sum := by decide
  have hdescent : baseEnd_312459 < baseStart_312459 := by decide
  rcases family_descends (prefixWord ++ tailWord_312459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312476 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_312476 : Nat := 118140960795 + 312476 * 2 ^ 59
def prefixEnd_312476 : Nat := 4983230072969 + 3 ^ 40 * 312476 * 2
def baseEnd_312476 : Nat := 53483460331474889970985

theorem tailTrace_312476 : CollatzResearch.WordTrace tailWord_312476 prefixEnd_312476 53483460331474889970985 := by
  unfold tailWord_312476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698468007980146748586641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7597957343973528998115521 5698468007980146748586641)
  ·
    refine ⟨4273851005985110061439981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5698468007980146748586641 4273851005985110061439981)
    ·
      refine ⟨1602694127244416273039993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4273851005985110061439981 1602694127244416273039993)
      ·
        refine ⟨1202020595433312204779995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1602694127244416273039993 1202020595433312204779995)
        ·
          refine ⟨1803030893149968307169993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202020595433312204779995 1803030893149968307169993)
          ·
            refine ⟨1352273169862476230377495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803030893149968307169993 1352273169862476230377495)
            ·
              refine ⟨2028409754793714345566243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352273169862476230377495 2028409754793714345566243)
              ·
                refine ⟨3042614632190571518349365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028409754793714345566243 3042614632190571518349365)
                ·
                  refine ⟨285245121767866079845253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042614632190571518349365 285245121767866079845253)
                  ·
                    refine ⟨53483460331474889970985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285245121767866079845253 53483460331474889970985)
                    ·
                      rfl

theorem cell23_312476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_312476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312476 prefixEnd_312476 := by exact prefixLift 312476
  have htrace : WordTrace (prefixWord ++ tailWord_312476) baseStart_312476 baseEnd_312476 := by
    simpa [prefixWord, tailWord_312476, baseEnd_312476] using wordTrace_append hprefix tailTrace_312476
  have hstable : (prefixWord ++ tailWord_312476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312476).length < 2 ^ (prefixWord ++ tailWord_312476).sum := by decide
  have hdescent : baseEnd_312476 < baseStart_312476 := by decide
  rcases family_descends (prefixWord ++ tailWord_312476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312509 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_312509 : Nat := 118140960795 + 312509 * 2 ^ 59
def prefixEnd_312509 : Nat := 4983230072969 + 3 ^ 40 * 312509 * 2
def baseEnd_312509 : Nat := 160467325856023040800303

theorem tailTrace_312509 : CollatzResearch.WordTrace tailWord_312509 prefixEnd_312509 160467325856023040800303 := by
  unfold tailWord_312509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11398139624840740133124581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7598759749893826755416387 11398139624840740133124581)
  ·
    refine ⟨2137151179657638774960859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11398139624840740133124581 2137151179657638774960859)
    ·
      refine ⟨3205726769486458162441289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137151179657638774960859 3205726769486458162441289)
      ·
        refine ⟨2404295077114843621830967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3205726769486458162441289 2404295077114843621830967)
        ·
          refine ⟨3606442615672265432746451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404295077114843621830967 3606442615672265432746451)
          ·
            refine ⟨5409663923508398149119677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606442615672265432746451 5409663923508398149119677)
            ·
              refine ⟨2028623971315649305919879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5409663923508398149119677 2028623971315649305919879)
              ·
                refine ⟨3042935956973473958879819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028623971315649305919879 3042935956973473958879819)
                ·
                  refine ⟨4564403935460210938319729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042935956973473958879819 4564403935460210938319729)
                  ·
                    refine ⟨3423302951595158203739797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564403935460210938319729 3423302951595158203739797)
                    ·
                      refine ⟨160467325856023040800303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3423302951595158203739797 160467325856023040800303)
                      ·
                        rfl

theorem cell23_312509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_312509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312509 prefixEnd_312509 := by exact prefixLift 312509
  have htrace : WordTrace (prefixWord ++ tailWord_312509) baseStart_312509 baseEnd_312509 := by
    simpa [prefixWord, tailWord_312509, baseEnd_312509] using wordTrace_append hprefix tailTrace_312509
  have hstable : (prefixWord ++ tailWord_312509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312509).length < 2 ^ (prefixWord ++ tailWord_312509).sum := by decide
  have hdescent : baseEnd_312509 < baseStart_312509 := by decide
  rcases family_descends (prefixWord ++ tailWord_312509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312510 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_312510 : Nat := 118140960795 + 312510 * 2 ^ 59
def prefixEnd_312510 : Nat := 4983230072969 + 3 ^ 40 * 312510 * 2
def baseEnd_312510 : Nat := 53489279778892512295933

theorem tailTrace_312510 : CollatzResearch.WordTrace tailWord_312510 prefixEnd_312510 53489279778892512295933 := by
  unfold tailWord_312510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424772012229639662988873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7598784065224744869273989 1424772012229639662988873)
  ·
    refine ⟨1068579009172229747241655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1424772012229639662988873 1068579009172229747241655)
    ·
      refine ⟨1602868513758344620862483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068579009172229747241655 1602868513758344620862483)
      ·
        refine ⟨2404302770637516931293725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602868513758344620862483 2404302770637516931293725)
        ·
          refine ⟨901613538989068849235147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2404302770637516931293725 901613538989068849235147)
          ·
            refine ⟨1352420308483603273852721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901613538989068849235147 1352420308483603273852721)
            ·
              refine ⟨1014315231362702455389541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352420308483603273852721 1014315231362702455389541)
              ·
                refine ⟨190184105880506710385539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1014315231362702455389541 190184105880506710385539)
                ·
                  refine ⟨285276158820760065578309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190184105880506710385539 285276158820760065578309)
                  ·
                    refine ⟨53489279778892512295933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285276158820760065578309 53489279778892512295933)
                    ·
                      rfl

theorem cell23_312510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_312510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312510 prefixEnd_312510 := by exact prefixLift 312510
  have htrace : WordTrace (prefixWord ++ tailWord_312510) baseStart_312510 baseEnd_312510 := by
    simpa [prefixWord, tailWord_312510, baseEnd_312510] using wordTrace_append hprefix tailTrace_312510
  have hstable : (prefixWord ++ tailWord_312510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312510).length < 2 ^ (prefixWord ++ tailWord_312510).sum := by decide
  have hdescent : baseEnd_312510 < baseStart_312510 := by decide
  rcases family_descends (prefixWord ++ tailWord_312510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312519 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 5, 5]
def baseStart_312519 : Nat := 118140960795 + 312519 * 2 ^ 59
def prefixEnd_312519 : Nat := 4983230072969 + 3 ^ 40 * 312519 * 2
def baseEnd_312519 : Nat := 53490820220856000558419

theorem tailTrace_312519 : CollatzResearch.WordTrace tailWord_312519 prefixEnd_312519 53490820220856000558419 := by
  unfold tailWord_312519
  simp only [CollatzResearch.WordTrace]
  refine ⟨11398504354804511840988611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7599002903203007893992407 11398504354804511840988611)
  ·
    refine ⟨17097756532206767761482917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11398504354804511840988611 17097756532206767761482917)
    ·
      refine ⟨3205829349788768955278047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17097756532206767761482917 3205829349788768955278047)
      ·
        refine ⟨4808744024683153432917071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205829349788768955278047 4808744024683153432917071)
        ·
          refine ⟨7213116037024730149375607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808744024683153432917071 7213116037024730149375607)
          ·
            refine ⟨10819674055537095224063411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7213116037024730149375607 10819674055537095224063411)
            ·
              refine ⟨16229511083305642836095117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819674055537095224063411 16229511083305642836095117)
              ·
                refine ⟨6086066656239616063535669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16229511083305642836095117 6086066656239616063535669)
                ·
                  refine ⟨570568749022464005956469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6086066656239616063535669 570568749022464005956469)
                  ·
                    refine ⟨53490820220856000558419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 570568749022464005956469 53490820220856000558419)
                    ·
                      rfl

theorem cell23_312519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_312519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312519 prefixEnd_312519 := by exact prefixLift 312519
  have htrace : WordTrace (prefixWord ++ tailWord_312519) baseStart_312519 baseEnd_312519 := by
    simpa [prefixWord, tailWord_312519, baseEnd_312519] using wordTrace_append hprefix tailTrace_312519
  have hstable : (prefixWord ++ tailWord_312519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312519).length < 2 ^ (prefixWord ++ tailWord_312519).sum := by decide
  have hdescent : baseEnd_312519 < baseStart_312519 := by decide
  rcases family_descends (prefixWord ++ tailWord_312519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312569 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_312569 : Nat := 118140960795 + 312569 * 2 ^ 59
def prefixEnd_312569 : Nat := 4983230072969 + 3 ^ 40 * 312569 * 2
def baseEnd_312569 : Nat := 160498134695292806050027

theorem tailTrace_312569 : CollatzResearch.WordTrace tailWord_312569 prefixEnd_312569 160498134695292806050027 := by
  unfold tailWord_312569
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400328004623370380308761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7600218669748913586872507 11400328004623370380308761)
  ·
    refine ⟨8550246003467527785231571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11400328004623370380308761 8550246003467527785231571)
    ·
      refine ⟨12825369005201291677847357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8550246003467527785231571 12825369005201291677847357)
      ·
        refine ⟨4809513376950484379192759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12825369005201291677847357 4809513376950484379192759)
        ·
          refine ⟨7214270065425726568789139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809513376950484379192759 7214270065425726568789139)
          ·
            refine ⟨10821405098138589853183709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214270065425726568789139 10821405098138589853183709)
            ·
              refine ⟨4058026911801971194943891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10821405098138589853183709 4058026911801971194943891)
              ·
                refine ⟨6087040367702956792415837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058026911801971194943891 6087040367702956792415837)
                ·
                  refine ⟨2282640137888608797155939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6087040367702956792415837 2282640137888608797155939)
                  ·
                    refine ⟨3423960206832913195733909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2282640137888608797155939 3423960206832913195733909)
                    ·
                      refine ⟨160498134695292806050027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3423960206832913195733909 160498134695292806050027)
                      ·
                        rfl

theorem cell23_312569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_312569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312569 prefixEnd_312569 := by exact prefixLift 312569
  have htrace : WordTrace (prefixWord ++ tailWord_312569) baseStart_312569 baseEnd_312569 := by
    simpa [prefixWord, tailWord_312569, baseEnd_312569] using wordTrace_append hprefix tailTrace_312569
  have hstable : (prefixWord ++ tailWord_312569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312569).length < 2 ^ (prefixWord ++ tailWord_312569).sum := by decide
  have hdescent : baseEnd_312569 < baseStart_312569 := by decide
  rcases family_descends (prefixWord ++ tailWord_312569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312576 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_312576 : Nat := 118140960795 + 312576 * 2 ^ 59
def prefixEnd_312576 : Nat := 4983230072969 + 3 ^ 40 * 312576 * 2
def baseEnd_312576 : Nat := 160501729059874278662495

theorem tailTrace_312576 : CollatzResearch.WordTrace tailWord_312576 prefixEnd_312576 160501729059874278662495 := by
  unfold tailWord_312576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5700291657799005287906791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7600388877065340383875721 5700291657799005287906791)
  ·
    refine ⟨8550437486698507931860187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5700291657799005287906791 8550437486698507931860187)
    ·
      refine ⟨12825656230047761897790281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8550437486698507931860187 12825656230047761897790281)
      ·
        refine ⟨9619242172535821423342711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12825656230047761897790281 9619242172535821423342711)
        ·
          refine ⟨14428863258803732135014067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9619242172535821423342711 14428863258803732135014067)
          ·
            refine ⟨21643294888205598202521101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14428863258803732135014067 21643294888205598202521101)
            ·
              refine ⟨8116235583077099325945413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21643294888205598202521101 8116235583077099325945413)
              ·
                refine ⟨1521794171826956123614765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8116235583077099325945413 1521794171826956123614765)
                ·
                  refine ⟨570672814435108546355537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1521794171826956123614765 570672814435108546355537)
                  ·
                    refine ⟨428004610826331409766653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570672814435108546355537 428004610826331409766653)
                    ·
                      refine ⟨160501729059874278662495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 428004610826331409766653 160501729059874278662495)
                      ·
                        rfl

theorem cell23_312576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_312576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312576 prefixEnd_312576 := by exact prefixLift 312576
  have htrace : WordTrace (prefixWord ++ tailWord_312576) baseStart_312576 baseEnd_312576 := by
    simpa [prefixWord, tailWord_312576, baseEnd_312576] using wordTrace_append hprefix tailTrace_312576
  have hstable : (prefixWord ++ tailWord_312576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312576).length < 2 ^ (prefixWord ++ tailWord_312576).sum := by decide
  have hdescent : baseEnd_312576 < baseStart_312576 := by decide
  rcases family_descends (prefixWord ++ tailWord_312576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312579 : List Nat := [1, 1, 1, 3, 2, 4, 1, 10]
def baseStart_312579 : Nat := 118140960795 + 312579 * 2 ^ 59
def prefixEnd_312579 : Nat := 4983230072969 + 3 ^ 40 * 312579 * 2
def baseEnd_312579 : Nat := 5944565537105102478703

theorem tailTrace_312579 : CollatzResearch.WordTrace tailWord_312579 prefixEnd_312579 5944565537105102478703 := by
  unfold tailWord_312579
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400692734587142088172791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7600461823058094725448527 11400692734587142088172791)
  ·
    refine ⟨17101039101880713132259187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11400692734587142088172791 17101039101880713132259187)
    ·
      refine ⟨25651558652821069698388781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17101039101880713132259187 25651558652821069698388781)
      ·
        refine ⟨9619334494807901136895793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25651558652821069698388781 9619334494807901136895793)
        ·
          refine ⟨7214500871105925852671845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9619334494807901136895793 7214500871105925852671845)
          ·
            refine ⟨1352718913332361097375971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7214500871105925852671845 1352718913332361097375971)
            ·
              refine ⟨2029078369998541646063957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352718913332361097375971 2029078369998541646063957)
              ·
                refine ⟨5944565537105102478703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2029078369998541646063957 5944565537105102478703)
                ·
                  rfl

theorem cell23_312579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 10].length) (baseStart_312579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312579 prefixEnd_312579 := by exact prefixLift 312579
  have htrace : WordTrace (prefixWord ++ tailWord_312579) baseStart_312579 baseEnd_312579 := by
    simpa [prefixWord, tailWord_312579, baseEnd_312579] using wordTrace_append hprefix tailTrace_312579
  have hstable : (prefixWord ++ tailWord_312579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312579).length < 2 ^ (prefixWord ++ tailWord_312579).sum := by decide
  have hdescent : baseEnd_312579 < baseStart_312579 := by decide
  rcases family_descends (prefixWord ++ tailWord_312579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312586 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_312586 : Nat := 118140960795 + 312586 * 2 ^ 59
def prefixEnd_312586 : Nat := 4983230072969 + 3 ^ 40 * 312586 * 2
def baseEnd_312586 : Nat := 160506863866419239537449

theorem tailTrace_312586 : CollatzResearch.WordTrace tailWord_312586 prefixEnd_312586 160506863866419239537449 := by
  unfold tailWord_312586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850237011390445570919403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7600632030374521522451741 2850237011390445570919403)
  ·
    refine ⟨4275355517085668356379105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850237011390445570919403 4275355517085668356379105)
    ·
      refine ⟨3206516637814251267284329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4275355517085668356379105 3206516637814251267284329)
      ·
        refine ⟨2404887478360688450463247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3206516637814251267284329 2404887478360688450463247)
        ·
          refine ⟨3607331217541032675694871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404887478360688450463247 3607331217541032675694871)
          ·
            refine ⟨5410996826311549013542307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607331217541032675694871 5410996826311549013542307)
            ·
              refine ⟨8116495239467323520313461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5410996826311549013542307 8116495239467323520313461)
              ·
                refine ⟨760921428700061580029387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8116495239467323520313461 760921428700061580029387)
                ·
                  refine ⟨1141382143050092370044081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760921428700061580029387 1141382143050092370044081)
                  ·
                    refine ⟨856036607287569277533061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1141382143050092370044081 856036607287569277533061)
                    ·
                      refine ⟨160506863866419239537449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 856036607287569277533061 160506863866419239537449)
                      ·
                        rfl

theorem cell23_312586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_312586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312586 prefixEnd_312586 := by exact prefixLift 312586
  have htrace : WordTrace (prefixWord ++ tailWord_312586) baseStart_312586 baseEnd_312586 := by
    simpa [prefixWord, tailWord_312586, baseEnd_312586] using wordTrace_append hprefix tailTrace_312586
  have hstable : (prefixWord ++ tailWord_312586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312586).length < 2 ^ (prefixWord ++ tailWord_312586).sum := by decide
  have hdescent : baseEnd_312586 < baseStart_312586 := by decide
  rcases family_descends (prefixWord ++ tailWord_312586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312590 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_312590 : Nat := 118140960795 + 312590 * 2 ^ 59
def prefixEnd_312590 : Nat := 4983230072969 + 3 ^ 40 * 312590 * 2
def baseEnd_312590 : Nat := 160508917789037223887431

theorem tailTrace_312590 : CollatzResearch.WordTrace tailWord_312590 prefixEnd_312590 160508917789037223887431 := by
  unfold tailWord_312590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425136742193411370852903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7600729291698193977882149 1425136742193411370852903)
  ·
    refine ⟨2137705113290117056279355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1425136742193411370852903 2137705113290117056279355)
    ·
      refine ⟨3206557669935175584419033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137705113290117056279355 3206557669935175584419033)
      ·
        refine ⟨2404918252451381688314275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3206557669935175584419033 2404918252451381688314275)
        ·
          refine ⟨3607377378677072532471413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404918252451381688314275 3607377378677072532471413)
          ·
            refine ⟨338191629250975549919195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3607377378677072532471413 338191629250975549919195)
            ·
              refine ⟨507287443876463324878793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338191629250975549919195 507287443876463324878793)
              ·
                refine ⟨380465582907347493659095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507287443876463324878793 380465582907347493659095)
                ·
                  refine ⟨570698374361021240488643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380465582907347493659095 570698374361021240488643)
                  ·
                    refine ⟨856047561541531860732965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 570698374361021240488643 856047561541531860732965)
                    ·
                      refine ⟨160508917789037223887431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 856047561541531860732965 160508917789037223887431)
                      ·
                        rfl

theorem cell23_312590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_312590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312590 prefixEnd_312590 := by exact prefixLift 312590
  have htrace : WordTrace (prefixWord ++ tailWord_312590) baseStart_312590 baseEnd_312590 := by
    simpa [prefixWord, tailWord_312590, baseEnd_312590] using wordTrace_append hprefix tailTrace_312590
  have hstable : (prefixWord ++ tailWord_312590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312590).length < 2 ^ (prefixWord ++ tailWord_312590).sum := by decide
  have hdescent : baseEnd_312590 < baseStart_312590 := by decide
  rcases family_descends (prefixWord ++ tailWord_312590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312594 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_312594 : Nat := 118140960795 + 312594 * 2 ^ 59
def prefixEnd_312594 : Nat := 4983230072969 + 3 ^ 40 * 312594 * 2
def baseEnd_312594 : Nat := 160510971711655208237413

theorem tailTrace_312594 : CollatzResearch.WordTrace tailWord_312594 prefixEnd_312594 160510971711655208237413 := by
  unfold tailWord_312594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850309957383199912492209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7600826553021866433312557 2850309957383199912492209)
  ·
    refine ⟨2137732468037399934369157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2850309957383199912492209 2137732468037399934369157)
    ·
      refine ⟨400824837757012487694217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2137732468037399934369157 400824837757012487694217)
      ·
        refine ⟨300618628317759365770663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400824837757012487694217 300618628317759365770663)
        ·
          refine ⟨450927942476639048655995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300618628317759365770663 450927942476639048655995)
          ·
            refine ⟨676391913714958572983993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450927942476639048655995 676391913714958572983993)
            ·
              refine ⟨507293935286218929737995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676391913714958572983993 507293935286218929737995)
              ·
                refine ⟨760940902929328394606993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507293935286218929737995 760940902929328394606993)
                ·
                  refine ⟨570705677196996295955245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 760940902929328394606993 570705677196996295955245)
                  ·
                    refine ⟨214014628948873610983217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570705677196996295955245 214014628948873610983217)
                    ·
                      refine ⟨160510971711655208237413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214014628948873610983217 160510971711655208237413)
                      ·
                        rfl

theorem cell23_312594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_312594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312594 prefixEnd_312594 := by exact prefixLift 312594
  have htrace : WordTrace (prefixWord ++ tailWord_312594) baseStart_312594 baseEnd_312594 := by
    simpa [prefixWord, tailWord_312594, baseEnd_312594] using wordTrace_append hprefix tailTrace_312594
  have hstable : (prefixWord ++ tailWord_312594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312594).length < 2 ^ (prefixWord ++ tailWord_312594).sum := by decide
  have hdescent : baseEnd_312594 < baseStart_312594 := by decide
  rcases family_descends (prefixWord ++ tailWord_312594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312610 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_312610 : Nat := 118140960795 + 312610 * 2 ^ 59
def prefixEnd_312610 : Nat := 4983230072969 + 3 ^ 40 * 312610 * 2
def baseEnd_312610 : Nat := 160519187402127145637339

theorem tailTrace_312610 : CollatzResearch.WordTrace tailWord_312610 prefixEnd_312610 160519187402127145637339 := by
  unfold tailWord_312610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850455849368708595637821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7601215598316556255034189 2850455849368708595637821)
  ·
    refine ⟨1068920943513265723364183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2850455849368708595637821 1068920943513265723364183)
    ·
      refine ⟨1603381415269898585046275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068920943513265723364183 1603381415269898585046275)
      ·
        refine ⟨2405072122904847877569413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603381415269898585046275 2405072122904847877569413)
        ·
          refine ⟨450951023044658977044265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2405072122904847877569413 450951023044658977044265)
          ·
            refine ⟨338213267283494232783199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450951023044658977044265 338213267283494232783199)
            ·
              refine ⟨507319900925241349174799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338213267283494232783199 507319900925241349174799)
              ·
                refine ⟨760979851387862023762199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507319900925241349174799 760979851387862023762199)
                ·
                  refine ⟨1141469777081793035643299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760979851387862023762199 1141469777081793035643299)
                  ·
                    refine ⟨1712204665622689553464949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1141469777081793035643299 1712204665622689553464949)
                    ·
                      refine ⟨160519187402127145637339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1712204665622689553464949 160519187402127145637339)
                      ·
                        rfl

theorem cell23_312610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_312610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312610 prefixEnd_312610 := by exact prefixLift 312610
  have htrace : WordTrace (prefixWord ++ tailWord_312610) baseStart_312610 baseEnd_312610 := by
    simpa [prefixWord, tailWord_312610, baseEnd_312610] using wordTrace_append hprefix tailTrace_312610
  have hstable : (prefixWord ++ tailWord_312610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312610).length < 2 ^ (prefixWord ++ tailWord_312610).sum := by decide
  have hdescent : baseEnd_312610 < baseStart_312610 := by decide
  rcases family_descends (prefixWord ++ tailWord_312610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312626 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_312626 : Nat := 118140960795 + 312626 * 2 ^ 59
def prefixEnd_312626 : Nat := 4983230072969 + 3 ^ 40 * 312626 * 2
def baseEnd_312626 : Nat := 53509134364199694345755

theorem tailTrace_312626 : CollatzResearch.WordTrace tailWord_312626 prefixEnd_312626 53509134364199694345755 := by
  unfold tailWord_312626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850601741354217278783433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7601604643611246076755821 2850601741354217278783433)
  ·
    refine ⟨2137951306015662959087575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2850601741354217278783433 2137951306015662959087575)
    ·
      refine ⟨3206926959023494438631363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137951306015662959087575 3206926959023494438631363)
      ·
        refine ⟨4810390438535241657947045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3206926959023494438631363 4810390438535241657947045)
        ·
          refine ⟨901948207225357810865071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4810390438535241657947045 901948207225357810865071)
          ·
            refine ⟨1352922310838036716297607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901948207225357810865071 1352922310838036716297607)
            ·
              refine ⟨2029383466257055074446411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352922310838036716297607 2029383466257055074446411)
              ·
                refine ⟨3044075199385582611669617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029383466257055074446411 3044075199385582611669617)
                ·
                  refine ⟨2283056399539186958752213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044075199385582611669617 2283056399539186958752213)
                  ·
                    refine ⟨53509134364199694345755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2283056399539186958752213 53509134364199694345755)
                    ·
                      rfl

theorem cell23_312626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_312626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312626 prefixEnd_312626 := by exact prefixLift 312626
  have htrace : WordTrace (prefixWord ++ tailWord_312626) baseStart_312626 baseEnd_312626 := by
    simpa [prefixWord, tailWord_312626, baseEnd_312626] using wordTrace_append hprefix tailTrace_312626
  have hstable : (prefixWord ++ tailWord_312626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312626).length < 2 ^ (prefixWord ++ tailWord_312626).sum := by decide
  have hdescent : baseEnd_312626 < baseStart_312626 := by decide
  rcases family_descends (prefixWord ++ tailWord_312626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312666 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_312666 : Nat := 118140960795 + 312666 * 2 ^ 59
def prefixEnd_312666 : Nat := 4983230072969 + 3 ^ 40 * 312666 * 2
def baseEnd_312666 : Nat := 160547942318778926537081

theorem tailTrace_312666 : CollatzResearch.WordTrace tailWord_312666 prefixEnd_312666 160547942318778926537081 := by
  unfold tailWord_312666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850966471317988986647463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7602577256847970631059901 2850966471317988986647463)
  ·
    refine ⟨4276449706976983479971195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850966471317988986647463 4276449706976983479971195)
    ·
      refine ⟨6414674560465475219956793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276449706976983479971195 6414674560465475219956793)
      ·
        refine ⟨4811005920349106414967595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6414674560465475219956793 4811005920349106414967595)
        ·
          refine ⟨7216508880523659622451393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811005920349106414967595 7216508880523659622451393)
          ·
            refine ⟨5412381660392744716838545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7216508880523659622451393 5412381660392744716838545)
            ·
              refine ⟨4059286245294558537628909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412381660392744716838545 4059286245294558537628909)
              ·
                refine ⟨1522232341985459451610841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059286245294558537628909 1522232341985459451610841)
                ·
                  refine ⟨1141674256489094588708131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522232341985459451610841 1141674256489094588708131)
                  ·
                    refine ⟨1712511384733641883062197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1141674256489094588708131 1712511384733641883062197)
                    ·
                      refine ⟨160547942318778926537081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1712511384733641883062197 160547942318778926537081)
                      ·
                        rfl

theorem cell23_312666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_312666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312666 prefixEnd_312666 := by exact prefixLift 312666
  have htrace : WordTrace (prefixWord ++ tailWord_312666) baseStart_312666 baseEnd_312666 := by
    simpa [prefixWord, tailWord_312666, baseEnd_312666] using wordTrace_append hprefix tailTrace_312666
  have hstable : (prefixWord ++ tailWord_312666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312666).length < 2 ^ (prefixWord ++ tailWord_312666).sum := by decide
  have hdescent : baseEnd_312666 < baseStart_312666 := by decide
  rcases family_descends (prefixWord ++ tailWord_312666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312716 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_312716 : Nat := 118140960795 + 312716 * 2 ^ 59
def prefixEnd_312716 : Nat := 4983230072969 + 3 ^ 40 * 312716 * 2
def baseEnd_312716 : Nat := 53524538783834576970617

theorem tailTrace_312716 : CollatzResearch.WordTrace tailWord_312716 prefixEnd_312716 53524538783834576970617 := by
  unfold tailWord_312716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702844767545407242955001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7603793023393876323940001 5702844767545407242955001)
  ·
    refine ⟨4277133575659055432216251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5702844767545407242955001 4277133575659055432216251)
    ·
      refine ⟨6415700363488583148324377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4277133575659055432216251 6415700363488583148324377)
      ·
        refine ⟨4811775272616437361243283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6415700363488583148324377 4811775272616437361243283)
        ·
          refine ⟨7217662908924656041864925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811775272616437361243283 7217662908924656041864925)
          ·
            refine ⟨2706623590846746015699347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7217662908924656041864925 2706623590846746015699347)
            ·
              refine ⟨4059935386270119023549021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706623590846746015699347 4059935386270119023549021)
              ·
                refine ⟨1522475769851294633830883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059935386270119023549021 1522475769851294633830883)
                ·
                  refine ⟨2283713654776941950746325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522475769851294633830883 2283713654776941950746325)
                  ·
                    refine ⟨53524538783834576970617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2283713654776941950746325 53524538783834576970617)
                    ·
                      rfl

theorem cell23_312716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_312716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312716 prefixEnd_312716 := by exact prefixLift 312716
  have htrace : WordTrace (prefixWord ++ tailWord_312716) baseStart_312716 baseEnd_312716 := by
    simpa [prefixWord, tailWord_312716, baseEnd_312716] using wordTrace_append hprefix tailTrace_312716
  have hstable : (prefixWord ++ tailWord_312716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312716).length < 2 ^ (prefixWord ++ tailWord_312716).sum := by decide
  have hdescent : baseEnd_312716 < baseStart_312716 := by decide
  rcases family_descends (prefixWord ++ tailWord_312716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312733 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_312733 : Nat := 118140960795 + 312733 * 2 ^ 59
def prefixEnd_312733 : Nat := 4983230072969 + 3 ^ 40 * 312733 * 2
def baseEnd_312733 : Nat := 53527448507543388133091

theorem tailTrace_312733 : CollatzResearch.WordTrace tailWord_312733 prefixEnd_312733 53527448507543388133091 := by
  unfold tailWord_312733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406309576029226389278853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7604206384019484259519235 11406309576029226389278853)
  ·
    refine ⟨2138683045505479947989785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11406309576029226389278853 2138683045505479947989785)
    ·
      refine ⟨1604012284129109960992339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2138683045505479947989785 1604012284129109960992339)
      ·
        refine ⟨2406018426193664941488509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604012284129109960992339 2406018426193664941488509)
        ·
          refine ⟨902256909822624353058191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2406018426193664941488509 902256909822624353058191)
          ·
            refine ⟨1353385364733936529587287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902256909822624353058191 1353385364733936529587287)
            ·
              refine ⟨2030078047100904794380931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353385364733936529587287 2030078047100904794380931)
              ·
                refine ⟨3045117070651357191571397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030078047100904794380931 3045117070651357191571397)
                ·
                  refine ⟨570959450747129473419637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3045117070651357191571397 570959450747129473419637)
                  ·
                    refine ⟨53527448507543388133091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 570959450747129473419637 53527448507543388133091)
                    ·
                      rfl

theorem cell23_312733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_312733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312733 prefixEnd_312733 := by exact prefixLift 312733
  have htrace : WordTrace (prefixWord ++ tailWord_312733) baseStart_312733 baseEnd_312733 := by
    simpa [prefixWord, tailWord_312733, baseEnd_312733] using wordTrace_append hprefix tailTrace_312733
  have hstable : (prefixWord ++ tailWord_312733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312733).length < 2 ^ (prefixWord ++ tailWord_312733).sum := by decide
  have hdescent : baseEnd_312733 < baseStart_312733 := by decide
  rcases family_descends (prefixWord ++ tailWord_312733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312743 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_312743 : Nat := 118140960795 + 312743 * 2 ^ 59
def prefixEnd_312743 : Nat := 4983230072969 + 3 ^ 40 * 312743 * 2
def baseEnd_312743 : Nat := 160587480329175125274227

theorem tailTrace_312743 : CollatzResearch.WordTrace tailWord_312743 prefixEnd_312743 160587480329175125274227 := by
  unfold tailWord_312743
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406674305992998097142883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7604449537328665398095255 11406674305992998097142883)
  ·
    refine ⟨17110011458989497145714325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11406674305992998097142883 17110011458989497145714325)
    ·
      refine ⟨802031787140132678705359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17110011458989497145714325 802031787140132678705359)
      ·
        refine ⟨1203047680710199018058039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802031787140132678705359 1203047680710199018058039)
        ·
          refine ⟨1804571521065298527087059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203047680710199018058039 1804571521065298527087059)
          ·
            refine ⟨2706857281597947790630589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804571521065298527087059 2706857281597947790630589)
            ·
              refine ⟨1015071480599230421486471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2706857281597947790630589 1015071480599230421486471)
              ·
                refine ⟨1522607220898845632229707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015071480599230421486471 1522607220898845632229707)
                ·
                  refine ⟨2283910831348268448344561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522607220898845632229707 2283910831348268448344561)
                  ·
                    refine ⟨1712933123511201336258421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283910831348268448344561 1712933123511201336258421)
                    ·
                      refine ⟨160587480329175125274227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1712933123511201336258421 160587480329175125274227)
                      ·
                        rfl

theorem cell23_312743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_312743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312743 prefixEnd_312743 := by exact prefixLift 312743
  have htrace : WordTrace (prefixWord ++ tailWord_312743) baseStart_312743 baseEnd_312743 := by
    simpa [prefixWord, tailWord_312743, baseEnd_312743] using wordTrace_append hprefix tailTrace_312743
  have hstable : (prefixWord ++ tailWord_312743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312743).length < 2 ^ (prefixWord ++ tailWord_312743).sum := by decide
  have hdescent : baseEnd_312743 < baseStart_312743 := by decide
  rcases family_descends (prefixWord ++ tailWord_312743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312753 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_312753 : Nat := 118140960795 + 312753 * 2 ^ 59
def prefixEnd_312753 : Nat := 4983230072969 + 3 ^ 40 * 312753 * 2
def baseEnd_312753 : Nat := 160592615135720086149181

theorem tailTrace_312753 : CollatzResearch.WordTrace tailWord_312753 prefixEnd_312753 160592615135720086149181 := by
  unfold tailWord_312753
  simp only [CollatzResearch.WordTrace]
  refine ⟨11407039035956769805006913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7604692690637846536671275 11407039035956769805006913)
  ·
    refine ⟨8555279276967577353755185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11407039035956769805006913 8555279276967577353755185)
    ·
      refine ⟨6416459457725683015316389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8555279276967577353755185 6416459457725683015316389)
      ·
        refine ⟨1203086148323565565371823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6416459457725683015316389 1203086148323565565371823)
        ·
          refine ⟨1804629222485348348057735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203086148323565565371823 1804629222485348348057735)
          ·
            refine ⟨2706943833728022522086603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804629222485348348057735 2706943833728022522086603)
            ·
              refine ⟨4060415750592033783129905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706943833728022522086603 4060415750592033783129905)
              ·
                refine ⟨3045311812944025337347429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060415750592033783129905 3045311812944025337347429)
                ·
                  refine ⟨570995964927004750752643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3045311812944025337347429 570995964927004750752643)
                  ·
                    refine ⟨856493947390507126128965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 570995964927004750752643 856493947390507126128965)
                    ·
                      refine ⟨160592615135720086149181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 856493947390507126128965 160592615135720086149181)
                      ·
                        rfl

theorem cell23_312753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_312753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312753 prefixEnd_312753 := by exact prefixLift 312753
  have htrace : WordTrace (prefixWord ++ tailWord_312753) baseStart_312753 baseEnd_312753 := by
    simpa [prefixWord, tailWord_312753, baseEnd_312753] using wordTrace_append hprefix tailTrace_312753
  have hstable : (prefixWord ++ tailWord_312753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312753).length < 2 ^ (prefixWord ++ tailWord_312753).sum := by decide
  have hdescent : baseEnd_312753 < baseStart_312753 := by decide
  rcases family_descends (prefixWord ++ tailWord_312753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312793 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 6]
def baseStart_312793 : Nat := 118140960795 + 312793 * 2 ^ 59
def prefixEnd_312793 : Nat := 4983230072969 + 3 ^ 40 * 312793 * 2
def baseEnd_312793 : Nat := 17845906040211103294333

theorem tailTrace_312793 : CollatzResearch.WordTrace tailWord_312793 prefixEnd_312793 17845906040211103294333 := by
  unfold tailWord_312793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408497955811856636463033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7605665303874571090975355 11408497955811856636463033)
  ·
    refine ⟨8556373466858892477347275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11408497955811856636463033 8556373466858892477347275)
    ·
      refine ⟨12834560200288338716020913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8556373466858892477347275 12834560200288338716020913)
      ·
        refine ⟨9625920150216254037015685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12834560200288338716020913 9625920150216254037015685)
        ·
          refine ⟨1804860028165547631940441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9625920150216254037015685 1804860028165547631940441)
          ·
            refine ⟨1353645021124160723955331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804860028165547631940441 1353645021124160723955331)
            ·
              refine ⟨2030467531686241085932997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353645021124160723955331 2030467531686241085932997)
              ·
                refine ⟨380712662191170203612437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2030467531686241085932997 380712662191170203612437)
                ·
                  refine ⟨17845906040211103294333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 380712662191170203612437 17845906040211103294333)
                  ·
                    rfl

theorem cell23_312793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_312793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312793 prefixEnd_312793 := by exact prefixLift 312793
  have htrace : WordTrace (prefixWord ++ tailWord_312793) baseStart_312793 baseEnd_312793 := by
    simpa [prefixWord, tailWord_312793, baseEnd_312793] using wordTrace_append hprefix tailTrace_312793
  have hstable : (prefixWord ++ tailWord_312793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312793).length < 2 ^ (prefixWord ++ tailWord_312793).sum := by decide
  have hdescent : baseEnd_312793 < baseStart_312793 := by decide
  rcases family_descends (prefixWord ++ tailWord_312793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312863 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_312863 : Nat := 118140960795 + 312863 * 2 ^ 59
def prefixEnd_312863 : Nat := 4983230072969 + 3 ^ 40 * 312863 * 2
def baseEnd_312863 : Nat := 160649098007714655773675

theorem tailTrace_312863 : CollatzResearch.WordTrace tailWord_312863 prefixEnd_312863 160649098007714655773675 := by
  unfold tailWord_312863
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411051065558258591511243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7607367377038839061007495 11411051065558258591511243)
  ·
    refine ⟨17116576598337387887266865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411051065558258591511243 17116576598337387887266865)
    ·
      refine ⟨12837432448753040915450149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17116576598337387887266865 12837432448753040915450149)
      ·
        refine ⟨2407018584141195171646903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12837432448753040915450149 2407018584141195171646903)
        ·
          refine ⟨3610527876211792757470355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407018584141195171646903 3610527876211792757470355)
          ·
            refine ⟨5415791814317689136205533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610527876211792757470355 5415791814317689136205533)
            ·
              refine ⟨2030921930369133426077075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5415791814317689136205533 2030921930369133426077075)
              ·
                refine ⟨3046382895553700139115613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030921930369133426077075 3046382895553700139115613)
                ·
                  refine ⟨1142393585832637552168355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3046382895553700139115613 1142393585832637552168355)
                  ·
                    refine ⟨1713590378748956328252533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142393585832637552168355 1713590378748956328252533)
                    ·
                      refine ⟨160649098007714655773675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1713590378748956328252533 160649098007714655773675)
                      ·
                        rfl

theorem cell23_312863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_312863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312863 prefixEnd_312863 := by exact prefixLift 312863
  have htrace : WordTrace (prefixWord ++ tailWord_312863) baseStart_312863 baseEnd_312863 := by
    simpa [prefixWord, tailWord_312863, baseEnd_312863] using wordTrace_append hprefix tailTrace_312863
  have hstable : (prefixWord ++ tailWord_312863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312863).length < 2 ^ (prefixWord ++ tailWord_312863).sum := by decide
  have hdescent : baseEnd_312863 < baseStart_312863 := by decide
  rcases family_descends (prefixWord ++ tailWord_312863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312883 : List Nat := [1, 1, 1, 2, 4, 4, 1, 9]
def baseStart_312883 : Nat := 118140960795 + 312883 * 2 ^ 59
def prefixEnd_312883 : Nat := 4983230072969 + 3 ^ 40 * 312883 * 2
def baseEnd_312883 : Nat := 5950346948918688056429

theorem tailTrace_312883 : CollatzResearch.WordTrace tailWord_312883 prefixEnd_312883 5950346948918688056429 := by
  unfold tailWord_312883
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411780525485802007239303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7607853683657201338159535 11411780525485802007239303)
  ·
    refine ⟨17117670788228703010858955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411780525485802007239303 17117670788228703010858955)
    ·
      refine ⟨25676506182343054516288433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117670788228703010858955 25676506182343054516288433)
      ·
        refine ⟨19257379636757290887216325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25676506182343054516288433 19257379636757290887216325)
        ·
          refine ⟨3610758681891992041353061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19257379636757290887216325 3610758681891992041353061)
          ·
            refine ⟨677017252854748507753699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3610758681891992041353061 677017252854748507753699)
            ·
              refine ⟨1015525879282122761630549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677017252854748507753699 1015525879282122761630549)
              ·
                refine ⟨5950346948918688056429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1015525879282122761630549 5950346948918688056429)
                ·
                  rfl

theorem cell23_312883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 9].length) (baseStart_312883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312883 prefixEnd_312883 := by exact prefixLift 312883
  have htrace : WordTrace (prefixWord ++ tailWord_312883) baseStart_312883 baseEnd_312883 := by
    simpa [prefixWord, tailWord_312883, baseEnd_312883] using wordTrace_append hprefix tailTrace_312883
  have hstable : (prefixWord ++ tailWord_312883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312883).length < 2 ^ (prefixWord ++ tailWord_312883).sum := by decide
  have hdescent : baseEnd_312883 < baseStart_312883 := by decide
  rcases family_descends (prefixWord ++ tailWord_312883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312897 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_312897 : Nat := 118140960795 + 312897 * 2 ^ 59
def prefixEnd_312897 : Nat := 4983230072969 + 3 ^ 40 * 312897 * 2
def baseEnd_312897 : Nat := 160666556349967522748519

theorem tailTrace_312897 : CollatzResearch.WordTrace tailWord_312897 prefixEnd_312897 160666556349967522748519 := by
  unfold tailWord_312897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412291147435082398248945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7608194098290054932165963 11412291147435082398248945)
  ·
    refine ⟨8559218360576311798686709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11412291147435082398248945 8559218360576311798686709)
    ·
      refine ⟨802426721304029231126879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8559218360576311798686709 802426721304029231126879)
      ·
        refine ⟨1203640081956043846690319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802426721304029231126879 1203640081956043846690319)
        ·
          refine ⟨1805460122934065770035479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203640081956043846690319 1805460122934065770035479)
          ·
            refine ⟨2708190184401098655053219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805460122934065770035479 2708190184401098655053219)
            ·
              refine ⟨4062285276601647982579829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708190184401098655053219 4062285276601647982579829)
              ·
                refine ⟨380839244681404498366859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4062285276601647982579829 380839244681404498366859)
                ·
                  refine ⟨571258867022106747550289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380839244681404498366859 571258867022106747550289)
                  ·
                    refine ⟨428444150266580060662717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571258867022106747550289 428444150266580060662717)
                    ·
                      refine ⟨160666556349967522748519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 428444150266580060662717 160666556349967522748519)
                      ·
                        rfl

theorem cell23_312897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_312897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312897 prefixEnd_312897 := by exact prefixLift 312897
  have htrace : WordTrace (prefixWord ++ tailWord_312897) baseStart_312897 baseEnd_312897 := by
    simpa [prefixWord, tailWord_312897, baseEnd_312897] using wordTrace_append hprefix tailTrace_312897
  have hstable : (prefixWord ++ tailWord_312897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312897).length < 2 ^ (prefixWord ++ tailWord_312897).sum := by decide
  have hdescent : baseEnd_312897 < baseStart_312897 := by decide
  rcases family_descends (prefixWord ++ tailWord_312897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312913 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_312913 : Nat := 118140960795 + 312913 * 2 ^ 59
def prefixEnd_312913 : Nat := 4983230072969 + 3 ^ 40 * 312913 * 2
def baseEnd_312913 : Nat := 53558257346813153382815

theorem tailTrace_312913 : CollatzResearch.WordTrace tailWord_312913 prefixEnd_312913 53558257346813153382815 := by
  unfold tailWord_312913
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412874715377117130831393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7608583143584744753887595 11412874715377117130831393)
  ·
    refine ⟨8559656036532837848123545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11412874715377117130831393 8559656036532837848123545)
    ·
      refine ⟨6419742027399628386092659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8559656036532837848123545 6419742027399628386092659)
      ·
        refine ⟨9629613041099442579138989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419742027399628386092659 9629613041099442579138989)
        ·
          refine ⟨3611104890412290967177121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9629613041099442579138989 3611104890412290967177121)
          ·
            refine ⟨2708328667809218225382841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3611104890412290967177121 2708328667809218225382841)
            ·
              refine ⟨2031246500856913669037131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708328667809218225382841 2031246500856913669037131)
              ·
                refine ⟨3046869751285370503555697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031246500856913669037131 3046869751285370503555697)
                ·
                  refine ⟨2285152313464027877666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3046869751285370503555697 2285152313464027877666773)
                  ·
                    refine ⟨53558257346813153382815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2285152313464027877666773 53558257346813153382815)
                    ·
                      rfl

theorem cell23_312913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_312913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312913 prefixEnd_312913 := by exact prefixLift 312913
  have htrace : WordTrace (prefixWord ++ tailWord_312913) baseStart_312913 baseEnd_312913 := by
    simpa [prefixWord, tailWord_312913, baseEnd_312913] using wordTrace_append hprefix tailTrace_312913
  have hstable : (prefixWord ++ tailWord_312913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312913).length < 2 ^ (prefixWord ++ tailWord_312913).sum := by decide
  have hdescent : baseEnd_312913 < baseStart_312913 := by decide
  rcases family_descends (prefixWord ++ tailWord_312913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312920 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_312920 : Nat := 118140960795 + 312920 * 2 ^ 59
def prefixEnd_312920 : Nat := 4983230072969 + 3 ^ 40 * 312920 * 2
def baseEnd_312920 : Nat := 160678366405020932760913

theorem tailTrace_312920 : CollatzResearch.WordTrace tailWord_312920 prefixEnd_312920 160678366405020932760913 := by
  unfold tailWord_312920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706565013175878663168107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7608753350901171550890809 5706565013175878663168107)
  ·
    refine ⟨8559847519763817994752161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5706565013175878663168107 8559847519763817994752161)
    ·
      refine ⟨6419885639822863496064121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8559847519763817994752161 6419885639822863496064121)
      ·
        refine ⟨4814914229867147622048091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6419885639822863496064121 4814914229867147622048091)
        ·
          refine ⟨7222371344800721433072137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814914229867147622048091 7222371344800721433072137)
          ·
            refine ⟨5416778508600541074804103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7222371344800721433072137 5416778508600541074804103)
            ·
              refine ⟨8125167762900811612206155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416778508600541074804103 8125167762900811612206155)
              ·
                refine ⟨12187751644351217418309233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8125167762900811612206155 12187751644351217418309233)
                ·
                  refine ⟨9140813733263413063731925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12187751644351217418309233 9140813733263413063731925)
                  ·
                    refine ⟨214237821873361243681217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9140813733263413063731925 214237821873361243681217)
                    ·
                      refine ⟨160678366405020932760913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214237821873361243681217 160678366405020932760913)
                      ·
                        rfl

theorem cell23_312920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_312920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312920 prefixEnd_312920 := by exact prefixLift 312920
  have htrace : WordTrace (prefixWord ++ tailWord_312920) baseStart_312920 baseEnd_312920 := by
    simpa [prefixWord, tailWord_312920, baseEnd_312920] using wordTrace_append hprefix tailTrace_312920
  have hstable : (prefixWord ++ tailWord_312920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312920).length < 2 ^ (prefixWord ++ tailWord_312920).sum := by decide
  have hdescent : baseEnd_312920 < baseStart_312920 := by decide
  rcases family_descends (prefixWord ++ tailWord_312920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312943 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 4, 6]
def baseStart_312943 : Nat := 118140960795 + 312943 * 2 ^ 59
def prefixEnd_312943 : Nat := 4983230072969 + 3 ^ 40 * 312943 * 2
def baseEnd_312943 : Nat := 53563392153358114257769

theorem tailTrace_312943 : CollatzResearch.WordTrace tailWord_312943 prefixEnd_312943 53563392153358114257769 := by
  unfold tailWord_312943
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413968905268432254423483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7609312603512288169615655 11413968905268432254423483)
  ·
    refine ⟨17120953357902648381635225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11413968905268432254423483 17120953357902648381635225)
    ·
      refine ⟨12840715018426986286226419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17120953357902648381635225 12840715018426986286226419)
      ·
        refine ⟨19261072527640479429339629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12840715018426986286226419 19261072527640479429339629)
        ·
          refine ⟨7222902197865179786002361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19261072527640479429339629 7222902197865179786002361)
          ·
            refine ⟨5417176648398884839501771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7222902197865179786002361 5417176648398884839501771)
            ·
              refine ⟨8125764972598327259252657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417176648398884839501771 8125764972598327259252657)
              ·
                refine ⟨6094323729448745444439493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8125764972598327259252657 6094323729448745444439493)
                ·
                  refine ⟨1142685699271639770832405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6094323729448745444439493 1142685699271639770832405)
                  ·
                    refine ⟨53563392153358114257769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1142685699271639770832405 53563392153358114257769)
                    ·
                      rfl

theorem cell23_312943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_312943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312943 prefixEnd_312943 := by exact prefixLift 312943
  have htrace : WordTrace (prefixWord ++ tailWord_312943) baseStart_312943 baseEnd_312943 := by
    simpa [prefixWord, tailWord_312943, baseEnd_312943] using wordTrace_append hprefix tailTrace_312943
  have hstable : (prefixWord ++ tailWord_312943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312943).length < 2 ^ (prefixWord ++ tailWord_312943).sum := by decide
  have hdescent : baseEnd_312943 < baseStart_312943 := by decide
  rcases family_descends (prefixWord ++ tailWord_312943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312963 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_312963 : Nat := 118140960795 + 312963 * 2 ^ 59
def prefixEnd_312963 : Nat := 4983230072969 + 3 ^ 40 * 312963 * 2
def baseEnd_312963 : Nat := 160700446073164264523215

theorem tailTrace_312963 : CollatzResearch.WordTrace tailWord_312963 prefixEnd_312963 160700446073164264523215 := by
  unfold tailWord_312963
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414698365195975670151543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7609798910130650446767695 11414698365195975670151543)
  ·
    refine ⟨17122047547793963505227315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11414698365195975670151543 17122047547793963505227315)
    ·
      refine ⟨25683071321690945257840973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17122047547793963505227315 25683071321690945257840973)
      ·
        refine ⟨9631151745634104471690365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25683071321690945257840973 9631151745634104471690365)
        ·
          refine ⟨3611681904612789176883887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9631151745634104471690365 3611681904612789176883887)
          ·
            refine ⟨5417522856919183765325831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611681904612789176883887 5417522856919183765325831)
            ·
              refine ⟨8126284285378775647988747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417522856919183765325831 8126284285378775647988747)
              ·
                refine ⟨12189426428068163471983121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126284285378775647988747 12189426428068163471983121)
                ·
                  refine ⟨9142069821051122603987341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12189426428068163471983121 9142069821051122603987341)
                  ·
                    refine ⟨3428276182894170976495253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9142069821051122603987341 3428276182894170976495253)
                    ·
                      refine ⟨160700446073164264523215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3428276182894170976495253 160700446073164264523215)
                      ·
                        rfl

theorem cell23_312963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_312963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312963 prefixEnd_312963 := by exact prefixLift 312963
  have htrace : WordTrace (prefixWord ++ tailWord_312963) baseStart_312963 baseEnd_312963 := by
    simpa [prefixWord, tailWord_312963, baseEnd_312963] using wordTrace_append hprefix tailTrace_312963
  have hstable : (prefixWord ++ tailWord_312963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312963).length < 2 ^ (prefixWord ++ tailWord_312963).sum := by decide
  have hdescent : baseEnd_312963 < baseStart_312963 := by decide
  rcases family_descends (prefixWord ++ tailWord_312963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312984 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_312984 : Nat := 118140960795 + 312984 * 2 ^ 59
def prefixEnd_312984 : Nat := 4983230072969 + 3 ^ 40 * 312984 * 2
def baseEnd_312984 : Nat := 160711229166908682360619

theorem tailTrace_312984 : CollatzResearch.WordTrace tailWord_312984 prefixEnd_312984 160711229166908682360619 := by
  unfold tailWord_312984
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707732149059948128333003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7610309532079930837777337 5707732149059948128333003)
  ·
    refine ⟨8561598223589922192499505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5707732149059948128333003 8561598223589922192499505)
    ·
      refine ⟨6421198667692441644374629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8561598223589922192499505 6421198667692441644374629)
      ·
        refine ⟨1203974750192332808320243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6421198667692441644374629 1203974750192332808320243)
        ·
          refine ⟨1805962125288499212480365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203974750192332808320243 1805962125288499212480365)
          ·
            refine ⟨677235796983187204680137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1805962125288499212480365 677235796983187204680137)
            ·
              refine ⟨507926847737390403510103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677235796983187204680137 507926847737390403510103)
              ·
                refine ⟨761890271606085605265155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507926847737390403510103 761890271606085605265155)
                ·
                  refine ⟨1142835407409128407897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761890271606085605265155 1142835407409128407897733)
                  ·
                    refine ⟨214281638889211576480825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142835407409128407897733 214281638889211576480825)
                    ·
                      refine ⟨160711229166908682360619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214281638889211576480825 160711229166908682360619)
                      ·
                        rfl

theorem cell23_312984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_312984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_312984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_312984 prefixEnd_312984 := by exact prefixLift 312984
  have htrace : WordTrace (prefixWord ++ tailWord_312984) baseStart_312984 baseEnd_312984 := by
    simpa [prefixWord, tailWord_312984, baseEnd_312984] using wordTrace_append hprefix tailTrace_312984
  have hstable : (prefixWord ++ tailWord_312984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312984).length < 2 ^ (prefixWord ++ tailWord_312984).sum := by decide
  have hdescent : baseEnd_312984 < baseStart_312984 := by decide
  rcases family_descends (prefixWord ++ tailWord_312984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313007 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 5]
def baseStart_313007 : Nat := 118140960795 + 313007 * 2 ^ 59
def prefixEnd_313007 : Nat := 4983230072969 + 3 ^ 40 * 313007 * 2
def baseEnd_313007 : Nat := 17858115469106899152557

theorem tailTrace_313007 : CollatzResearch.WordTrace tailWord_313007 prefixEnd_313007 17858115469106899152557 := by
  unfold tailWord_313007
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416303177036571184753275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7610868784691047456502183 11416303177036571184753275)
  ·
    refine ⟨17124454765554856777129913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416303177036571184753275 17124454765554856777129913)
    ·
      refine ⟨12843341074166142582847435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17124454765554856777129913 12843341074166142582847435)
      ·
        refine ⟨19265011611249213874271153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843341074166142582847435 19265011611249213874271153)
        ·
          refine ⟨14448758708436910405703365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19265011611249213874271153 14448758708436910405703365)
          ·
            refine ⟨2709142257831920701069381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14448758708436910405703365 2709142257831920701069381)
            ·
              refine ⟨507964173343485131450509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2709142257831920701069381 507964173343485131450509)
              ·
                refine ⟨190486565003806924293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507964173343485131450509 190486565003806924293941)
                ·
                  refine ⟨17858115469106899152557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190486565003806924293941 17858115469106899152557)
                  ·
                    rfl

theorem cell23_313007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 5].length) (baseStart_313007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313007 prefixEnd_313007 := by exact prefixLift 313007
  have htrace : WordTrace (prefixWord ++ tailWord_313007) baseStart_313007 baseEnd_313007 := by
    simpa [prefixWord, tailWord_313007, baseEnd_313007] using wordTrace_append hprefix tailTrace_313007
  have hstable : (prefixWord ++ tailWord_313007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313007).length < 2 ^ (prefixWord ++ tailWord_313007).sum := by decide
  have hdescent : baseEnd_313007 < baseStart_313007 := by decide
  rcases family_descends (prefixWord ++ tailWord_313007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313014 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_313014 : Nat := 118140960795 + 313014 * 2 ^ 59
def prefixEnd_313014 : Nat := 4983230072969 + 3 ^ 40 * 313014 * 2
def baseEnd_313014 : Nat := 160726633586543564985481

theorem tailTrace_313014 : CollatzResearch.WordTrace tailWord_313014 prefixEnd_313014 160726633586543564985481 := by
  unfold tailWord_313014
  simp only [CollatzResearch.WordTrace]
  refine ⟨713534905500700711266131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7611038992007474253505397 713534905500700711266131)
  ·
    refine ⟨1070302358251051066899197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713534905500700711266131 1070302358251051066899197)
    ·
      refine ⟨401363384344144150087199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1070302358251051066899197 401363384344144150087199)
      ·
        refine ⟨602045076516216225130799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401363384344144150087199 602045076516216225130799)
        ·
          refine ⟨903067614774324337696199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602045076516216225130799 903067614774324337696199)
          ·
            refine ⟨1354601422161486506544299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903067614774324337696199 1354601422161486506544299)
            ·
              refine ⟨2031902133242229759816449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354601422161486506544299 2031902133242229759816449)
              ·
                refine ⟨1523926599931672319862337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031902133242229759816449 1523926599931672319862337)
                ·
                  refine ⟨1142944949948754239896753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1523926599931672319862337 1142944949948754239896753)
                  ·
                    refine ⟨857208712461565679922565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1142944949948754239896753 857208712461565679922565)
                    ·
                      refine ⟨160726633586543564985481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 857208712461565679922565 160726633586543564985481)
                      ·
                        rfl

theorem cell23_313014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_313014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313014 prefixEnd_313014 := by exact prefixLift 313014
  have htrace : WordTrace (prefixWord ++ tailWord_313014) baseStart_313014 baseEnd_313014 := by
    simpa [prefixWord, tailWord_313014, baseEnd_313014] using wordTrace_append hprefix tailTrace_313014
  have hstable : (prefixWord ++ tailWord_313014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313014).length < 2 ^ (prefixWord ++ tailWord_313014).sum := by decide
  have hdescent : baseEnd_313014 < baseStart_313014 := by decide
  rcases family_descends (prefixWord ++ tailWord_313014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313040 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_313040 : Nat := 118140960795 + 313040 * 2 ^ 59
def prefixEnd_313040 : Nat := 4983230072969 + 3 ^ 40 * 313040 * 2
def baseEnd_313040 : Nat := 160739984083560463260361

theorem tailTrace_313040 : CollatzResearch.WordTrace tailWord_313040 prefixEnd_313040 160739984083560463260361 := by
  unfold tailWord_313040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708753392958508910352287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7611671190611345213803049 5708753392958508910352287)
  ·
    refine ⟨8563130089437763365528431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708753392958508910352287 8563130089437763365528431)
    ·
      refine ⟨12844695134156645048292647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8563130089437763365528431 12844695134156645048292647)
      ·
        refine ⟨19267042701234967572438971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12844695134156645048292647 19267042701234967572438971)
        ·
          refine ⟨28900564051852451358658457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19267042701234967572438971 28900564051852451358658457)
          ·
            refine ⟨21675423038889338518993843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28900564051852451358658457 21675423038889338518993843)
            ·
              refine ⟨32513134558334007778490765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21675423038889338518993843 32513134558334007778490765)
              ·
                refine ⟨12192425459375252916934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32513134558334007778490765 12192425459375252916934037)
                ·
                  refine ⟨571519943408214980481283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12192425459375252916934037 571519943408214980481283)
                  ·
                    refine ⟨857279915112322470721925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 571519943408214980481283 857279915112322470721925)
                    ·
                      refine ⟨160739984083560463260361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 857279915112322470721925 160739984083560463260361)
                      ·
                        rfl

theorem cell23_313040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_313040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313040 prefixEnd_313040 := by exact prefixLift 313040
  have htrace : WordTrace (prefixWord ++ tailWord_313040) baseStart_313040 baseEnd_313040 := by
    simpa [prefixWord, tailWord_313040, baseEnd_313040] using wordTrace_append hprefix tailTrace_313040
  have hstable : (prefixWord ++ tailWord_313040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313040).length < 2 ^ (prefixWord ++ tailWord_313040).sum := by decide
  have hdescent : baseEnd_313040 < baseStart_313040 := by decide
  rcases family_descends (prefixWord ++ tailWord_313040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313100 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_313100 : Nat := 118140960795 + 313100 * 2 ^ 59
def prefixEnd_313100 : Nat := 4983230072969 + 3 ^ 40 * 313100 * 2
def baseEnd_313100 : Nat := 160770792922830228510085

theorem tailTrace_313100 : CollatzResearch.WordTrace tailWord_313100 prefixEnd_313100 160770792922830228510085 := by
  unfold tailWord_313100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709847582849824033944377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7613130110466432045259169 5709847582849824033944377)
  ·
    refine ⟨4282385687137368025458283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5709847582849824033944377 4282385687137368025458283)
    ·
      refine ⟨6423578530706052038187425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4282385687137368025458283 6423578530706052038187425)
      ·
        refine ⟨4817683898029539028640569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423578530706052038187425 4817683898029539028640569)
        ·
          refine ⟨3613262923522154271480427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4817683898029539028640569 3613262923522154271480427)
          ·
            refine ⟨5419894385283231407220641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613262923522154271480427 5419894385283231407220641)
            ·
              refine ⟨4064920788962423555415481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419894385283231407220641 4064920788962423555415481)
              ·
                refine ⟨3048690591721817666561611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064920788962423555415481 3048690591721817666561611)
                ·
                  refine ⟨4573035887582726499842417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048690591721817666561611 4573035887582726499842417)
                  ·
                    refine ⟨3429776915687044874881813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573035887582726499842417 3429776915687044874881813)
                    ·
                      refine ⟨160770792922830228510085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3429776915687044874881813 160770792922830228510085)
                      ·
                        rfl

theorem cell23_313100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_313100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313100 prefixEnd_313100 := by exact prefixLift 313100
  have htrace : WordTrace (prefixWord ++ tailWord_313100) baseStart_313100 baseEnd_313100 := by
    simpa [prefixWord, tailWord_313100, baseEnd_313100] using wordTrace_append hprefix tailTrace_313100
  have hstable : (prefixWord ++ tailWord_313100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313100).length < 2 ^ (prefixWord ++ tailWord_313100).sum := by decide
  have hdescent : baseEnd_313100 < baseStart_313100 := by decide
  rcases family_descends (prefixWord ++ tailWord_313100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313157 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_313157 : Nat := 118140960795 + 313157 * 2 ^ 59
def prefixEnd_313157 : Nat := 4983230072969 + 3 ^ 40 * 313157 * 2
def baseEnd_313157 : Nat := 53600020440045501832441

theorem tailTrace_313157 : CollatzResearch.WordTrace tailWord_313157 prefixEnd_313157 53600020440045501832441 := by
  unfold tailWord_313157
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421774126493146802713725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7614516084328764535142483 11421774126493146802713725)
  ·
    refine ⟨4283165297434930051017647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11421774126493146802713725 4283165297434930051017647)
    ·
      refine ⟨6424747946152395076526471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283165297434930051017647 6424747946152395076526471)
      ·
        refine ⟨9637121919228592614789707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6424747946152395076526471 9637121919228592614789707)
        ·
          refine ⟨14455682878842888922184561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637121919228592614789707 14455682878842888922184561)
          ·
            refine ⟨10841762159132166691638421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14455682878842888922184561 10841762159132166691638421)
            ·
              refine ⟨508207601209320313670551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10841762159132166691638421 508207601209320313670551)
              ·
                refine ⟨762311401813980470505827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508207601209320313670551 762311401813980470505827)
                ·
                  refine ⟨1143467102720970705758741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762311401813980470505827 1143467102720970705758741)
                  ·
                    refine ⟨53600020440045501832441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1143467102720970705758741 53600020440045501832441)
                    ·
                      rfl

theorem cell23_313157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_313157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313157 prefixEnd_313157 := by exact prefixLift 313157
  have htrace : WordTrace (prefixWord ++ tailWord_313157) baseStart_313157 baseEnd_313157 := by
    simpa [prefixWord, tailWord_313157, baseEnd_313157] using wordTrace_append hprefix tailTrace_313157
  have hstable : (prefixWord ++ tailWord_313157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313157).length < 2 ^ (prefixWord ++ tailWord_313157).sum := by decide
  have hdescent : baseEnd_313157 < baseStart_313157 := by decide
  rcases family_descends (prefixWord ++ tailWord_313157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313158 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_313158 : Nat := 118140960795 + 313158 * 2 ^ 59
def prefixEnd_313158 : Nat := 4983230072969 + 3 ^ 40 * 313158 * 2
def baseEnd_313158 : Nat := 160800574800791001584819

theorem tailTrace_313158 : CollatzResearch.WordTrace tailWord_313158 prefixEnd_313158 160800574800791001584819 := by
  unfold tailWord_313158
  simp only [CollatzResearch.WordTrace]
  refine ⟨356931581234047624171879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7614540399659682649000085 356931581234047624171879)
  ·
    refine ⟨535397371851071436257819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356931581234047624171879 535397371851071436257819)
    ·
      refine ⟨803096057776607154386729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535397371851071436257819 803096057776607154386729)
      ·
        refine ⟨602322043332455365790047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803096057776607154386729 602322043332455365790047)
        ·
          refine ⟨903483064998683048685071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602322043332455365790047 903483064998683048685071)
          ·
            refine ⟨1355224597498024573027607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903483064998683048685071 1355224597498024573027607)
            ·
              refine ⟨2032836896247036859541411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355224597498024573027607 2032836896247036859541411)
              ·
                refine ⟨3049255344370555289312117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032836896247036859541411 3049255344370555289312117)
                ·
                  refine ⟨285867688534739558373011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3049255344370555289312117 285867688534739558373011)
                  ·
                    refine ⟨428801532802109337559517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285867688534739558373011 428801532802109337559517)
                    ·
                      refine ⟨160800574800791001584819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 428801532802109337559517 160800574800791001584819)
                      ·
                        rfl

theorem cell23_313158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_313158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313158 prefixEnd_313158 := by exact prefixLift 313158
  have htrace : WordTrace (prefixWord ++ tailWord_313158) baseStart_313158 baseEnd_313158 := by
    simpa [prefixWord, tailWord_313158, baseEnd_313158] using wordTrace_append hprefix tailTrace_313158
  have hstable : (prefixWord ++ tailWord_313158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313158).length < 2 ^ (prefixWord ++ tailWord_313158).sum := by decide
  have hdescent : baseEnd_313158 < baseStart_313158 := by decide
  rcases family_descends (prefixWord ++ tailWord_313158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313177 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_313177 : Nat := 118140960795 + 313177 * 2 ^ 59
def prefixEnd_313177 : Nat := 4983230072969 + 3 ^ 40 * 313177 * 2
def baseEnd_313177 : Nat := 160810330933226427247231

theorem tailTrace_313177 : CollatzResearch.WordTrace tailWord_313177 prefixEnd_313177 160810330933226427247231 := by
  unfold tailWord_313177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422503586420690218441785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7615002390947126812294523 11422503586420690218441785)
  ·
    refine ⟨8566877689815517663831339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11422503586420690218441785 8566877689815517663831339)
    ·
      refine ⟨12850316534723276495747009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566877689815517663831339 12850316534723276495747009)
      ·
        refine ⟨9637737401042457371810257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12850316534723276495747009 9637737401042457371810257)
        ·
          refine ⟨7228303050781843028857693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9637737401042457371810257 7228303050781843028857693)
          ·
            refine ⟨2710613644043191135821635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7228303050781843028857693 2710613644043191135821635)
            ·
              refine ⟨4065920466064786703732453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710613644043191135821635 4065920466064786703732453)
              ·
                refine ⟨762360087387147506949835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4065920466064786703732453 762360087387147506949835)
                ·
                  refine ⟨1143540131080721260424753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762360087387147506949835 1143540131080721260424753)
                  ·
                    refine ⟨857655098310540945318565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1143540131080721260424753 857655098310540945318565)
                    ·
                      refine ⟨160810330933226427247231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 857655098310540945318565 160810330933226427247231)
                      ·
                        rfl

theorem cell23_313177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_313177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313177 prefixEnd_313177 := by exact prefixLift 313177
  have htrace : WordTrace (prefixWord ++ tailWord_313177) baseStart_313177 baseEnd_313177 := by
    simpa [prefixWord, tailWord_313177, baseEnd_313177] using wordTrace_append hprefix tailTrace_313177
  have hstable : (prefixWord ++ tailWord_313177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313177).length < 2 ^ (prefixWord ++ tailWord_313177).sum := by decide
  have hdescent : baseEnd_313177 < baseStart_313177 := by decide
  rcases family_descends (prefixWord ++ tailWord_313177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313187 : List Nat := [1, 1, 1, 5, 4, 1, 10]
def baseStart_313187 : Nat := 118140960795 + 313187 * 2 ^ 59
def prefixEnd_313187 : Nat := 4983230072969 + 3 ^ 40 * 313187 * 2
def baseEnd_313187 : Nat := 1985376120244091211385

theorem tailTrace_313187 : CollatzResearch.WordTrace tailWord_313187 prefixEnd_313187 1985376120244091211385 := by
  unfold tailWord_313187
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422868316384461926305815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7615245544256307950870543 11422868316384461926305815)
  ·
    refine ⟨17134302474576692889458723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11422868316384461926305815 17134302474576692889458723)
    ·
      refine ⟨25701453711865039334188085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17134302474576692889458723 25701453711865039334188085)
      ·
        refine ⟨2409511285487347437580133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25701453711865039334188085 2409511285487347437580133)
        ·
          refine ⟨451783366028877644546275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2409511285487347437580133 451783366028877644546275)
          ·
            refine ⟨677675049043316466819413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451783366028877644546275 677675049043316466819413)
            ·
              refine ⟨1985376120244091211385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 677675049043316466819413 1985376120244091211385)
              ·
                rfl

theorem cell23_313187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 10].length) (baseStart_313187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313187 prefixEnd_313187 := by exact prefixLift 313187
  have htrace : WordTrace (prefixWord ++ tailWord_313187) baseStart_313187 baseEnd_313187 := by
    simpa [prefixWord, tailWord_313187, baseEnd_313187] using wordTrace_append hprefix tailTrace_313187
  have hstable : (prefixWord ++ tailWord_313187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313187).length < 2 ^ (prefixWord ++ tailWord_313187).sum := by decide
  have hdescent : baseEnd_313187 < baseStart_313187 := by decide
  rcases family_descends (prefixWord ++ tailWord_313187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313198 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_313198 : Nat := 118140960795 + 313198 * 2 ^ 59
def prefixEnd_313198 : Nat := 4983230072969 + 3 ^ 40 * 313198 * 2
def baseEnd_313198 : Nat := 160821114026970845084635

theorem tailTrace_313198 : CollatzResearch.WordTrace tailWord_313198 prefixEnd_313198 160821114026970845084635 := by
  unfold tailWord_313198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427908689918076350619531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7615513012896407203304165 1427908689918076350619531)
  ·
    refine ⟨2141863034877114525929297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427908689918076350619531 2141863034877114525929297)
    ·
      refine ⟨1606397276157835894446973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2141863034877114525929297 1606397276157835894446973)
      ·
        refine ⟨602398978559188460417615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1606397276157835894446973 602398978559188460417615)
        ·
          refine ⟨903598467838782690626423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602398978559188460417615 903598467838782690626423)
          ·
            refine ⟨1355397701758174035939635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903598467838782690626423 1355397701758174035939635)
            ·
              refine ⟨2033096552637261053909453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355397701758174035939635 2033096552637261053909453)
              ·
                refine ⟨762411207238972895216045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2033096552637261053909453 762411207238972895216045)
                ·
                  refine ⟨285904202714614835706017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762411207238972895216045 285904202714614835706017)
                  ·
                    refine ⟨214428152035961126779513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 285904202714614835706017 214428152035961126779513)
                    ·
                      refine ⟨160821114026970845084635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214428152035961126779513 160821114026970845084635)
                      ·
                        rfl

theorem cell23_313198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_313198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313198 prefixEnd_313198 := by exact prefixLift 313198
  have htrace : WordTrace (prefixWord ++ tailWord_313198) baseStart_313198 baseEnd_313198 := by
    simpa [prefixWord, tailWord_313198, baseEnd_313198] using wordTrace_append hprefix tailTrace_313198
  have hstable : (prefixWord ++ tailWord_313198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313198).length < 2 ^ (prefixWord ++ tailWord_313198).sum := by decide
  have hdescent : baseEnd_313198 < baseStart_313198 := by decide
  rcases family_descends (prefixWord ++ tailWord_313198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313238 : List Nat := [5, 3, 1, 1, 2, 2, 9]
def baseStart_313238 : Nat := 118140960795 + 313238 * 2 ^ 59
def prefixEnd_313238 : Nat := 4983230072969 + 3 ^ 40 * 313238 * 2
def baseEnd_313238 : Nat := 1985699422878403562771

theorem tailTrace_313238 : CollatzResearch.WordTrace tailWord_313238 prefixEnd_313238 1985699422878403562771 := by
  unfold tailWord_313238
  simp only [CollatzResearch.WordTrace]
  refine ⟨714045527449981102275773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7616485626133131757608245 714045527449981102275773)
  ·
    refine ⟨267767072793742913353415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 714045527449981102275773 267767072793742913353415)
    ·
      refine ⟨401650609190614370030123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267767072793742913353415 401650609190614370030123)
      ·
        refine ⟨602475913785921555045185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401650609190614370030123 602475913785921555045185)
        ·
          refine ⟨451856935339441166283889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602475913785921555045185 451856935339441166283889)
          ·
            refine ⟨338892701504580874712917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451856935339441166283889 338892701504580874712917)
            ·
              refine ⟨1985699422878403562771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 338892701504580874712917 1985699422878403562771)
              ·
                rfl

theorem cell23_313238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 9].length) (baseStart_313238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313238 prefixEnd_313238 := by exact prefixLift 313238
  have htrace : WordTrace (prefixWord ++ tailWord_313238) baseStart_313238 baseEnd_313238 := by
    simpa [prefixWord, tailWord_313238, baseEnd_313238] using wordTrace_append hprefix tailTrace_313238
  have hstable : (prefixWord ++ tailWord_313238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313238).length < 2 ^ (prefixWord ++ tailWord_313238).sum := by decide
  have hdescent : baseEnd_313238 < baseStart_313238 := by decide
  rcases family_descends (prefixWord ++ tailWord_313238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313241 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 1, 3, 2]
def baseStart_313241 : Nat := 118140960795 + 313241 * 2 ^ 59
def prefixEnd_313241 : Nat := 4983230072969 + 3 ^ 40 * 313241 * 2
def baseEnd_313241 : Nat := 160843193695114176846937

theorem tailTrace_313241 : CollatzResearch.WordTrace tailWord_313241 prefixEnd_313241 160843193695114176846937 := by
  unfold tailWord_313241
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424837858188829148771577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7616558572125886099181051 11424837858188829148771577)
  ·
    refine ⟨8568628393641621861578683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11424837858188829148771577 8568628393641621861578683)
    ·
      refine ⟨12852942590462432792368025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8568628393641621861578683 12852942590462432792368025)
      ·
        refine ⟨9639706942846824594276019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12852942590462432792368025 9639706942846824594276019)
        ·
          refine ⟨14459560414270236891414029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639706942846824594276019 14459560414270236891414029)
          ·
            refine ⟨5422335155351338834280261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14459560414270236891414029 5422335155351338834280261)
            ·
              refine ⟨1016687841628376031427549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5422335155351338834280261 1016687841628376031427549)
              ·
                refine ⟨381257940610641011785331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016687841628376031427549 381257940610641011785331)
                ·
                  refine ⟨571886910915961517677997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381257940610641011785331 571886910915961517677997)
                  ·
                    refine ⟨214457591593485569129249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571886910915961517677997 214457591593485569129249)
                    ·
                      refine ⟨160843193695114176846937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214457591593485569129249 160843193695114176846937)
                      ·
                        rfl

theorem cell23_313241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_313241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313241 prefixEnd_313241 := by exact prefixLift 313241
  have htrace : WordTrace (prefixWord ++ tailWord_313241) baseStart_313241 baseEnd_313241 := by
    simpa [prefixWord, tailWord_313241, baseEnd_313241] using wordTrace_append hprefix tailTrace_313241
  have hstable : (prefixWord ++ tailWord_313241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313241).length < 2 ^ (prefixWord ++ tailWord_313241).sum := by decide
  have hdescent : baseEnd_313241 < baseStart_313241 := by decide
  rcases family_descends (prefixWord ++ tailWord_313241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313265 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_313265 : Nat := 118140960795 + 313265 * 2 ^ 59
def prefixEnd_313265 : Nat := 4983230072969 + 3 ^ 40 * 313265 * 2
def baseEnd_313265 : Nat := 160855517230822082946827

theorem tailTrace_313265 : CollatzResearch.WordTrace tailWord_313265 prefixEnd_313265 160855517230822082946827 := by
  unfold tailWord_313265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425713210101881247645249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7617142140067920831763499 11425713210101881247645249)
  ·
    refine ⟨8569284907576410935733937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11425713210101881247645249 8569284907576410935733937)
    ·
      refine ⟨6426963680682308201800453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8569284907576410935733937 6426963680682308201800453)
      ·
        refine ⟨1205055690127932787837585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6426963680682308201800453 1205055690127932787837585)
        ·
          refine ⟨903791767595949590878189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205055690127932787837585 903791767595949590878189)
          ·
            refine ⟨338921912848481096579321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 903791767595949590878189 338921912848481096579321)
            ·
              refine ⟨254191434636360822434491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338921912848481096579321 254191434636360822434491)
              ·
                refine ⟨381287151954541233651737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254191434636360822434491 381287151954541233651737)
                ·
                  refine ⟨285965363965905925238803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381287151954541233651737 285965363965905925238803)
                  ·
                    refine ⟨428948045948858887858205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285965363965905925238803 428948045948858887858205)
                    ·
                      refine ⟨160855517230822082946827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 428948045948858887858205 160855517230822082946827)
                      ·
                        rfl

theorem cell23_313265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_313265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313265 prefixEnd_313265 := by exact prefixLift 313265
  have htrace : WordTrace (prefixWord ++ tailWord_313265) baseStart_313265 baseEnd_313265 := by
    simpa [prefixWord, tailWord_313265, baseEnd_313265] using wordTrace_append hprefix tailTrace_313265
  have hstable : (prefixWord ++ tailWord_313265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313265).length < 2 ^ (prefixWord ++ tailWord_313265).sum := by decide
  have hdescent : baseEnd_313265 < baseStart_313265 := by decide
  rcases family_descends (prefixWord ++ tailWord_313265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313267 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_313267 : Nat := 118140960795 + 313267 * 2 ^ 59
def prefixEnd_313267 : Nat := 4983230072969 + 3 ^ 40 * 313267 * 2
def baseEnd_313267 : Nat := 160856544192131075121817

theorem tailTrace_313267 : CollatzResearch.WordTrace tailWord_313267 prefixEnd_313267 160856544192131075121817 := by
  unfold tailWord_313267
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425786156094635589218055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7617190770729757059478703 11425786156094635589218055)
  ·
    refine ⟨17138679234141953383827083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11425786156094635589218055 17138679234141953383827083)
    ·
      refine ⟨25708018851212930075740625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17138679234141953383827083 25708018851212930075740625)
      ·
        refine ⟨19281014138409697556805469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25708018851212930075740625 19281014138409697556805469)
        ·
          refine ⟨7230380301903636583802051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19281014138409697556805469 7230380301903636583802051)
          ·
            refine ⟨10845570452855454875703077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7230380301903636583802051 10845570452855454875703077)
            ·
              refine ⟨2033544459910397789194327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10845570452855454875703077 2033544459910397789194327)
              ·
                refine ⟨3050316689865596683791491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033544459910397789194327 3050316689865596683791491)
                ·
                  refine ⟨4575475034798395025687237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050316689865596683791491 4575475034798395025687237)
                  ·
                    refine ⟨857901569024699067316357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575475034798395025687237 857901569024699067316357)
                    ·
                      refine ⟨160856544192131075121817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 857901569024699067316357 160856544192131075121817)
                      ·
                        rfl

theorem cell23_313267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_313267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313267 prefixEnd_313267 := by exact prefixLift 313267
  have htrace : WordTrace (prefixWord ++ tailWord_313267) baseStart_313267 baseEnd_313267 := by
    simpa [prefixWord, tailWord_313267, baseEnd_313267] using wordTrace_append hprefix tailTrace_313267
  have hstable : (prefixWord ++ tailWord_313267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313267).length < 2 ^ (prefixWord ++ tailWord_313267).sum := by decide
  have hdescent : baseEnd_313267 < baseStart_313267 := by decide
  rcases family_descends (prefixWord ++ tailWord_313267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313304 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_313304 : Nat := 118140960795 + 313304 * 2 ^ 59
def prefixEnd_313304 : Nat := 4983230072969 + 3 ^ 40 * 313304 * 2
def baseEnd_313304 : Nat := 160875542976347430359147

theorem tailTrace_313304 : CollatzResearch.WordTrace tailWord_313304 prefixEnd_313304 160875542976347430359147 := by
  unfold tailWord_313304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5713567828480295454157483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7618090437973727272209977 5713567828480295454157483)
  ·
    refine ⟨8570351742720443181236225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5713567828480295454157483 8570351742720443181236225)
    ·
      refine ⟨6427763807040332385927169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8570351742720443181236225 6427763807040332385927169)
      ·
        refine ⟨4820822855280249289445377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6427763807040332385927169 4820822855280249289445377)
        ·
          refine ⟨3615617141460186967084033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4820822855280249289445377 3615617141460186967084033)
          ·
            refine ⟨2711712856095140225313025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615617141460186967084033 2711712856095140225313025)
            ·
              refine ⟨2033784642071355168984769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711712856095140225313025 2033784642071355168984769)
              ·
                refine ⟨1525338481553516376738577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033784642071355168984769 1525338481553516376738577)
                ·
                  refine ⟨1144003861165137282553933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525338481553516376738577 1144003861165137282553933)
                  ·
                    refine ⟨429001447936926480957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144003861165137282553933 429001447936926480957725)
                    ·
                      refine ⟨160875542976347430359147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 429001447936926480957725 160875542976347430359147)
                      ·
                        rfl

theorem cell23_313304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_313304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313304 prefixEnd_313304 := by exact prefixLift 313304
  have htrace : WordTrace (prefixWord ++ tailWord_313304) baseStart_313304 baseEnd_313304 := by
    simpa [prefixWord, tailWord_313304, baseEnd_313304] using wordTrace_append hprefix tailTrace_313304
  have hstable : (prefixWord ++ tailWord_313304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313304).length < 2 ^ (prefixWord ++ tailWord_313304).sum := by decide
  have hdescent : baseEnd_313304 < baseStart_313304 := by decide
  rcases family_descends (prefixWord ++ tailWord_313304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313305 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 2, 2, 2]
def baseStart_313305 : Nat := 118140960795 + 313305 * 2 ^ 59
def prefixEnd_313305 : Nat := 4983230072969 + 3 ^ 40 * 313305 * 2
def baseEnd_313305 : Nat := 160876056457001926446643

theorem tailTrace_313305 : CollatzResearch.WordTrace tailWord_313305 prefixEnd_313305 160876056457001926446643 := by
  unfold tailWord_313305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427172129956968079101369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7618114753304645386067579 11427172129956968079101369)
  ·
    refine ⟨8570379097467726059326027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11427172129956968079101369 8570379097467726059326027)
    ·
      refine ⟨12855568646201589088989041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570379097467726059326027 12855568646201589088989041)
      ·
        refine ⟨9641676484651191816741781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12855568646201589088989041 9641676484651191816741781)
        ·
          refine ⟨451953585218024616409771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9641676484651191816741781 451953585218024616409771)
          ·
            refine ⟨677930377827036924614657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451953585218024616409771 677930377827036924614657)
            ·
              refine ⟨508447783370277693460993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677930377827036924614657 508447783370277693460993)
              ·
                refine ⟨381335837527708270095745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508447783370277693460993 381335837527708270095745)
                ·
                  refine ⟨286001878145781202571809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381335837527708270095745 286001878145781202571809)
                  ·
                    refine ⟨214501408609335901928857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286001878145781202571809 214501408609335901928857)
                    ·
                      refine ⟨160876056457001926446643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214501408609335901928857 160876056457001926446643)
                      ·
                        rfl

theorem cell23_313305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_313305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313305 prefixEnd_313305 := by exact prefixLift 313305
  have htrace : WordTrace (prefixWord ++ tailWord_313305) baseStart_313305 baseEnd_313305 := by
    simpa [prefixWord, tailWord_313305, baseEnd_313305] using wordTrace_append hprefix tailTrace_313305
  have hstable : (prefixWord ++ tailWord_313305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313305).length < 2 ^ (prefixWord ++ tailWord_313305).sum := by decide
  have hdescent : baseEnd_313305 < baseStart_313305 := by decide
  rcases family_descends (prefixWord ++ tailWord_313305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313311 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 5]
def baseStart_313311 : Nat := 118140960795 + 313311 * 2 ^ 59
def prefixEnd_313311 : Nat := 4983230072969 + 3 ^ 40 * 313311 * 2
def baseEnd_313311 : Nat := 17875459704547655885735

theorem tailTrace_313311 : CollatzResearch.WordTrace tailWord_313311 prefixEnd_313311 17875459704547655885735 := by
  unfold tailWord_313311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427390967935231103819787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7618260645290154069213191 11427390967935231103819787)
  ·
    refine ⟨17141086451902846655729681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11427390967935231103819787 17141086451902846655729681)
    ·
      refine ⟨12855814838927134991797261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17141086451902846655729681 12855814838927134991797261)
      ·
        refine ⟨4820930564597675621923973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12855814838927134991797261 4820930564597675621923973)
        ·
          refine ⟨903924480862064179110745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4820930564597675621923973 903924480862064179110745)
          ·
            refine ⟨677943360646548134333059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903924480862064179110745 677943360646548134333059)
            ·
              refine ⟨1016915040969822201499589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677943360646548134333059 1016915040969822201499589)
              ·
                refine ⟨190671570181841662781173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1016915040969822201499589 190671570181841662781173)
                ·
                  refine ⟨17875459704547655885735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190671570181841662781173 17875459704547655885735)
                  ·
                    rfl

theorem cell23_313311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 5].length) (baseStart_313311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313311 prefixEnd_313311 := by exact prefixLift 313311
  have htrace : WordTrace (prefixWord ++ tailWord_313311) baseStart_313311 baseEnd_313311 := by
    simpa [prefixWord, tailWord_313311, baseEnd_313311] using wordTrace_append hprefix tailTrace_313311
  have hstable : (prefixWord ++ tailWord_313311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313311).length < 2 ^ (prefixWord ++ tailWord_313311).sum := by decide
  have hdescent : baseEnd_313311 < baseStart_313311 := by decide
  rcases family_descends (prefixWord ++ tailWord_313311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313344 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_313344 : Nat := 118140960795 + 313344 * 2 ^ 59
def prefixEnd_313344 : Nat := 4983230072969 + 3 ^ 40 * 313344 * 2
def baseEnd_313344 : Nat := 160896082202527273858963

theorem tailTrace_313344 : CollatzResearch.WordTrace tailWord_313344 prefixEnd_313344 160896082202527273858963 := by
  unfold tailWord_313344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5714297288407838869885543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7619063051210451826514057 5714297288407838869885543)
  ·
    refine ⟨8571445932611758304828315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5714297288407838869885543 8571445932611758304828315)
    ·
      refine ⟨12857168898917637457242473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8571445932611758304828315 12857168898917637457242473)
      ·
        refine ⟨9642876674188228092931855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12857168898917637457242473 9642876674188228092931855)
        ·
          refine ⟨14464315011282342139397783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9642876674188228092931855 14464315011282342139397783)
          ·
            refine ⟨21696472516923513209096675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14464315011282342139397783 21696472516923513209096675)
            ·
              refine ⟨32544708775385269813645013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21696472516923513209096675 32544708775385269813645013)
              ·
                refine ⟨762766611923092261257305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32544708775385269813645013 762766611923092261257305)
                ·
                  refine ⟨572074958942319195942979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762766611923092261257305 572074958942319195942979)
                  ·
                    refine ⟨858112438413478793914469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572074958942319195942979 858112438413478793914469)
                    ·
                      refine ⟨160896082202527273858963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 858112438413478793914469 160896082202527273858963)
                      ·
                        rfl

theorem cell23_313344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_313344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313344 prefixEnd_313344 := by exact prefixLift 313344
  have htrace : WordTrace (prefixWord ++ tailWord_313344) baseStart_313344 baseEnd_313344 := by
    simpa [prefixWord, tailWord_313344, baseEnd_313344] using wordTrace_append hprefix tailTrace_313344
  have hstable : (prefixWord ++ tailWord_313344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313344).length < 2 ^ (prefixWord ++ tailWord_313344).sum := by decide
  have hdescent : baseEnd_313344 < baseStart_313344 := by decide
  rcases family_descends (prefixWord ++ tailWord_313344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313398 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_313398 : Nat := 118140960795 + 313398 * 2 ^ 59
def prefixEnd_313398 : Nat := 4983230072969 + 3 ^ 40 * 313398 * 2
def baseEnd_313398 : Nat := 160923810157870062583715

theorem tailTrace_313398 : CollatzResearch.WordTrace tailWord_313398 prefixEnd_313398 160923810157870062583715 := by
  unfold tailWord_313398
  simp only [CollatzResearch.WordTrace]
  refine ⟨714410257413752810139803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7620376079080029974824565 714410257413752810139803)
  ·
    refine ⟨1071615386120629215209705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714410257413752810139803 1071615386120629215209705)
    ·
      refine ⟨803711539590471911407279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071615386120629215209705 803711539590471911407279)
      ·
        refine ⟨1205567309385707867110919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803711539590471911407279 1205567309385707867110919)
        ·
          refine ⟨1808350964078561800666379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205567309385707867110919 1808350964078561800666379)
          ·
            refine ⟨2712526446117842700999569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808350964078561800666379 2712526446117842700999569)
            ·
              refine ⟨2034394834588382025749677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712526446117842700999569 2034394834588382025749677)
              ·
                refine ⟨762898062970643259656129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034394834588382025749677 762898062970643259656129)
                ·
                  refine ⟨572173547227982444742097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762898062970643259656129 572173547227982444742097)
                  ·
                    refine ⟨429130160420986833556573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 572173547227982444742097 429130160420986833556573)
                    ·
                      refine ⟨160923810157870062583715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 429130160420986833556573 160923810157870062583715)
                      ·
                        rfl

theorem cell23_313398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_313398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313398 prefixEnd_313398 := by exact prefixLift 313398
  have htrace : WordTrace (prefixWord ++ tailWord_313398) baseStart_313398 baseEnd_313398 := by
    simpa [prefixWord, tailWord_313398, baseEnd_313398] using wordTrace_append hprefix tailTrace_313398
  have hstable : (prefixWord ++ tailWord_313398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313398).length < 2 ^ (prefixWord ++ tailWord_313398).sum := by decide
  have hdescent : baseEnd_313398 < baseStart_313398 := by decide
  rcases family_descends (prefixWord ++ tailWord_313398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313474 : List Nat := [3, 4, 16]
def baseStart_313474 : Nat := 118140960795 + 313474 * 2 ^ 59
def prefixEnd_313474 : Nat := 4983230072969 + 3 ^ 40 * 313474 * 2
def baseEnd_313474 : Nat := 24533277653956982965

theorem tailTrace_313474 : CollatzResearch.WordTrace tailWord_313474 prefixEnd_313474 24533277653956982965 := by
  unfold tailWord_313474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858334016586177485500869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7622224044229806628002317 2858334016586177485500869)
  ·
    refine ⟨535937628109908278531413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2858334016586177485500869 535937628109908278531413)
    ·
      refine ⟨24533277653956982965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 535937628109908278531413 24533277653956982965)
      ·
        rfl

theorem cell23_313474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 16].length) (baseStart_313474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313474 prefixEnd_313474 := by exact prefixLift 313474
  have htrace : WordTrace (prefixWord ++ tailWord_313474) baseStart_313474 baseEnd_313474 := by
    simpa [prefixWord, tailWord_313474, baseEnd_313474] using wordTrace_append hprefix tailTrace_313474
  have hstable : (prefixWord ++ tailWord_313474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313474).length < 2 ^ (prefixWord ++ tailWord_313474).sum := by decide
  have hdescent : baseEnd_313474 < baseStart_313474 := by decide
  rcases family_descends (prefixWord ++ tailWord_313474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313508 : List Nat := [2, 3, 1, 2, 4, 1, 3, 7]
def baseStart_313508 : Nat := 118140960795 + 313508 * 2 ^ 59
def prefixEnd_313508 : Nat := 4983230072969 + 3 ^ 40 * 313508 * 2
def baseEnd_313508 : Nat := 5962233075180171563267

theorem tailTrace_313508 : CollatzResearch.WordTrace tailWord_313508 prefixEnd_313508 5962233075180171563267 := by
  unfold tailWord_313508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5717288074110766874370589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7623050765481022499160785 5717288074110766874370589)
  ·
    refine ⟨2143983027791537577888971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5717288074110766874370589 2143983027791537577888971)
    ·
      refine ⟨3215974541687306366833457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143983027791537577888971 3215974541687306366833457)
      ·
        refine ⟨2411980906265479775125093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3215974541687306366833457 2411980906265479775125093)
        ·
          refine ⟨452246419924777457835955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2411980906265479775125093 452246419924777457835955)
          ·
            refine ⟨678369629887166186753933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452246419924777457835955 678369629887166186753933)
            ·
              refine ⟨254388611207687320032725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 678369629887166186753933 254388611207687320032725)
              ·
                refine ⟨5962233075180171563267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 254388611207687320032725 5962233075180171563267)
                ·
                  rfl

theorem cell23_313508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 7].length) (baseStart_313508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313508 prefixEnd_313508 := by exact prefixLift 313508
  have htrace : WordTrace (prefixWord ++ tailWord_313508) baseStart_313508 baseEnd_313508 := by
    simpa [prefixWord, tailWord_313508, baseEnd_313508] using wordTrace_append hprefix tailTrace_313508
  have hstable : (prefixWord ++ tailWord_313508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313508).length < 2 ^ (prefixWord ++ tailWord_313508).sum := by decide
  have hdescent : baseEnd_313508 < baseStart_313508 := by decide
  rcases family_descends (prefixWord ++ tailWord_313508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313561 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 3]
def baseStart_313561 : Nat := 118140960795 + 313561 * 2 ^ 59
def prefixEnd_313561 : Nat := 4983230072969 + 3 ^ 40 * 313561 * 2
def baseEnd_313561 : Nat := 161007507504552924845465

theorem tailTrace_313561 : CollatzResearch.WordTrace tailWord_313561 prefixEnd_313561 161007507504552924845465 := by
  unfold tailWord_313561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436509217029523800420537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7624339478019682533613691 11436509217029523800420537)
  ·
    refine ⟨8577381912772142850315403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11436509217029523800420537 8577381912772142850315403)
    ·
      refine ⟨12866072869158214275473105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8577381912772142850315403 12866072869158214275473105)
      ·
        refine ⟨9649554651868660706604829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12866072869158214275473105 9649554651868660706604829)
        ·
          refine ⟨3618582994450747764976811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9649554651868660706604829 3618582994450747764976811)
          ·
            refine ⟨5427874491676121647465217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618582994450747764976811 5427874491676121647465217)
            ·
              refine ⟨4070905868757091235598913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427874491676121647465217 4070905868757091235598913)
              ·
                refine ⟨3053179401567818426699185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4070905868757091235598913 3053179401567818426699185)
                ·
                  refine ⟨2289884551175863820024389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3053179401567818426699185 2289884551175863820024389)
                  ·
                    refine ⟨429353353345474466254573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2289884551175863820024389 429353353345474466254573)
                    ·
                      refine ⟨161007507504552924845465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 429353353345474466254573 161007507504552924845465)
                      ·
                        rfl

theorem cell23_313561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_313561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313561 prefixEnd_313561 := by exact prefixLift 313561
  have htrace : WordTrace (prefixWord ++ tailWord_313561) baseStart_313561 baseEnd_313561 := by
    simpa [prefixWord, tailWord_313561, baseEnd_313561] using wordTrace_append hprefix tailTrace_313561
  have hstable : (prefixWord ++ tailWord_313561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313561).length < 2 ^ (prefixWord ++ tailWord_313561).sum := by decide
  have hdescent : baseEnd_313561 < baseStart_313561 := by decide
  rcases family_descends (prefixWord ++ tailWord_313561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313570 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_313570 : Nat := 118140960795 + 313570 * 2 ^ 59
def prefixEnd_313570 : Nat := 4983230072969 + 3 ^ 40 * 313570 * 2
def baseEnd_313570 : Nat := 161012128830443389632925

theorem tailTrace_313570 : CollatzResearch.WordTrace tailWord_313570 prefixEnd_313570 161012128830443389632925 := by
  unfold tailWord_313570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859209368499229584374541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7624558315997945558332109 2859209368499229584374541)
  ·
    refine ⟨1072203513187211094140453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2859209368499229584374541 1072203513187211094140453)
    ·
      refine ⟨201038158722602080151335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1072203513187211094140453 201038158722602080151335)
      ·
        refine ⟨301557238083903120227003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201038158722602080151335 301557238083903120227003)
        ·
          refine ⟨452335857125854680340505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301557238083903120227003 452335857125854680340505)
          ·
            refine ⟨339251892844391010255379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452335857125854680340505 339251892844391010255379)
            ·
              refine ⟨508877839266586515383069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339251892844391010255379 508877839266586515383069)
              ·
                refine ⟨190829189724969943268651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508877839266586515383069 190829189724969943268651)
                ·
                  refine ⟨286243784587454914902977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190829189724969943268651 286243784587454914902977)
                  ·
                    refine ⟨214682838440591186177233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286243784587454914902977 214682838440591186177233)
                    ·
                      refine ⟨161012128830443389632925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214682838440591186177233 161012128830443389632925)
                      ·
                        rfl

theorem cell23_313570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_313570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313570 prefixEnd_313570 := by exact prefixLift 313570
  have htrace : WordTrace (prefixWord ++ tailWord_313570) baseStart_313570 baseEnd_313570 := by
    simpa [prefixWord, tailWord_313570, baseEnd_313570] using wordTrace_append hprefix tailTrace_313570
  have hstable : (prefixWord ++ tailWord_313570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313570).length < 2 ^ (prefixWord ++ tailWord_313570).sum := by decide
  have hdescent : baseEnd_313570 < baseStart_313570 := by decide
  rcases family_descends (prefixWord ++ tailWord_313570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313609 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 2, 2, 2]
def baseStart_313609 : Nat := 118140960795 + 313609 * 2 ^ 59
def prefixEnd_313609 : Nat := 4983230072969 + 3 ^ 40 * 313609 * 2
def baseEnd_313609 : Nat := 161032154575968737045245

theorem tailTrace_313609 : CollatzResearch.WordTrace tailWord_313609 prefixEnd_313609 161032154575968737045245 := by
  unfold tailWord_313609
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438259920855627998167881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7625506613903751998778587 11438259920855627998167881)
  ·
    refine ⟨8578694940641720998625911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11438259920855627998167881 8578694940641720998625911)
    ·
      refine ⟨12868042410962581497938867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578694940641720998625911 12868042410962581497938867)
      ·
        refine ⟨19302063616443872246908301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12868042410962581497938867 19302063616443872246908301)
        ·
          refine ⟨7238273856166452092590613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19302063616443872246908301 7238273856166452092590613)
          ·
            refine ⟨339294087007802441840185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7238273856166452092590613 339294087007802441840185)
            ·
              refine ⟨254470565255851831380139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339294087007802441840185 254470565255851831380139)
              ·
                refine ⟨381705847883777747070209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254470565255851831380139 381705847883777747070209)
                ·
                  refine ⟨286279385912833310302657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381705847883777747070209 286279385912833310302657)
                  ·
                    refine ⟨214709539434624982726993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286279385912833310302657 214709539434624982726993)
                    ·
                      refine ⟨161032154575968737045245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214709539434624982726993 161032154575968737045245)
                      ·
                        rfl

theorem cell23_313609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 2, 2].length) (baseStart_313609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313609 prefixEnd_313609 := by exact prefixLift 313609
  have htrace : WordTrace (prefixWord ++ tailWord_313609) baseStart_313609 baseEnd_313609 := by
    simpa [prefixWord, tailWord_313609, baseEnd_313609] using wordTrace_append hprefix tailTrace_313609
  have hstable : (prefixWord ++ tailWord_313609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313609).length < 2 ^ (prefixWord ++ tailWord_313609).sum := by decide
  have hdescent : baseEnd_313609 < baseStart_313609 := by decide
  rcases family_descends (prefixWord ++ tailWord_313609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313611 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 4, 5]
def baseStart_313611 : Nat := 118140960795 + 313611 * 2 ^ 59
def prefixEnd_313611 : Nat := 4983230072969 + 3 ^ 40 * 313611 * 2
def baseEnd_313611 : Nat := 53677727179092576406745

theorem tailTrace_313611 : CollatzResearch.WordTrace tailWord_313611 prefixEnd_313611 53677727179092576406745 := by
  unfold tailWord_313611
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438332866848382339740687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7625555244565588226493791 11438332866848382339740687)
  ·
    refine ⟨17157499300272573509611031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11438332866848382339740687 17157499300272573509611031)
    ·
      refine ⟨25736248950408860264416547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17157499300272573509611031 25736248950408860264416547)
      ·
        refine ⟨38604373425613290396624821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25736248950408860264416547 38604373425613290396624821)
        ·
          refine ⟨3619160008651245974683577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38604373425613290396624821 3619160008651245974683577)
          ·
            refine ⟨2714370006488434481012683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619160008651245974683577 2714370006488434481012683)
            ·
              refine ⟨4071555009732651721519025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714370006488434481012683 4071555009732651721519025)
              ·
                refine ⟨3053666257299488791139269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4071555009732651721519025 3053666257299488791139269)
                ·
                  refine ⟨572562423243654148338613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3053666257299488791139269 572562423243654148338613)
                  ·
                    refine ⟨53677727179092576406745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 572562423243654148338613 53677727179092576406745)
                    ·
                      rfl

theorem cell23_313611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 5].length) (baseStart_313611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313611 prefixEnd_313611 := by exact prefixLift 313611
  have htrace : WordTrace (prefixWord ++ tailWord_313611) baseStart_313611 baseEnd_313611 := by
    simpa [prefixWord, tailWord_313611, baseEnd_313611] using wordTrace_append hprefix tailTrace_313611
  have hstable : (prefixWord ++ tailWord_313611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313611).length < 2 ^ (prefixWord ++ tailWord_313611).sum := by decide
  have hdescent : baseEnd_313611 < baseStart_313611 := by decide
  rcases family_descends (prefixWord ++ tailWord_313611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313649 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 5]
def baseStart_313649 : Nat := 118140960795 + 313649 * 2 ^ 59
def prefixEnd_313649 : Nat := 4983230072969 + 3 ^ 40 * 313649 * 2
def baseEnd_313649 : Nat := 17894743755794286727229

theorem tailTrace_313649 : CollatzResearch.WordTrace tailWord_313649 prefixEnd_313649 17894743755794286727229 := by
  unfold tailWord_313649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439718840710714829624001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7626479227140476553082667 11439718840710714829624001)
  ·
    refine ⟨8579789130533036122218001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11439718840710714829624001 8579789130533036122218001)
    ·
      refine ⟨6434841847899777091663501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8579789130533036122218001 6434841847899777091663501)
      ·
        refine ⟨2413065692962416409373813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6434841847899777091663501 2413065692962416409373813)
        ·
          refine ⟨226224908715226538378795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2413065692962416409373813 226224908715226538378795)
          ·
            refine ⟨339337363072839807568193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226224908715226538378795 339337363072839807568193)
            ·
              refine ⟨254503022304629855676145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339337363072839807568193 254503022304629855676145)
              ·
                refine ⟨190877266728472391757109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254503022304629855676145 190877266728472391757109)
                ·
                  refine ⟨17894743755794286727229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190877266728472391757109 17894743755794286727229)
                  ·
                    rfl

theorem cell23_313649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 5].length) (baseStart_313649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313649 prefixEnd_313649 := by exact prefixLift 313649
  have htrace : WordTrace (prefixWord ++ tailWord_313649) baseStart_313649 baseEnd_313649 := by
    simpa [prefixWord, tailWord_313649, baseEnd_313649] using wordTrace_append hprefix tailTrace_313649
  have hstable : (prefixWord ++ tailWord_313649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313649).length < 2 ^ (prefixWord ++ tailWord_313649).sum := by decide
  have hdescent : baseEnd_313649 < baseStart_313649 := by decide
  rcases family_descends (prefixWord ++ tailWord_313649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313651 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_313651 : Nat := 118140960795 + 313651 * 2 ^ 59
def prefixEnd_313651 : Nat := 4983230072969 + 3 ^ 40 * 313651 * 2
def baseEnd_313651 : Nat := 161053720763457572720051

theorem tailTrace_313651 : CollatzResearch.WordTrace tailWord_313651 prefixEnd_313651 161053720763457572720051 := by
  unfold tailWord_313651
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439791786703469171196807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7626527857802312780797871 11439791786703469171196807)
  ·
    refine ⟨17159687680055203756795211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11439791786703469171196807 17159687680055203756795211)
    ·
      refine ⟨25739531520082805635192817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159687680055203756795211 25739531520082805635192817)
      ·
        refine ⟨19304648640062104226394613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25739531520082805635192817 19304648640062104226394613)
        ·
          refine ⟨1809810810005822271224495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19304648640062104226394613 1809810810005822271224495)
          ·
            refine ⟨2714716215008733406836743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809810810005822271224495 2714716215008733406836743)
            ·
              refine ⟨4072074322513100110255115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714716215008733406836743 4072074322513100110255115)
              ·
                refine ⟨6108111483769650165382673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072074322513100110255115 6108111483769650165382673)
                ·
                  refine ⟨4581083612827237624037005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108111483769650165382673 4581083612827237624037005)
                  ·
                    refine ⟨1717906354810214109013877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4581083612827237624037005 1717906354810214109013877)
                    ·
                      refine ⟨161053720763457572720051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1717906354810214109013877 161053720763457572720051)
                      ·
                        rfl

theorem cell23_313651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_313651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313651 prefixEnd_313651 := by exact prefixLift 313651
  have htrace : WordTrace (prefixWord ++ tailWord_313651) baseStart_313651 baseEnd_313651 := by
    simpa [prefixWord, tailWord_313651, baseEnd_313651] using wordTrace_append hprefix tailTrace_313651
  have hstable : (prefixWord ++ tailWord_313651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313651).length < 2 ^ (prefixWord ++ tailWord_313651).sum := by decide
  have hdescent : baseEnd_313651 < baseStart_313651 := by decide
  rcases family_descends (prefixWord ++ tailWord_313651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313685 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_313685 : Nat := 118140960795 + 313685 * 2 ^ 59
def prefixEnd_313685 : Nat := 4983230072969 + 3 ^ 40 * 313685 * 2
def baseEnd_313685 : Nat := 161071179105710439694895

theorem tailTrace_313685 : CollatzResearch.WordTrace tailWord_313685 prefixEnd_313685 161071179105710439694895 := by
  unfold tailWord_313685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11441031868580292977934509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7627354579053528651956339 11441031868580292977934509)
  ·
    refine ⟨4290386950717609866725441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11441031868580292977934509 4290386950717609866725441)
    ·
      refine ⟨3217790213038207400044081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4290386950717609866725441 3217790213038207400044081)
      ·
        refine ⟨2413342659778655550033061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217790213038207400044081 2413342659778655550033061)
        ·
          refine ⟨452501748708497915631199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2413342659778655550033061 452501748708497915631199)
          ·
            refine ⟨678752623062746873446799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452501748708497915631199 678752623062746873446799)
            ·
              refine ⟨1018128934594120310170199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678752623062746873446799 1018128934594120310170199)
              ·
                refine ⟨1527193401891180465255299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018128934594120310170199 1527193401891180465255299)
                ·
                  refine ⟨2290790102836770697882949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527193401891180465255299 2290790102836770697882949)
                  ·
                    refine ⟨429523144281894505853053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290790102836770697882949 429523144281894505853053)
                    ·
                      refine ⟨161071179105710439694895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 429523144281894505853053 161071179105710439694895)
                      ·
                        rfl

theorem cell23_313685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_313685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313685 prefixEnd_313685 := by exact prefixLift 313685
  have htrace : WordTrace (prefixWord ++ tailWord_313685) baseStart_313685 baseEnd_313685 := by
    simpa [prefixWord, tailWord_313685, baseEnd_313685] using wordTrace_append hprefix tailTrace_313685
  have hstable : (prefixWord ++ tailWord_313685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313685).length < 2 ^ (prefixWord ++ tailWord_313685).sum := by decide
  have hdescent : baseEnd_313685 < baseStart_313685 := by decide
  rcases family_descends (prefixWord ++ tailWord_313685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313711 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_313711 : Nat := 118140960795 + 313711 * 2 ^ 59
def prefixEnd_313711 : Nat := 4983230072969 + 3 ^ 40 * 313711 * 2
def baseEnd_313711 : Nat := 161084529602727337969775

theorem tailTrace_313711 : CollatzResearch.WordTrace tailWord_313711 prefixEnd_313711 161084529602727337969775 := by
  unfold tailWord_313711
  simp only [CollatzResearch.WordTrace]
  refine ⟨11441980166486099418380987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7627986777657399612253991 11441980166486099418380987)
  ·
    refine ⟨17162970249729149127571481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11441980166486099418380987 17162970249729149127571481)
    ·
      refine ⟨12872227687296861845678611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17162970249729149127571481 12872227687296861845678611)
      ·
        refine ⟨19308341530945292768517917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872227687296861845678611 19308341530945292768517917)
        ·
          refine ⟨7240628074104484788194219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19308341530945292768517917 7240628074104484788194219)
          ·
            refine ⟨10860942111156727182291329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240628074104484788194219 10860942111156727182291329)
            ·
              refine ⟨8145706583367545386718497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10860942111156727182291329 8145706583367545386718497)
              ·
                refine ⟨6109279937525659040038873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8145706583367545386718497 6109279937525659040038873)
                ·
                  refine ⟨4581959953144244280029155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6109279937525659040038873 4581959953144244280029155)
                  ·
                    refine ⟨6872939929716366420043733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4581959953144244280029155 6872939929716366420043733)
                    ·
                      refine ⟨161084529602727337969775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6872939929716366420043733 161084529602727337969775)
                      ·
                        rfl

theorem cell23_313711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_313711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313711 prefixEnd_313711 := by exact prefixLift 313711
  have htrace : WordTrace (prefixWord ++ tailWord_313711) baseStart_313711 baseEnd_313711 := by
    simpa [prefixWord, tailWord_313711, baseEnd_313711] using wordTrace_append hprefix tailTrace_313711
  have hstable : (prefixWord ++ tailWord_313711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313711).length < 2 ^ (prefixWord ++ tailWord_313711).sum := by decide
  have hdescent : baseEnd_313711 < baseStart_313711 := by decide
  rcases family_descends (prefixWord ++ tailWord_313711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313725 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_313725 : Nat := 118140960795 + 313725 * 2 ^ 59
def prefixEnd_313725 : Nat := 4983230072969 + 3 ^ 40 * 313725 * 2
def baseEnd_313725 : Nat := 161091718331890283194711

theorem tailTrace_313725 : CollatzResearch.WordTrace tailWord_313725 prefixEnd_313725 161091718331890283194711 := by
  unfold tailWord_313725
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442490788435379809390629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7628327192290253206260419 11442490788435379809390629)
  ·
    refine ⟨2145467022831633714260743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11442490788435379809390629 2145467022831633714260743)
    ·
      refine ⟨3218200534247450571391115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145467022831633714260743 3218200534247450571391115)
      ·
        refine ⟨4827300801371175857086673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218200534247450571391115 4827300801371175857086673)
        ·
          refine ⟨3620475601028381892815005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827300801371175857086673 3620475601028381892815005)
          ·
            refine ⟨1357678350385643209805627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3620475601028381892815005 1357678350385643209805627)
            ·
              refine ⟨2036517525578464814708441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357678350385643209805627 2036517525578464814708441)
              ·
                refine ⟨1527388144183848611031331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036517525578464814708441 1527388144183848611031331)
                ·
                  refine ⟨2291082216275772916546997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527388144183848611031331 2291082216275772916546997)
                  ·
                    refine ⟨214788957775853710926281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2291082216275772916546997 214788957775853710926281)
                    ·
                      refine ⟨161091718331890283194711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214788957775853710926281 161091718331890283194711)
                      ·
                        rfl

theorem cell23_313725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_313725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313725 prefixEnd_313725 := by exact prefixLift 313725
  have htrace : WordTrace (prefixWord ++ tailWord_313725) baseStart_313725 baseEnd_313725 := by
    simpa [prefixWord, tailWord_313725, baseEnd_313725] using wordTrace_append hprefix tailTrace_313725
  have hstable : (prefixWord ++ tailWord_313725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313725).length < 2 ^ (prefixWord ++ tailWord_313725).sum := by decide
  have hdescent : baseEnd_313725 < baseStart_313725 := by decide
  rcases family_descends (prefixWord ++ tailWord_313725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313735 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 1, 5]
def baseStart_313735 : Nat := 118140960795 + 313735 * 2 ^ 59
def prefixEnd_313735 : Nat := 4983230072969 + 3 ^ 40 * 313735 * 2
def baseEnd_313735 : Nat := 53698951046145081356555

theorem tailTrace_313735 : CollatzResearch.WordTrace tailWord_313735 prefixEnd_313735 53698951046145081356555 := by
  unfold tailWord_313735
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442855518399151517254659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7628570345599434344836439 11442855518399151517254659)
  ·
    refine ⟨17164283277598727275881989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442855518399151517254659 17164283277598727275881989)
    ·
      refine ⟨3218303114549761364227873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17164283277598727275881989 3218303114549761364227873)
      ·
        refine ⟨2413727335912321023170905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3218303114549761364227873 2413727335912321023170905)
        ·
          refine ⟨1810295501934240767378179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413727335912321023170905 1810295501934240767378179)
          ·
            refine ⟨2715443252901361151067269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810295501934240767378179 2715443252901361151067269)
            ·
              refine ⟨509145609919005215825113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2715443252901361151067269 509145609919005215825113)
              ·
                refine ⟨381859207439253911868835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509145609919005215825113 381859207439253911868835)
                ·
                  refine ⟨572788811158880867803253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381859207439253911868835 572788811158880867803253)
                  ·
                    refine ⟨53698951046145081356555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 572788811158880867803253 53698951046145081356555)
                    ·
                      rfl

theorem cell23_313735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_313735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313735 prefixEnd_313735 := by exact prefixLift 313735
  have htrace : WordTrace (prefixWord ++ tailWord_313735) baseStart_313735 baseEnd_313735 := by
    simpa [prefixWord, tailWord_313735, baseEnd_313735] using wordTrace_append hprefix tailTrace_313735
  have hstable : (prefixWord ++ tailWord_313735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313735).length < 2 ^ (prefixWord ++ tailWord_313735).sum := by decide
  have hdescent : baseEnd_313735 < baseStart_313735 := by decide
  rcases family_descends (prefixWord ++ tailWord_313735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313742 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_313742 : Nat := 118140960795 + 313742 * 2 ^ 59
def prefixEnd_313742 : Nat := 4983230072969 + 3 ^ 40 * 313742 * 2
def baseEnd_313742 : Nat := 161100447503016716682133

theorem tailTrace_313742 : CollatzResearch.WordTrace tailWord_313742 prefixEnd_313742 161100447503016716682133 := by
  unfold tailWord_313742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430388853671723964094935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7628740552915861141839653 1430388853671723964094935)
  ·
    refine ⟨2145583280507585946142403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430388853671723964094935 2145583280507585946142403)
    ·
      refine ⟨3218374920761378919213605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145583280507585946142403 3218374920761378919213605)
      ·
        refine ⟨603445297642758547352551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3218374920761378919213605 603445297642758547352551)
        ·
          refine ⟨905167946464137821028827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603445297642758547352551 905167946464137821028827)
          ·
            refine ⟨1357751919696206731543241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905167946464137821028827 1357751919696206731543241)
            ·
              refine ⟨1018313939772155048657431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357751919696206731543241 1018313939772155048657431)
              ·
                refine ⟨1527470909658232572986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018313939772155048657431 1527470909658232572986147)
                ·
                  refine ⟨2291206364487348859479221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527470909658232572986147 2291206364487348859479221)
                  ·
                    refine ⟨214800596670688955576177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2291206364487348859479221 214800596670688955576177)
                    ·
                      refine ⟨161100447503016716682133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214800596670688955576177 161100447503016716682133)
                      ·
                        rfl

theorem cell23_313742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_313742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313742 prefixEnd_313742 := by exact prefixLift 313742
  have htrace : WordTrace (prefixWord ++ tailWord_313742) baseStart_313742 baseEnd_313742 := by
    simpa [prefixWord, tailWord_313742, baseEnd_313742] using wordTrace_append hprefix tailTrace_313742
  have hstable : (prefixWord ++ tailWord_313742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313742).length < 2 ^ (prefixWord ++ tailWord_313742).sum := by decide
  have hdescent : baseEnd_313742 < baseStart_313742 := by decide
  rcases family_descends (prefixWord ++ tailWord_313742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313765 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_313765 : Nat := 118140960795 + 313765 * 2 ^ 59
def prefixEnd_313765 : Nat := 4983230072969 + 3 ^ 40 * 313765 * 2
def baseEnd_313765 : Nat := 53704085852690042231509

theorem tailTrace_313765 : CollatzResearch.WordTrace tailWord_313765 prefixEnd_313765 53704085852690042231509 := by
  unfold tailWord_313765
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443949708290466640846749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7629299805526977760564499 11443949708290466640846749)
  ·
    refine ⟨4291481140608924990317531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11443949708290466640846749 4291481140608924990317531)
    ·
      refine ⟨6437221710913387485476297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4291481140608924990317531 6437221710913387485476297)
      ·
        refine ⟨4827916283185040614107223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437221710913387485476297 4827916283185040614107223)
        ·
          refine ⟨7241874424777560921160835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827916283185040614107223 7241874424777560921160835)
          ·
            refine ⟨10862811637166341381741253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7241874424777560921160835 10862811637166341381741253)
            ·
              refine ⟨2036777181968689009076485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10862811637166341381741253 2036777181968689009076485)
              ·
                refine ⟨381895721619129189201841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2036777181968689009076485 381895721619129189201841)
                ·
                  refine ⟨286421791214346891901381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381895721619129189201841 286421791214346891901381)
                  ·
                    refine ⟨53704085852690042231509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286421791214346891901381 53704085852690042231509)
                    ·
                      rfl

theorem cell23_313765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_313765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313765 prefixEnd_313765 := by exact prefixLift 313765
  have htrace : WordTrace (prefixWord ++ tailWord_313765) baseStart_313765 baseEnd_313765 := by
    simpa [prefixWord, tailWord_313765, baseEnd_313765] using wordTrace_append hprefix tailTrace_313765
  have hstable : (prefixWord ++ tailWord_313765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313765).length < 2 ^ (prefixWord ++ tailWord_313765).sum := by decide
  have hdescent : baseEnd_313765 < baseStart_313765 := by decide
  rcases family_descends (prefixWord ++ tailWord_313765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313778 : List Nat := [3, 2, 1, 1, 1, 1, 6, 8]
def baseStart_313778 : Nat := 118140960795 + 313778 * 2 ^ 59
def prefixEnd_313778 : Nat := 4983230072969 + 3 ^ 40 * 313778 * 2
def baseEnd_313778 : Nat := 5967367881725132438221

theorem tailTrace_313778 : CollatzResearch.WordTrace tailWord_313778 prefixEnd_313778 5967367881725132438221 := by
  unfold tailWord_313778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861105964310842465267497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7629615904828913240713325 2861105964310842465267497)
  ·
    refine ⟨2145829473233131848950623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2861105964310842465267497 2145829473233131848950623)
    ·
      refine ⟨3218744209849697773425935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145829473233131848950623 3218744209849697773425935)
      ·
        refine ⟨4828116314774546660138903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218744209849697773425935 4828116314774546660138903)
        ·
          refine ⟨7242174472161819990208355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4828116314774546660138903 7242174472161819990208355)
          ·
            refine ⟨10863261708242729985312533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242174472161819990208355 10863261708242729985312533)
            ·
              refine ⟨509215392573877968061525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10863261708242729985312533 509215392573877968061525)
              ·
                refine ⟨5967367881725132438221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 509215392573877968061525 5967367881725132438221)
                ·
                  rfl

theorem cell23_313778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_313778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313778 prefixEnd_313778 := by exact prefixLift 313778
  have htrace : WordTrace (prefixWord ++ tailWord_313778) baseStart_313778 baseEnd_313778 := by
    simpa [prefixWord, tailWord_313778, baseEnd_313778] using wordTrace_append hprefix tailTrace_313778
  have hstable : (prefixWord ++ tailWord_313778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313778).length < 2 ^ (prefixWord ++ tailWord_313778).sum := by decide
  have hdescent : baseEnd_313778 < baseStart_313778 := by decide
  rcases family_descends (prefixWord ++ tailWord_313778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313793 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_313793 : Nat := 118140960795 + 313793 * 2 ^ 59
def prefixEnd_313793 : Nat := 4983230072969 + 3 ^ 40 * 313793 * 2
def baseEnd_313793 : Nat := 161126635016396017144399

theorem tailTrace_313793 : CollatzResearch.WordTrace tailWord_313793 prefixEnd_313793 161126635016396017144399 := by
  unfold tailWord_313793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444970952189027422866033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7629980634792684948577355 11444970952189027422866033)
  ·
    refine ⟨8583728214141770567149525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11444970952189027422866033 8583728214141770567149525)
    ·
      refine ⟨201181130018947747667567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8583728214141770567149525 201181130018947747667567)
      ·
        refine ⟨301771695028421621501351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201181130018947747667567 301771695028421621501351)
        ·
          refine ⟨452657542542632432252027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301771695028421621501351 452657542542632432252027)
          ·
            refine ⟨678986313813948648378041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452657542542632432252027 678986313813948648378041)
            ·
              refine ⟨509239735360461486283531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678986313813948648378041 509239735360461486283531)
              ·
                refine ⟨763859603040692229425297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509239735360461486283531 763859603040692229425297)
                ·
                  refine ⟨572894702280519172068973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763859603040692229425297 572894702280519172068973)
                  ·
                    refine ⟨214835513355194689525865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572894702280519172068973 214835513355194689525865)
                    ·
                      refine ⟨161126635016396017144399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214835513355194689525865 161126635016396017144399)
                      ·
                        rfl

theorem cell23_313793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_313793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313793 prefixEnd_313793 := by exact prefixLift 313793
  have htrace : WordTrace (prefixWord ++ tailWord_313793) baseStart_313793 baseEnd_313793 := by
    simpa [prefixWord, tailWord_313793, baseEnd_313793] using wordTrace_append hprefix tailTrace_313793
  have hstable : (prefixWord ++ tailWord_313793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313793).length < 2 ^ (prefixWord ++ tailWord_313793).sum := by decide
  have hdescent : baseEnd_313793 < baseStart_313793 := by decide
  rcases family_descends (prefixWord ++ tailWord_313793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
