import V185TrunkScan22Chunk455

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4065546 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_4065546 : Nat := 118140960795 + 4065546 * 2 ^ 59
def prefixEnd_4065546 : Nat := 4983230072969 + 3 ^ 40 * 4065546 * 2
def baseEnd_4065546 : Nat := 1391719480642703844185267

theorem tailTrace_4065546 : CollatzResearch.WordTrace tailWord_4065546 prefixEnd_4065546 1391719480642703844185267 := by
  unfold tailWord_4065546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070661132307164205670123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98855096352819104548453661 37070661132307164205670123)
  ·
    refine ⟨55605991698460746308505185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37070661132307164205670123 55605991698460746308505185)
    ·
      refine ⟨41704493773845559731378889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55605991698460746308505185 41704493773845559731378889)
      ·
        refine ⟨31278370330384169798534167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41704493773845559731378889 31278370330384169798534167)
        ·
          refine ⟨46917555495576254697801251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31278370330384169798534167 46917555495576254697801251)
          ·
            refine ⟨70376333243364382046701877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46917555495576254697801251 70376333243364382046701877)
            ·
              refine ⟨6597781241565410816878301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70376333243364382046701877 6597781241565410816878301)
              ·
                refine ⟨2474167965587029056329363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6597781241565410816878301 2474167965587029056329363)
                ·
                  refine ⟨3711251948380543584494045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474167965587029056329363 3711251948380543584494045)
                  ·
                    refine ⟨1391719480642703844185267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711251948380543584494045 1391719480642703844185267)
                    ·
                      rfl

theorem cell22_4065546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_4065546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065546 prefixEnd_4065546 := by exact prefixLift 4065546
  have htrace : WordTrace (prefixWord ++ tailWord_4065546) baseStart_4065546 baseEnd_4065546 := by
    simpa [prefixWord, tailWord_4065546, baseEnd_4065546] using wordTrace_append hprefix tailTrace_4065546
  have hstable : (prefixWord ++ tailWord_4065546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065546).length < 2 ^ (prefixWord ++ tailWord_4065546).sum := by decide
  have hdescent : baseEnd_4065546 < baseStart_4065546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065621 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 4]
def baseStart_4065621 : Nat := 118140960795 + 4065621 * 2 ^ 59
def prefixEnd_4065621 : Nat := 4983230072969 + 3 ^ 40 * 4065621 * 2
def baseEnd_4065621 : Nat := 463915051558476216186679

theorem tailTrace_4065621 : CollatzResearch.WordTrace tailWord_4065621 prefixEnd_4065621 463915051558476216186679 := by
  unfold tailWord_4065621
  simp only [CollatzResearch.WordTrace]
  refine ⟨148285380003956944631660717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98856920002637963087773811 148285380003956944631660717)
  ·
    refine ⟨55607017501483854236872769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148285380003956944631660717 55607017501483854236872769)
    ·
      refine ⟨41705263126112890677654577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55607017501483854236872769 41705263126112890677654577)
      ·
        refine ⟨31278947344584668008240933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41705263126112890677654577 31278947344584668008240933)
        ·
          refine ⟨5864802627109625251545175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31278947344584668008240933 5864802627109625251545175)
          ·
            refine ⟨8797203940664437877317763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864802627109625251545175 8797203940664437877317763)
            ·
              refine ⟨13195805910996656815976645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8797203940664437877317763 13195805910996656815976645)
              ·
                refine ⟨2474213608311873152995621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13195805910996656815976645 2474213608311873152995621)
                ·
                  refine ⟨463915051558476216186679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474213608311873152995621 463915051558476216186679)
                  ·
                    rfl

theorem cell22_4065621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_4065621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065621 prefixEnd_4065621 := by exact prefixLift 4065621
  have htrace : WordTrace (prefixWord ++ tailWord_4065621) baseStart_4065621 baseEnd_4065621 := by
    simpa [prefixWord, tailWord_4065621, baseEnd_4065621] using wordTrace_append hprefix tailTrace_4065621
  have hstable : (prefixWord ++ tailWord_4065621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065621).length < 2 ^ (prefixWord ++ tailWord_4065621).sum := by decide
  have hdescent : baseEnd_4065621 < baseStart_4065621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065666 : List Nat := [3, 4, 2, 1, 2, 1, 9]
def baseStart_4065666 : Nat := 118140960795 + 4065666 * 2 ^ 59
def prefixEnd_4065666 : Nat := 4983230072969 + 3 ^ 40 * 4065666 * 2
def baseEnd_4065666 : Nat := 51546687373891241895737

theorem tailTrace_4065666 : CollatzResearch.WordTrace tailWord_4065666 prefixEnd_4065666 51546687373891241895737 := by
  unfold tailWord_4065666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37071755322198479329262213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98858014192529278211365901 37071755322198479329262213)
  ·
    refine ⟨6950954122912214874236665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37071755322198479329262213 6950954122912214874236665)
    ·
      refine ⟨5213215592184161155677499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6950954122912214874236665 5213215592184161155677499)
      ·
        refine ⟨7819823388276241733516249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213215592184161155677499 7819823388276241733516249)
        ·
          refine ⟨5864867541207181300137187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7819823388276241733516249 5864867541207181300137187)
          ·
            refine ⟨8797301311810771950205781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864867541207181300137187 8797301311810771950205781)
            ·
              refine ⟨51546687373891241895737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8797301311810771950205781 51546687373891241895737)
              ·
                rfl

theorem cell22_4065666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 9].length) (baseStart_4065666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065666 prefixEnd_4065666 := by exact prefixLift 4065666
  have htrace : WordTrace (prefixWord ++ tailWord_4065666) baseStart_4065666 baseEnd_4065666 := by
    simpa [prefixWord, tailWord_4065666, baseEnd_4065666] using wordTrace_append hprefix tailTrace_4065666
  have hstable : (prefixWord ++ tailWord_4065666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065666).length < 2 ^ (prefixWord ++ tailWord_4065666).sum := by decide
  have hdescent : baseEnd_4065666 < baseStart_4065666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065722 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_4065722 : Nat := 118140960795 + 4065722 * 2 ^ 59
def prefixEnd_4065722 : Nat := 4983230072969 + 3 ^ 40 * 4065722 * 2
def baseEnd_4065722 : Nat := 463926576346499350594909

theorem tailTrace_4065722 : CollatzResearch.WordTrace tailWord_4065722 prefixEnd_4065722 463926576346499350594909 := by
  unfold tailWord_4065722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37072265944147759720271855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98859375851060692587391613 37072265944147759720271855)
  ·
    refine ⟨55608398916221639580407783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37072265944147759720271855 55608398916221639580407783)
    ·
      refine ⟨83412598374332459370611675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55608398916221639580407783 83412598374332459370611675)
      ·
        refine ⟨125118897561498689055917513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83412598374332459370611675 125118897561498689055917513)
        ·
          refine ⟨93839173171124016791938135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125118897561498689055917513 93839173171124016791938135)
          ·
            refine ⟨140758759756686025187907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93839173171124016791938135 140758759756686025187907203)
            ·
              refine ⟨211138139635029037781860805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140758759756686025187907203 211138139635029037781860805)
              ·
                refine ⟨39588401181567944584098901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211138139635029037781860805 39588401181567944584098901)
                ·
                  refine ⟨463926576346499350594909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39588401181567944584098901 463926576346499350594909)
                  ·
                    rfl

theorem cell22_4065722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_4065722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065722 prefixEnd_4065722 := by exact prefixLift 4065722
  have htrace : WordTrace (prefixWord ++ tailWord_4065722) baseStart_4065722 baseEnd_4065722 := by
    simpa [prefixWord, tailWord_4065722, baseEnd_4065722] using wordTrace_append hprefix tailTrace_4065722
  have hstable : (prefixWord ++ tailWord_4065722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065722).length < 2 ^ (prefixWord ++ tailWord_4065722).sum := by decide
  have hdescent : baseEnd_4065722 < baseStart_4065722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065732 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4065732 : Nat := 118140960795 + 4065732 * 2 ^ 59
def prefixEnd_4065732 : Nat := 4983230072969 + 3 ^ 40 * 4065732 * 2
def baseEnd_4065732 : Nat := 1391783152243861359034697

theorem tailTrace_4065732 : CollatzResearch.WordTrace tailWord_4065732 prefixEnd_4065732 1391783152243861359034697 := by
  unfold tailWord_4065732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74144714253277405294475725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98859619004369873725967633 74144714253277405294475725)
  ·
    refine ⟨27804267844979026985428397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74144714253277405294475725 27804267844979026985428397)
    ·
      refine ⟨10426600441867135119535649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27804267844979026985428397 10426600441867135119535649)
      ·
        refine ⟨7819950331400351339651737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10426600441867135119535649 7819950331400351339651737)
        ·
          refine ⟨5864962748550263504738803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7819950331400351339651737 5864962748550263504738803)
          ·
            refine ⟨8797444122825395257108205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864962748550263504738803 8797444122825395257108205)
            ·
              refine ⟨3299041546059523221415577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8797444122825395257108205 3299041546059523221415577)
              ·
                refine ⟨2474281159544642416061683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299041546059523221415577 2474281159544642416061683)
                ·
                  refine ⟨3711421739316963624092525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474281159544642416061683 3711421739316963624092525)
                  ·
                    refine ⟨1391783152243861359034697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711421739316963624092525 1391783152243861359034697)
                    ·
                      rfl

theorem cell22_4065732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4065732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065732 prefixEnd_4065732 := by exact prefixLift 4065732
  have htrace : WordTrace (prefixWord ++ tailWord_4065732) baseStart_4065732 baseEnd_4065732 := by
    simpa [prefixWord, tailWord_4065732, baseEnd_4065732] using wordTrace_append hprefix tailTrace_4065732
  have hstable : (prefixWord ++ tailWord_4065732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065732).length < 2 ^ (prefixWord ++ tailWord_4065732).sum := by decide
  have hdescent : baseEnd_4065732 < baseStart_4065732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065754 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_4065754 : Nat := 118140960795 + 4065754 * 2 ^ 59
def prefixEnd_4065754 : Nat := 4983230072969 + 3 ^ 40 * 4065754 * 2
def baseEnd_4065754 : Nat := 1391790683293460634984629

theorem tailTrace_4065754 : CollatzResearch.WordTrace tailWord_4065754 prefixEnd_4065754 1391790683293460634984629 := by
  unfold tailWord_4065754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37072557728118777086563079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98860153941650072230834877 37072557728118777086563079)
  ·
    refine ⟨55608836592178165629844619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37072557728118777086563079 55608836592178165629844619)
    ·
      refine ⟨83413254888267248444766929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55608836592178165629844619 83413254888267248444766929)
      ·
        refine ⟨62559941166200436333575197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83413254888267248444766929 62559941166200436333575197)
        ·
          refine ⟨23459977937325163625090699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62559941166200436333575197 23459977937325163625090699)
          ·
            refine ⟨35189966905987745437636049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23459977937325163625090699 35189966905987745437636049)
            ·
              refine ⟨26392475179490809078227037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35189966905987745437636049 26392475179490809078227037)
              ·
                refine ⟨9897178192309053404335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26392475179490809078227037 9897178192309053404335139)
                ·
                  refine ⟨14845767288463580106502709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897178192309053404335139 14845767288463580106502709)
                  ·
                    refine ⟨1391790683293460634984629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14845767288463580106502709 1391790683293460634984629)
                    ·
                      rfl

theorem cell22_4065754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_4065754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065754 prefixEnd_4065754 := by exact prefixLift 4065754
  have htrace : WordTrace (prefixWord ++ tailWord_4065754) baseStart_4065754 baseEnd_4065754 := by
    simpa [prefixWord, tailWord_4065754, baseEnd_4065754] using wordTrace_append hprefix tailTrace_4065754
  have hstable : (prefixWord ++ tailWord_4065754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065754).length < 2 ^ (prefixWord ++ tailWord_4065754).sum := by decide
  have hdescent : baseEnd_4065754 < baseStart_4065754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065805 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4065805 : Nat := 118140960795 + 4065805 * 2 ^ 59
def prefixEnd_4065805 : Nat := 4983230072969 + 3 ^ 40 * 4065805 * 2
def baseEnd_4065805 : Nat := 1391808141635713501959473

theorem tailTrace_4065805 : CollatzResearch.WordTrace tailWord_4065805 prefixEnd_4065805 1391808141635713501959473 := by
  unfold tailWord_4065805
  simp only [CollatzResearch.WordTrace]
  refine ⟨148292091035290344056358869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98861394023526896037572579 148292091035290344056358869)
  ·
    refine ⟨3475595883639617438820911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 148292091035290344056358869 3475595883639617438820911)
    ·
      refine ⟨5213393825459426158231367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475595883639617438820911 5213393825459426158231367)
      ·
        refine ⟨7820090738189139237347051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5213393825459426158231367 7820090738189139237347051)
        ·
          refine ⟨11730136107283708856020577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820090738189139237347051 11730136107283708856020577)
          ·
            refine ⟨8797602080462781642015433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11730136107283708856020577 8797602080462781642015433)
            ·
              refine ⟨6598201560347086231511575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8797602080462781642015433 6598201560347086231511575)
              ·
                refine ⟨9897302340520629347267363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598201560347086231511575 9897302340520629347267363)
                ·
                  refine ⟨14845953510780944020901045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897302340520629347267363 14845953510780944020901045)
                  ·
                    refine ⟨1391808141635713501959473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14845953510780944020901045 1391808141635713501959473)
                    ·
                      rfl

theorem cell22_4065805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4065805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065805 prefixEnd_4065805 := by exact prefixLift 4065805
  have htrace : WordTrace (prefixWord ++ tailWord_4065805) baseStart_4065805 baseEnd_4065805 := by
    simpa [prefixWord, tailWord_4065805, baseEnd_4065805] using wordTrace_append hprefix tailTrace_4065805
  have hstable : (prefixWord ++ tailWord_4065805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065805).length < 2 ^ (prefixWord ++ tailWord_4065805).sum := by decide
  have hdescent : baseEnd_4065805 < baseStart_4065805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065816 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_4065816 : Nat := 118140960795 + 4065816 * 2 ^ 59
def prefixEnd_4065816 : Nat := 4983230072969 + 3 ^ 40 * 4065816 * 2
def baseEnd_4065816 : Nat := 1391811907160513139934439

theorem tailTrace_4065816 : CollatzResearch.WordTrace tailWord_4065816 prefixEnd_4065816 1391811907160513139934439 := by
  unfold tailWord_4065816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74146246119125246467504651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98861661492166995290006201 74146246119125246467504651)
  ·
    refine ⟨111219369178687869701256977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74146246119125246467504651 111219369178687869701256977)
    ·
      refine ⟨83414526884015902275942733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111219369178687869701256977 83414526884015902275942733)
      ·
        refine ⟨31280447581505963353478525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83414526884015902275942733 31280447581505963353478525)
        ·
          refine ⟨11730167843064736257554447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31280447581505963353478525 11730167843064736257554447)
          ·
            refine ⟨17595251764597104386331671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730167843064736257554447 17595251764597104386331671)
            ·
              refine ⟨26392877646895656579497507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595251764597104386331671 26392877646895656579497507)
              ·
                refine ⟨39589316470343484869246261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26392877646895656579497507 39589316470343484869246261)
                ·
                  refine ⟨3711498419094701706491837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39589316470343484869246261 3711498419094701706491837)
                  ·
                    refine ⟨1391811907160513139934439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711498419094701706491837 1391811907160513139934439)
                    ·
                      rfl

theorem cell22_4065816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_4065816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065816 prefixEnd_4065816 := by exact prefixLift 4065816
  have htrace : WordTrace (prefixWord ++ tailWord_4065816) baseStart_4065816 baseEnd_4065816 := by
    simpa [prefixWord, tailWord_4065816, baseEnd_4065816] using wordTrace_append hprefix tailTrace_4065816
  have hstable : (prefixWord ++ tailWord_4065816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065816).length < 2 ^ (prefixWord ++ tailWord_4065816).sum := by decide
  have hdescent : baseEnd_4065816 < baseStart_4065816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065859 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_4065859 : Nat := 118140960795 + 4065859 * 2 ^ 59
def prefixEnd_4065859 : Nat := 4983230072969 + 3 ^ 40 * 4065859 * 2
def baseEnd_4065859 : Nat := 1391826626939275361109307

theorem tailTrace_4065859 : CollatzResearch.WordTrace tailWord_4065859 prefixEnd_4065859 1391826626939275361109307 := by
  unfold tailWord_4065859
  simp only [CollatzResearch.WordTrace]
  refine ⟨148294060577094711278824631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98862707051396474185883087 148294060577094711278824631)
  ·
    refine ⟨222441090865642066918236947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148294060577094711278824631 222441090865642066918236947)
    ·
      refine ⟨333661636298463100377355421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222441090865642066918236947 333661636298463100377355421)
      ·
        refine ⟨125123113611923662641508283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333661636298463100377355421 125123113611923662641508283)
        ·
          refine ⟨187684670417885493962262425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125123113611923662641508283 187684670417885493962262425)
          ·
            refine ⟨140763502813414120471696819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187684670417885493962262425 140763502813414120471696819)
            ·
              refine ⟨211145254220121180707545229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140763502813414120471696819 211145254220121180707545229)
              ·
                refine ⟨79179470332545442765329461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211145254220121180707545229 79179470332545442765329461)
                ·
                  refine ⟨7423075343676135259249637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79179470332545442765329461 7423075343676135259249637)
                  ·
                    refine ⟨1391826626939275361109307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423075343676135259249637 1391826626939275361109307)
                    ·
                      rfl

theorem cell22_4065859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_4065859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065859 prefixEnd_4065859 := by exact prefixLift 4065859
  have htrace : WordTrace (prefixWord ++ tailWord_4065859) baseStart_4065859 baseEnd_4065859 := by
    simpa [prefixWord, tailWord_4065859, baseEnd_4065859] using wordTrace_append hprefix tailTrace_4065859
  have hstable : (prefixWord ++ tailWord_4065859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065859).length < 2 ^ (prefixWord ++ tailWord_4065859).sum := by decide
  have hdescent : baseEnd_4065859 < baseStart_4065859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065863 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 5]
def baseStart_4065863 : Nat := 118140960795 + 4065863 * 2 ^ 59
def prefixEnd_4065863 : Nat := 4983230072969 + 3 ^ 40 * 4065863 * 2
def baseEnd_4065863 : Nat := 463942665407006894669765

theorem tailTrace_4065863 : CollatzResearch.WordTrace tailWord_4065863 prefixEnd_4065863 463942665407006894669765 := by
  unfold tailWord_4065863
  simp only [CollatzResearch.WordTrace]
  refine ⟨148294206469080219961970243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98862804312720146641313495 148294206469080219961970243)
  ·
    refine ⟨222441309703620329942955365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148294206469080219961970243 222441309703620329942955365)
    ·
      refine ⟨41707745569428811864304131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222441309703620329942955365 41707745569428811864304131)
      ·
        refine ⟨62561618354143217796456197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41707745569428811864304131 62561618354143217796456197)
        ·
          refine ⟨11730303441401853336835537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62561618354143217796456197 11730303441401853336835537)
          ·
            refine ⟨8797727581051390002626653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11730303441401853336835537 8797727581051390002626653)
            ·
              refine ⟨3299147842894271250984995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8797727581051390002626653 3299147842894271250984995)
              ·
                refine ⟨4948721764341406876477493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299147842894271250984995 4948721764341406876477493)
                ·
                  refine ⟨463942665407006894669765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948721764341406876477493 463942665407006894669765)
                  ·
                    rfl

theorem cell22_4065863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 5].length) (baseStart_4065863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065863 prefixEnd_4065863 := by exact prefixLift 4065863
  have htrace : WordTrace (prefixWord ++ tailWord_4065863) baseStart_4065863 baseEnd_4065863 := by
    simpa [prefixWord, tailWord_4065863, baseEnd_4065863] using wordTrace_append hprefix tailTrace_4065863
  have hstable : (prefixWord ++ tailWord_4065863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065863).length < 2 ^ (prefixWord ++ tailWord_4065863).sum := by decide
  have hdescent : baseEnd_4065863 < baseStart_4065863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065884 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4065884 : Nat := 118140960795 + 4065884 * 2 ^ 59
def prefixEnd_4065884 : Nat := 4983230072969 + 3 ^ 40 * 4065884 * 2
def baseEnd_4065884 : Nat := 1391835184950183629234231

theorem tailTrace_4065884 : CollatzResearch.WordTrace tailWord_4065884 prefixEnd_4065884 1391835184950183629234231 := by
  unfold tailWord_4065884
  simp only [CollatzResearch.WordTrace]
  refine ⟨74147486201002070274242353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98863314934669427032323137 74147486201002070274242353)
  ·
    refine ⟨55610614650751552705681765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74147486201002070274242353 55610614650751552705681765)
    ·
      refine ⟨10426990247015916132315331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55610614650751552705681765 10426990247015916132315331)
      ·
        refine ⟨15640485370523874198472997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426990247015916132315331 15640485370523874198472997)
        ·
          refine ⟨2932591006973226412213687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15640485370523874198472997 2932591006973226412213687)
          ·
            refine ⟨4398886510459839618320531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932591006973226412213687 4398886510459839618320531)
            ·
              refine ⟨6598329765689759427480797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398886510459839618320531 6598329765689759427480797)
              ·
                refine ⟨2474373662133659785305299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6598329765689759427480797 2474373662133659785305299)
                ·
                  refine ⟨3711560493200489677957949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474373662133659785305299 3711560493200489677957949)
                  ·
                    refine ⟨1391835184950183629234231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711560493200489677957949 1391835184950183629234231)
                    ·
                      rfl

theorem cell22_4065884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4065884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065884 prefixEnd_4065884 := by exact prefixLift 4065884
  have htrace : WordTrace (prefixWord ++ tailWord_4065884) baseStart_4065884 baseEnd_4065884 := by
    simpa [prefixWord, tailWord_4065884, baseEnd_4065884] using wordTrace_append hprefix tailTrace_4065884
  have hstable : (prefixWord ++ tailWord_4065884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065884).length < 2 ^ (prefixWord ++ tailWord_4065884).sum := by decide
  have hdescent : baseEnd_4065884 < baseStart_4065884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065921 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4065921 : Nat := 118140960795 + 4065921 * 2 ^ 59
def prefixEnd_4065921 : Nat := 4983230072969 + 3 ^ 40 * 4065921 * 2
def baseEnd_4065921 : Nat := 1391847850806327866059117

theorem tailTrace_4065921 : CollatzResearch.WordTrace tailWord_4065921 prefixEnd_4065921 1391847850806327866059117 := by
  unfold tailWord_4065921
  simp only [CollatzResearch.WordTrace]
  refine ⟨148296321902870095867581617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98864214601913397245054411 148296321902870095867581617)
  ·
    refine ⟨111222241427152571900686213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148296321902870095867581617 111222241427152571900686213)
    ·
      refine ⟨20854170267591107231378665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111222241427152571900686213 20854170267591107231378665)
      ·
        refine ⟨15640627700693330423533999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20854170267591107231378665 15640627700693330423533999)
        ·
          refine ⟨23460941551039995635300999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15640627700693330423533999 23460941551039995635300999)
          ·
            refine ⟨35191412326559993452951499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23460941551039995635300999 35191412326559993452951499)
            ·
              refine ⟨52787118489839990179427249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35191412326559993452951499 52787118489839990179427249)
              ·
                refine ⟨39590338867379992634570437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52787118489839990179427249 39590338867379992634570437)
                ·
                  refine ⟨7423188537633748618981957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39590338867379992634570437 7423188537633748618981957)
                  ·
                    refine ⟨1391847850806327866059117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423188537633748618981957 1391847850806327866059117)
                    ·
                      rfl

theorem cell22_4065921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4065921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065921 prefixEnd_4065921 := by exact prefixLift 4065921
  have htrace : WordTrace (prefixWord ++ tailWord_4065921) baseStart_4065921 baseEnd_4065921 := by
    simpa [prefixWord, tailWord_4065921, baseEnd_4065921] using wordTrace_append hprefix tailTrace_4065921
  have hstable : (prefixWord ++ tailWord_4065921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065921).length < 2 ^ (prefixWord ++ tailWord_4065921).sum := by decide
  have hdescent : baseEnd_4065921 < baseStart_4065921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065938 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4065938 : Nat := 118140960795 + 4065938 * 2 ^ 59
def prefixEnd_4065938 : Nat := 4983230072969 + 3 ^ 40 * 4065938 * 2
def baseEnd_4065938 : Nat := 1391853670253745488384065

theorem tailTrace_4065938 : CollatzResearch.WordTrace tailWord_4065938 prefixEnd_4065938 1391853670253745488384065 := by
  unfold tailWord_4065938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37074235485952126942737617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98864627962539005180633645 37074235485952126942737617)
  ·
    refine ⟨27805676614464095207053213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37074235485952126942737617 27805676614464095207053213)
    ·
      refine ⟨10427128730424035702644955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27805676614464095207053213 10427128730424035702644955)
      ·
        refine ⟨15640693095636053553967433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10427128730424035702644955 15640693095636053553967433)
        ·
          refine ⟨11730519821727040165475575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15640693095636053553967433 11730519821727040165475575)
          ·
            refine ⟨17595779732590560248213363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11730519821727040165475575 17595779732590560248213363)
            ·
              refine ⟨26393669598885840372320045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17595779732590560248213363 26393669598885840372320045)
              ·
                refine ⟨9897626099582190139620017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26393669598885840372320045 9897626099582190139620017)
                ·
                  refine ⟨7423219574686642604715013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9897626099582190139620017 7423219574686642604715013)
                  ·
                    refine ⟨1391853670253745488384065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423219574686642604715013 1391853670253745488384065)
                    ·
                      rfl

theorem cell22_4065938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4065938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065938 prefixEnd_4065938 := by exact prefixLift 4065938
  have htrace : WordTrace (prefixWord ++ tailWord_4065938) baseStart_4065938 baseEnd_4065938 := by
    simpa [prefixWord, tailWord_4065938, baseEnd_4065938] using wordTrace_append hprefix tailTrace_4065938
  have hstable : (prefixWord ++ tailWord_4065938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065938).length < 2 ^ (prefixWord ++ tailWord_4065938).sum := by decide
  have hdescent : baseEnd_4065938 < baseStart_4065938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065959 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 4]
def baseStart_4065959 : Nat := 118140960795 + 4065959 * 2 ^ 59
def prefixEnd_4065959 : Nat := 4983230072969 + 3 ^ 40 * 4065959 * 2
def baseEnd_4065959 : Nat := 463953619660969477869667

theorem tailTrace_4065959 : CollatzResearch.WordTrace tailWord_4065959 prefixEnd_4065959 463953619660969477869667 := by
  unfold tailWord_4065959
  simp only [CollatzResearch.WordTrace]
  refine ⟨148297707876732428357464931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98865138584488285571643287 148297707876732428357464931)
  ·
    refine ⟨222446561815098642536197397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148297707876732428357464931 222446561815098642536197397)
    ·
      refine ⟨10427182585082748868884253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 222446561815098642536197397 10427182585082748868884253)
      ·
        refine ⟨3910193469406030825831595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10427182585082748868884253 3910193469406030825831595)
        ·
          refine ⟨5865290204109046238747393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910193469406030825831595 5865290204109046238747393)
          ·
            refine ⟨4398967653081784679060545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865290204109046238747393 4398967653081784679060545)
            ·
              refine ⟨3299225739811338509295409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398967653081784679060545 3299225739811338509295409)
              ·
                refine ⟨2474419304858503881971557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299225739811338509295409 2474419304858503881971557)
                ·
                  refine ⟨463953619660969477869667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474419304858503881971557 463953619660969477869667)
                  ·
                    rfl

theorem cell22_4065959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 4].length) (baseStart_4065959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065959 prefixEnd_4065959 := by exact prefixLift 4065959
  have htrace : WordTrace (prefixWord ++ tailWord_4065959) baseStart_4065959 baseEnd_4065959 := by
    simpa [prefixWord, tailWord_4065959, baseEnd_4065959] using wordTrace_append hprefix tailTrace_4065959
  have hstable : (prefixWord ++ tailWord_4065959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065959).length < 2 ^ (prefixWord ++ tailWord_4065959).sum := by decide
  have hdescent : baseEnd_4065959 < baseStart_4065959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066058 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4066058 : Nat := 118140960795 + 4066058 * 2 ^ 59
def prefixEnd_4066058 : Nat := 4983230072969 + 3 ^ 40 * 4066058 * 2
def baseEnd_4066058 : Nat := 1391894748706105175383697

theorem tailTrace_4066058 : CollatzResearch.WordTrace tailWord_4066058 prefixEnd_4066058 1391894748706105175383697 := by
  unfold tailWord_4066058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075329675843442066329707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98867545802249178843545885 37075329675843442066329707)
  ·
    refine ⟨55612994513765163099494561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37075329675843442066329707 55612994513765163099494561)
    ·
      refine ⟨41709745885323872324620921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55612994513765163099494561 41709745885323872324620921)
      ·
        refine ⟨31282309413992904243465691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41709745885323872324620921 31282309413992904243465691)
        ·
          refine ⟨46923464120989356365198537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31282309413992904243465691 46923464120989356365198537)
          ·
            refine ⟨35192598090742017273898903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46923464120989356365198537 35192598090742017273898903)
            ·
              refine ⟨52788897136113025910848355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35192598090742017273898903 52788897136113025910848355)
              ·
                refine ⟨79183345704169538866272533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52788897136113025910848355 79183345704169538866272533)
                ·
                  refine ⟨3711719329882947134356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79183345704169538866272533 3711719329882947134356525)
                  ·
                    refine ⟨1391894748706105175383697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711719329882947134356525 1391894748706105175383697)
                    ·
                      rfl

theorem cell22_4066058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4066058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066058 prefixEnd_4066058 := by exact prefixLift 4066058
  have htrace : WordTrace (prefixWord ++ tailWord_4066058) baseStart_4066058 baseEnd_4066058 := by
    simpa [prefixWord, tailWord_4066058, baseEnd_4066058] using wordTrace_append hprefix tailTrace_4066058
  have hstable : (prefixWord ++ tailWord_4066058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066058).length < 2 ^ (prefixWord ++ tailWord_4066058).sum := by decide
  have hdescent : baseEnd_4066058 < baseStart_4066058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066077 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 6]
def baseStart_4066077 : Nat := 118140960795 + 4066077 * 2 ^ 59
def prefixEnd_4066077 : Nat := 4983230072969 + 3 ^ 40 * 4066077 * 2
def baseEnd_4066077 : Nat := 463967084264798486386213

theorem tailTrace_4066077 : CollatzResearch.WordTrace tailWord_4066077 prefixEnd_4066077 463967084264798486386213 := by
  unfold tailWord_4066077
  simp only [CollatzResearch.WordTrace]
  refine ⟨148302011690304934510260485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98868007793536623006840323 148302011690304934510260485)
  ·
    refine ⟨27806627191932175220673841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148302011690304934510260485 27806627191932175220673841)
    ·
      refine ⟨20854970393949131415505381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27806627191932175220673841 20854970393949131415505381)
      ·
        refine ⟨3910306948865462140407259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20854970393949131415505381 3910306948865462140407259)
        ·
          refine ⟨5865460423298193210610889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910306948865462140407259 5865460423298193210610889)
          ·
            refine ⟨4399095317473644907958167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865460423298193210610889 4399095317473644907958167)
            ·
              refine ⟨6598642976210467361937251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399095317473644907958167 6598642976210467361937251)
              ·
                refine ⟨9897964464315701042905877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598642976210467361937251 9897964464315701042905877)
                ·
                  refine ⟨463967084264798486386213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9897964464315701042905877 463967084264798486386213)
                  ·
                    rfl

theorem cell22_4066077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_4066077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066077 prefixEnd_4066077 := by exact prefixLift 4066077
  have htrace : WordTrace (prefixWord ++ tailWord_4066077) baseStart_4066077 baseEnd_4066077 := by
    simpa [prefixWord, tailWord_4066077, baseEnd_4066077] using wordTrace_append hprefix tailTrace_4066077
  have hstable : (prefixWord ++ tailWord_4066077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066077).length < 2 ^ (prefixWord ++ tailWord_4066077).sum := by decide
  have hdescent : baseEnd_4066077 < baseStart_4066077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066088 : List Nat := [2, 1, 5, 1, 1, 1, 4, 7]
def baseStart_4066088 : Nat := 118140960795 + 4066088 * 2 ^ 59
def prefixEnd_4066088 : Nat := 4983230072969 + 3 ^ 40 * 4066088 * 2
def baseEnd_4066088 : Nat := 154656113146577233014845

theorem tailTrace_4066088 : CollatzResearch.WordTrace tailWord_4066088 prefixEnd_4066088 154656113146577233014845 := by
  unfold tailWord_4066088
  simp only [CollatzResearch.WordTrace]
  refine ⟨74151206446632541694455459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98868275262176722259273945 74151206446632541694455459)
  ·
    refine ⟨111226809669948812541683189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74151206446632541694455459 111226809669948812541683189)
    ·
      refine ⟨10427513406557701175782799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111226809669948812541683189 10427513406557701175782799)
      ·
        refine ⟨15641270109836551763674199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10427513406557701175782799 15641270109836551763674199)
        ·
          refine ⟨23461905164754827645511299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15641270109836551763674199 23461905164754827645511299)
          ·
            refine ⟨35192857747132241468266949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23461905164754827645511299 35192857747132241468266949)
            ·
              refine ⟨6598660827587295275300053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35192857747132241468266949 6598660827587295275300053)
              ·
                refine ⟨154656113146577233014845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6598660827587295275300053 154656113146577233014845)
                ·
                  rfl

theorem cell22_4066088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_4066088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066088 prefixEnd_4066088 := by exact prefixLift 4066088
  have htrace : WordTrace (prefixWord ++ tailWord_4066088) baseStart_4066088 baseEnd_4066088 := by
    simpa [prefixWord, tailWord_4066088, baseEnd_4066088] using wordTrace_append hprefix tailTrace_4066088
  have hstable : (prefixWord ++ tailWord_4066088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066088).length < 2 ^ (prefixWord ++ tailWord_4066088).sum := by decide
  have hdescent : baseEnd_4066088 < baseStart_4066088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066103 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 5, 3]
def baseStart_4066103 : Nat := 118140960795 + 4066103 * 2 ^ 59
def prefixEnd_4066103 : Nat := 4983230072969 + 3 ^ 40 * 4066103 * 2
def baseEnd_4066103 : Nat := 1391910153125740058008559

theorem tailTrace_4066103 : CollatzResearch.WordTrace tailWord_4066103 prefixEnd_4066103 1391910153125740058008559 := by
  unfold tailWord_4066103
  simp only [CollatzResearch.WordTrace]
  refine ⟨148302959988210740950706963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98868639992140493967137975 148302959988210740950706963)
  ·
    refine ⟨222454439982316111426060445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148302959988210740950706963 222454439982316111426060445)
    ·
      refine ⟨83420414993368541784772667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222454439982316111426060445 83420414993368541784772667)
      ·
        refine ⟨125130622490052812677159001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83420414993368541784772667 125130622490052812677159001)
        ·
          refine ⟨93847966867539609507869251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125130622490052812677159001 93847966867539609507869251)
          ·
            refine ⟨140771950301309414261803877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93847966867539609507869251 140771950301309414261803877)
            ·
              refine ⟨26394740681495515174088227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140771950301309414261803877 26394740681495515174088227)
              ·
                refine ⟨39592111022243272761132341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26394740681495515174088227 39592111022243272761132341)
                ·
                  refine ⟨3711760408335306821356157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39592111022243272761132341 3711760408335306821356157)
                  ·
                    refine ⟨1391910153125740058008559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711760408335306821356157 1391910153125740058008559)
                    ·
                      rfl

theorem cell22_4066103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_4066103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066103 prefixEnd_4066103 := by exact prefixLift 4066103
  have htrace : WordTrace (prefixWord ++ tailWord_4066103) baseStart_4066103 baseEnd_4066103 := by
    simpa [prefixWord, tailWord_4066103, baseEnd_4066103] using wordTrace_append hprefix tailTrace_4066103
  have hstable : (prefixWord ++ tailWord_4066103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066103).length < 2 ^ (prefixWord ++ tailWord_4066103).sum := by decide
  have hdescent : baseEnd_4066103 < baseStart_4066103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066131 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_4066131 : Nat := 118140960795 + 4066131 * 2 ^ 59
def prefixEnd_4066131 : Nat := 4983230072969 + 3 ^ 40 * 4066131 * 2
def baseEnd_4066131 : Nat := 1391919738097957318308473

theorem tailTrace_4066131 : CollatzResearch.WordTrace tailWord_4066131 prefixEnd_4066131 1391919738097957318308473 := by
  unfold tailWord_4066131
  simp only [CollatzResearch.WordTrace]
  refine ⟨148303981232109301732726247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98869320821406201155150831 148303981232109301732726247)
  ·
    refine ⟨222455971848163952599089371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148303981232109301732726247 222455971848163952599089371)
    ·
      refine ⟨333683957772245928898634057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222455971848163952599089371 333683957772245928898634057)
      ·
        refine ⟨250262968329184446673975543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333683957772245928898634057 250262968329184446673975543)
        ·
          refine ⟨375394452493776670010963315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250262968329184446673975543 375394452493776670010963315)
          ·
            refine ⟨563091678740665005016444973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375394452493776670010963315 563091678740665005016444973)
            ·
              refine ⟨211159379527749376881166865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563091678740665005016444973 211159379527749376881166865)
              ·
                refine ⟨158369534645812032660875149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211159379527749376881166865 158369534645812032660875149)
                ·
                  refine ⟨59388575492179512247828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158369534645812032660875149 59388575492179512247828181)
                  ·
                    refine ⟨1391919738097957318308473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59388575492179512247828181 1391919738097957318308473)
                    ·
                      rfl

theorem cell22_4066131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_4066131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066131 prefixEnd_4066131 := by exact prefixLift 4066131
  have htrace : WordTrace (prefixWord ++ tailWord_4066131) baseStart_4066131 baseEnd_4066131 := by
    simpa [prefixWord, tailWord_4066131, baseEnd_4066131] using wordTrace_append hprefix tailTrace_4066131
  have hstable : (prefixWord ++ tailWord_4066131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066131).length < 2 ^ (prefixWord ++ tailWord_4066131).sum := by decide
  have hdescent : baseEnd_4066131 < baseStart_4066131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066137 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 1, 3]
def baseStart_4066137 : Nat := 118140960795 + 4066137 * 2 ^ 59
def prefixEnd_4066137 : Nat := 4983230072969 + 3 ^ 40 * 4066137 * 2
def baseEnd_4066137 : Nat := 1391921792020575302658455

theorem tailTrace_4066137 : CollatzResearch.WordTrace tailWord_4066137 prefixEnd_4066137 1391921792020575302658455 := by
  unfold tailWord_4066137
  simp only [CollatzResearch.WordTrace]
  refine ⟨148304200070087564757444665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98869466713391709838296443 148304200070087564757444665)
  ·
    refine ⟨111228150052565673568083499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148304200070087564757444665 111228150052565673568083499)
    ·
      refine ⟨166842225078848510352125249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111228150052565673568083499 166842225078848510352125249)
      ·
        refine ⟨125131668809136382764093937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166842225078848510352125249 125131668809136382764093937)
        ·
          refine ⟨93848751606852287073070453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125131668809136382764093937 93848751606852287073070453)
          ·
            refine ⟨8798320463142401913100355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93848751606852287073070453 8798320463142401913100355)
            ·
              refine ⟨13197480694713602869650533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798320463142401913100355 13197480694713602869650533)
              ·
                refine ⟨2474527630258800538059475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13197480694713602869650533 2474527630258800538059475)
                ·
                  refine ⟨3711791445388200807089213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474527630258800538059475 3711791445388200807089213)
                  ·
                    refine ⟨1391921792020575302658455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711791445388200807089213 1391921792020575302658455)
                    ·
                      rfl

theorem cell22_4066137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_4066137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066137 prefixEnd_4066137 := by exact prefixLift 4066137
  have htrace : WordTrace (prefixWord ++ tailWord_4066137) baseStart_4066137 baseEnd_4066137 := by
    simpa [prefixWord, tailWord_4066137, baseEnd_4066137] using wordTrace_append hprefix tailTrace_4066137
  have hstable : (prefixWord ++ tailWord_4066137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066137).length < 2 ^ (prefixWord ++ tailWord_4066137).sum := by decide
  have hdescent : baseEnd_4066137 < baseStart_4066137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066148 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_4066148 : Nat := 118140960795 + 4066148 * 2 ^ 59
def prefixEnd_4066148 : Nat := 4983230072969 + 3 ^ 40 * 4066148 * 2
def baseEnd_4066148 : Nat := 1391925557545374940633421

theorem tailTrace_4066148 : CollatzResearch.WordTrace tailWord_4066148 prefixEnd_4066148 1391925557545374940633421 := by
  unfold tailWord_4066148
  simp only [CollatzResearch.WordTrace]
  refine ⟨74152300636523856818047549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98869734182031809090730065 74152300636523856818047549)
  ·
    refine ⟨27807112738696446306767831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74152300636523856818047549 27807112738696446306767831)
    ·
      refine ⟨41710669108044669460151747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27807112738696446306767831 41710669108044669460151747)
      ·
        refine ⟨62566003662067004190227621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41710669108044669460151747 62566003662067004190227621)
        ·
          refine ⟨11731125686637563285667679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62566003662067004190227621 11731125686637563285667679)
          ·
            refine ⟨17596688529956344928501519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11731125686637563285667679 17596688529956344928501519)
            ·
              refine ⟨26395032794934517392752279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17596688529956344928501519 26395032794934517392752279)
              ·
                refine ⟨39592549192401776089128419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26395032794934517392752279 39592549192401776089128419)
                ·
                  refine ⟨59388823788602664133692629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39592549192401776089128419 59388823788602664133692629)
                  ·
                    refine ⟨1391925557545374940633421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59388823788602664133692629 1391925557545374940633421)
                    ·
                      rfl

theorem cell22_4066148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_4066148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066148 prefixEnd_4066148 := by exact prefixLift 4066148
  have htrace : WordTrace (prefixWord ++ tailWord_4066148) baseStart_4066148 baseEnd_4066148 := by
    simpa [prefixWord, tailWord_4066148, baseEnd_4066148] using wordTrace_append hprefix tailTrace_4066148
  have hstable : (prefixWord ++ tailWord_4066148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066148).length < 2 ^ (prefixWord ++ tailWord_4066148).sum := by decide
  have hdescent : baseEnd_4066148 < baseStart_4066148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066163 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_4066163 : Nat := 118140960795 + 4066163 * 2 ^ 59
def prefixEnd_4066163 : Nat := 4983230072969 + 3 ^ 40 * 4066163 * 2
def baseEnd_4066163 : Nat := 1391930692351919901508375

theorem tailTrace_4066163 : CollatzResearch.WordTrace tailWord_4066163 prefixEnd_4066163 1391930692351919901508375 := by
  unfold tailWord_4066163
  simp only [CollatzResearch.WordTrace]
  refine ⟨148305148367993371197891143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98870098911995580798594095 148305148367993371197891143)
  ·
    refine ⟨222457722551990056796836715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148305148367993371197891143 222457722551990056796836715)
    ·
      refine ⟨333686583827985085195255073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222457722551990056796836715 333686583827985085195255073)
      ·
        refine ⟨250264937870988813896441305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333686583827985085195255073 250264937870988813896441305)
        ·
          refine ⟨187698703403241610422330979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250264937870988813896441305 187698703403241610422330979)
          ·
            refine ⟨281548055104862415633496469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187698703403241610422330979 281548055104862415633496469)
            ·
              refine ⟨13197565083040425732820147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281548055104862415633496469 13197565083040425732820147)
              ·
                refine ⟨19796347624560638599230221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197565083040425732820147 19796347624560638599230221)
                ·
                  refine ⟨7423630359210239474711333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19796347624560638599230221 7423630359210239474711333)
                  ·
                    refine ⟨1391930692351919901508375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423630359210239474711333 1391930692351919901508375)
                    ·
                      rfl

theorem cell22_4066163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_4066163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066163 prefixEnd_4066163 := by exact prefixLift 4066163
  have htrace : WordTrace (prefixWord ++ tailWord_4066163) baseStart_4066163 baseEnd_4066163 := by
    simpa [prefixWord, tailWord_4066163, baseEnd_4066163] using wordTrace_append hprefix tailTrace_4066163
  have hstable : (prefixWord ++ tailWord_4066163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066163).length < 2 ^ (prefixWord ++ tailWord_4066163).sum := by decide
  have hdescent : baseEnd_4066163 < baseStart_4066163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066208 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_4066208 : Nat := 118140960795 + 4066208 * 2 ^ 59
def prefixEnd_4066208 : Nat := 4983230072969 + 3 ^ 40 * 4066208 * 2
def baseEnd_4066208 : Nat := 1391946096771554784133237

theorem tailTrace_4066208 : CollatzResearch.WordTrace tailWord_4066208 prefixEnd_4066208 1391946096771554784133237 := by
  unfold tailWord_4066208
  simp only [CollatzResearch.WordTrace]
  refine ⟨74153394826415171941639639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98871193101886895922186185 74153394826415171941639639)
  ·
    refine ⟨111230092239622757912459459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74153394826415171941639639 111230092239622757912459459)
    ·
      refine ⟨166845138359434136868689189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111230092239622757912459459 166845138359434136868689189)
      ·
        refine ⟨31283463442393900662879223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166845138359434136868689189 31283463442393900662879223)
        ·
          refine ⟨46925195163590850994318835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31283463442393900662879223 46925195163590850994318835)
          ·
            refine ⟨70387792745386276491478253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46925195163590850994318835 70387792745386276491478253)
            ·
              refine ⟨26395422279519853684304345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70387792745386276491478253 26395422279519853684304345)
              ·
                refine ⟨19796566709639890263228259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26395422279519853684304345 19796566709639890263228259)
                ·
                  refine ⟨29694850064459835394842389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19796566709639890263228259 29694850064459835394842389)
                  ·
                    refine ⟨1391946096771554784133237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29694850064459835394842389 1391946096771554784133237)
                    ·
                      rfl

theorem cell22_4066208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_4066208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066208 prefixEnd_4066208 := by exact prefixLift 4066208
  have htrace : WordTrace (prefixWord ++ tailWord_4066208) baseStart_4066208 baseEnd_4066208 := by
    simpa [prefixWord, tailWord_4066208, baseEnd_4066208] using wordTrace_append hprefix tailTrace_4066208
  have hstable : (prefixWord ++ tailWord_4066208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066208).length < 2 ^ (prefixWord ++ tailWord_4066208).sum := by decide
  have hdescent : baseEnd_4066208 < baseStart_4066208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066261 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_4066261 : Nat := 118140960795 + 4066261 * 2 ^ 59
def prefixEnd_4066261 : Nat := 4983230072969 + 3 ^ 40 * 4066261 * 2
def baseEnd_4066261 : Nat := 1391964239754680312558075

theorem tailTrace_4066261 : CollatzResearch.WordTrace tailWord_4066261 prefixEnd_4066261 1391964239754680312558075 := by
  unfold tailWord_4066261
  simp only [CollatzResearch.WordTrace]
  refine ⟨148308722721638333934958637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98872481814425555956639091 148308722721638333934958637)
  ·
    refine ⟨55615771020614375225609489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148308722721638333934958637 55615771020614375225609489)
    ·
      refine ⟨41711828265460781419207117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55615771020614375225609489 41711828265460781419207117)
      ·
        refine ⟨15641935599547793032202669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41711828265460781419207117 15641935599547793032202669)
        ·
          refine ⟨5865725849830422387076001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15641935599547793032202669 5865725849830422387076001)
          ·
            refine ⟨4399294387372816790307001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865725849830422387076001 4399294387372816790307001)
            ·
              refine ⟨3299470790529612592730251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399294387372816790307001 3299470790529612592730251)
              ·
                refine ⟨4949206185794418889095377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299470790529612592730251 4949206185794418889095377)
                ·
                  refine ⟨3711904639345814166821533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4949206185794418889095377 3711904639345814166821533)
                  ·
                    refine ⟨1391964239754680312558075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711904639345814166821533 1391964239754680312558075)
                    ·
                      rfl

theorem cell22_4066261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_4066261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066261 prefixEnd_4066261 := by exact prefixLift 4066261
  have htrace : WordTrace (prefixWord ++ tailWord_4066261) baseStart_4066261 baseEnd_4066261 := by
    simpa [prefixWord, tailWord_4066261, baseEnd_4066261] using wordTrace_append hprefix tailTrace_4066261
  have hstable : (prefixWord ++ tailWord_4066261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066261).length < 2 ^ (prefixWord ++ tailWord_4066261).sum := by decide
  have hdescent : baseEnd_4066261 < baseStart_4066261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066283 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_4066283 : Nat := 118140960795 + 4066283 * 2 ^ 59
def prefixEnd_4066283 : Nat := 4983230072969 + 3 ^ 40 * 4066283 * 2
def baseEnd_4066283 : Nat := 1391971770804279588508007

theorem tailTrace_4066283 : CollatzResearch.WordTrace tailWord_4066283 prefixEnd_4066283 1391971770804279588508007 := by
  unfold tailWord_4066283
  simp only [CollatzResearch.WordTrace]
  refine ⟨148309525127558631692259503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98873016751705754461506335 148309525127558631692259503)
  ·
    refine ⟨222464287691337947538389255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148309525127558631692259503 222464287691337947538389255)
    ·
      refine ⟨333696431537006921307583883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222464287691337947538389255 333696431537006921307583883)
      ·
        refine ⟨500544647305510381961375825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333696431537006921307583883 500544647305510381961375825)
        ·
          refine ⟨375408485479132786471031869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500544647305510381961375825 375408485479132786471031869)
          ·
            refine ⟨140778182054674794926636951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375408485479132786471031869 140778182054674794926636951)
            ·
              refine ⟨211167273082012192389955427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140778182054674794926636951 211167273082012192389955427)
              ·
                refine ⟨316750909623018288584933141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211167273082012192389955427 316750909623018288584933141)
                ·
                  refine ⟨14847698888578982277418741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 316750909623018288584933141 14847698888578982277418741)
                  ·
                    refine ⟨1391971770804279588508007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14847698888578982277418741 1391971770804279588508007)
                    ·
                      rfl

theorem cell22_4066283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_4066283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066283 prefixEnd_4066283 := by exact prefixLift 4066283
  have htrace : WordTrace (prefixWord ++ tailWord_4066283) baseStart_4066283 baseEnd_4066283 := by
    simpa [prefixWord, tailWord_4066283, baseEnd_4066283] using wordTrace_append hprefix tailTrace_4066283
  have hstable : (prefixWord ++ tailWord_4066283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066283).length < 2 ^ (prefixWord ++ tailWord_4066283).sum := by decide
  have hdescent : baseEnd_4066283 < baseStart_4066283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066313 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 10]
def baseStart_4066313 : Nat := 118140960795 + 4066313 * 2 ^ 59
def prefixEnd_4066313 : Nat := 4983230072969 + 3 ^ 40 * 4066313 * 2
def baseEnd_4066313 : Nat := 463994013472456503419305

theorem tailTrace_4066313 : CollatzResearch.WordTrace tailWord_4066313 prefixEnd_4066313 463994013472456503419305 := by
  unfold tailWord_4066313
  simp only [CollatzResearch.WordTrace]
  refine ⟨148310619317449946815851593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98873746211633297877234395 148310619317449946815851593)
  ·
    refine ⟨111232964488087460111888695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148310619317449946815851593 111232964488087460111888695)
    ·
      refine ⟨166849446732131190167833043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111232964488087460111888695 166849446732131190167833043)
      ·
        refine ⟨250274170098196785251749565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166849446732131190167833043 250274170098196785251749565)
        ·
          refine ⟨93852813786823794469406087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250274170098196785251749565 93852813786823794469406087)
          ·
            refine ⟨140779220680235691704109131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93852813786823794469406087 140779220680235691704109131)
            ·
              refine ⟨211168831020353537556163697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140779220680235691704109131 211168831020353537556163697)
              ·
                refine ⟨158376623265265153167122773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211168831020353537556163697 158376623265265153167122773)
                ·
                  refine ⟨463994013472456503419305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 158376623265265153167122773 463994013472456503419305)
                  ·
                    rfl

theorem cell22_4066313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_4066313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066313 prefixEnd_4066313 := by exact prefixLift 4066313
  have htrace : WordTrace (prefixWord ++ tailWord_4066313) baseStart_4066313 baseEnd_4066313 := by
    simpa [prefixWord, tailWord_4066313, baseEnd_4066313] using wordTrace_append hprefix tailTrace_4066313
  have hstable : (prefixWord ++ tailWord_4066313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066313).length < 2 ^ (prefixWord ++ tailWord_4066313).sum := by decide
  have hdescent : baseEnd_4066313 < baseStart_4066313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066315 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_4066315 : Nat := 118140960795 + 4066315 * 2 ^ 59
def prefixEnd_4066315 : Nat := 4983230072969 + 3 ^ 40 * 4066315 * 2
def baseEnd_4066315 : Nat := 1391982725058242171707909

theorem tailTrace_4066315 : CollatzResearch.WordTrace tailWord_4066315 prefixEnd_4066315 1391982725058242171707909 := by
  unfold tailWord_4066315
  simp only [CollatzResearch.WordTrace]
  refine ⟨148310692263442701157424399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98873794842295134104949599 148310692263442701157424399)
  ·
    refine ⟨222466038395164051736136599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148310692263442701157424399 222466038395164051736136599)
    ·
      refine ⟨333699057592746077604204899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222466038395164051736136599 333699057592746077604204899)
      ·
        refine ⟨500548586389119116406307349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333699057592746077604204899 500548586389119116406307349)
        ·
          refine ⟨23463214986989958581545657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 500548586389119116406307349 23463214986989958581545657)
          ·
            refine ⟨17597411240242468936159243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23463214986989958581545657 17597411240242468936159243)
            ·
              refine ⟨26396116860363703404238865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17597411240242468936159243 26396116860363703404238865)
              ·
                refine ⟨19797087645272777553179149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26396116860363703404238865 19797087645272777553179149)
                ·
                  refine ⟨7423907866977291582442181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19797087645272777553179149 7423907866977291582442181)
                  ·
                    refine ⟨1391982725058242171707909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7423907866977291582442181 1391982725058242171707909)
                    ·
                      rfl

theorem cell22_4066315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_4066315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066315 prefixEnd_4066315 := by exact prefixLift 4066315
  have htrace : WordTrace (prefixWord ++ tailWord_4066315) baseStart_4066315 baseEnd_4066315 := by
    simpa [prefixWord, tailWord_4066315, baseEnd_4066315] using wordTrace_append hprefix tailTrace_4066315
  have hstable : (prefixWord ++ tailWord_4066315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066315).length < 2 ^ (prefixWord ++ tailWord_4066315).sum := by decide
  have hdescent : baseEnd_4066315 < baseStart_4066315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066330 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_4066330 : Nat := 118140960795 + 4066330 * 2 ^ 59
def prefixEnd_4066330 : Nat := 4983230072969 + 3 ^ 40 * 4066330 * 2
def baseEnd_4066330 : Nat := 463995953288262377527621

theorem tailTrace_4066330 : CollatzResearch.WordTrace tailWord_4066330 prefixEnd_4066330 463995953288262377527621 := by
  unfold tailWord_4066330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37077809839597089679805111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98874159572258905812813629 37077809839597089679805111)
  ·
    refine ⟨55616714759395634519707667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37077809839597089679805111 55616714759395634519707667)
    ·
      refine ⟨83425072139093451779561501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55616714759395634519707667 83425072139093451779561501)
      ·
        refine ⟨31284402052160044417335563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83425072139093451779561501 31284402052160044417335563)
        ·
          refine ⟨46926603078240066626003345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31284402052160044417335563 46926603078240066626003345)
          ·
            refine ⟨35194952308680049969502509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46926603078240066626003345 35194952308680049969502509)
            ·
              refine ⟨13198107115755018738563441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35194952308680049969502509 13198107115755018738563441)
              ·
                refine ⟨9898580336816264053922581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13198107115755018738563441 9898580336816264053922581)
                ·
                  refine ⟨463995953288262377527621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9898580336816264053922581 463995953288262377527621)
                  ·
                    rfl

theorem cell22_4066330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_4066330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066330 prefixEnd_4066330 := by exact prefixLift 4066330
  have htrace : WordTrace (prefixWord ++ tailWord_4066330) baseStart_4066330 baseEnd_4066330 := by
    simpa [prefixWord, tailWord_4066330, baseEnd_4066330] using wordTrace_append hprefix tailTrace_4066330
  have hstable : (prefixWord ++ tailWord_4066330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066330).length < 2 ^ (prefixWord ++ tailWord_4066330).sum := by decide
  have hdescent : baseEnd_4066330 < baseStart_4066330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066347 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 4]
def baseStart_4066347 : Nat := 118140960795 + 4066347 * 2 ^ 59
def prefixEnd_4066347 : Nat := 4983230072969 + 3 ^ 40 * 4066347 * 2
def baseEnd_4066347 : Nat := 463997893104068251635937

theorem tailTrace_4066347 : CollatzResearch.WordTrace tailWord_4066347 prefixEnd_4066347 463997893104068251635937 := by
  unfold tailWord_4066347
  simp only [CollatzResearch.WordTrace]
  refine ⟨148311859399326770622589295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98874572932884513748392863 148311859399326770622589295)
  ·
    refine ⟨222467789098990155933883943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148311859399326770622589295 222467789098990155933883943)
    ·
      refine ⟨333701683648485233900825915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222467789098990155933883943 333701683648485233900825915)
      ·
        refine ⟨500552525472727850851238873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333701683648485233900825915 500552525472727850851238873)
        ·
          refine ⟨375414394104545888138429155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500552525472727850851238873 375414394104545888138429155)
          ·
            refine ⟨563121591156818832207643733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375414394104545888138429155 563121591156818832207643733)
            ·
              refine ⟨6599081146368970689933325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 563121591156818832207643733 6599081146368970689933325)
              ·
                refine ⟨2474655429888364008724997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6599081146368970689933325 2474655429888364008724997)
                ·
                  refine ⟨463997893104068251635937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474655429888364008724997 463997893104068251635937)
                  ·
                    rfl

theorem cell22_4066347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 4].length) (baseStart_4066347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066347 prefixEnd_4066347 := by exact prefixLift 4066347
  have htrace : WordTrace (prefixWord ++ tailWord_4066347) baseStart_4066347 baseEnd_4066347 := by
    simpa [prefixWord, tailWord_4066347, baseEnd_4066347] using wordTrace_append hprefix tailTrace_4066347
  have hstable : (prefixWord ++ tailWord_4066347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066347).length < 2 ^ (prefixWord ++ tailWord_4066347).sum := by decide
  have hdescent : baseEnd_4066347 < baseStart_4066347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066398 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4066398 : Nat := 118140960795 + 4066398 * 2 ^ 59
def prefixEnd_4066398 : Nat := 4983230072969 + 3 ^ 40 * 4066398 * 2
def baseEnd_4066398 : Nat := 464003712551485873960885

theorem tailTrace_4066398 : CollatzResearch.WordTrace tailWord_4066398 prefixEnd_4066398 464003712551485873960885 := by
  unfold tailWord_4066398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539214940267750791586981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98875813014761337555130565 18539214940267750791586981)
  ·
    refine ⟨3476102801300203273422559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18539214940267750791586981 3476102801300203273422559)
    ·
      refine ⟨5214154201950304910133839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476102801300203273422559 5214154201950304910133839)
      ·
        refine ⟨7821231302925457365200759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214154201950304910133839 7821231302925457365200759)
        ·
          refine ⟨11731846954388186047801139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821231302925457365200759 11731846954388186047801139)
          ·
            refine ⟨17597770431582279071701709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11731846954388186047801139 17597770431582279071701709)
            ·
              refine ⟨6599163911843354651888141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17597770431582279071701709 6599163911843354651888141)
              ·
                refine ⟨2474686466941257994458053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6599163911843354651888141 2474686466941257994458053)
                ·
                  refine ⟨464003712551485873960885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474686466941257994458053 464003712551485873960885)
                  ·
                    rfl

theorem cell22_4066398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4066398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066398 prefixEnd_4066398 := by exact prefixLift 4066398
  have htrace : WordTrace (prefixWord ++ tailWord_4066398) baseStart_4066398 baseEnd_4066398 := by
    simpa [prefixWord, tailWord_4066398, baseEnd_4066398] using wordTrace_append hprefix tailTrace_4066398
  have hstable : (prefixWord ++ tailWord_4066398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066398).length < 2 ^ (prefixWord ++ tailWord_4066398).sum := by decide
  have hdescent : baseEnd_4066398 < baseStart_4066398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066422 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4066422 : Nat := 118140960795 + 4066422 * 2 ^ 59
def prefixEnd_4066422 : Nat := 4983230072969 + 3 ^ 40 * 4066422 * 2
def baseEnd_4066422 : Nat := 1392019353344929559282581

theorem tailTrace_4066422 : CollatzResearch.WordTrace tailWord_4066422 prefixEnd_4066422 1392019353344929559282581 := by
  unfold tailWord_4066422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269662179628441151973095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98876396582703372287713013 9269662179628441151973095)
  ·
    refine ⟨13904493269442661727959643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9269662179628441151973095 13904493269442661727959643)
    ·
      refine ⟨20856739904163992591939465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13904493269442661727959643 20856739904163992591939465)
      ·
        refine ⟨15642554928122994443954599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20856739904163992591939465 15642554928122994443954599)
        ·
          refine ⟨23463832392184491665931899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15642554928122994443954599 23463832392184491665931899)
          ·
            refine ⟨35195748588276737498897849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23463832392184491665931899 35195748588276737498897849)
            ·
              refine ⟨26396811441207553124173387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35195748588276737498897849 26396811441207553124173387)
              ·
                refine ⟨39595217161811329686260081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26396811441207553124173387 39595217161811329686260081)
                ·
                  refine ⟨29696412871358497264695061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39595217161811329686260081 29696412871358497264695061)
                  ·
                    refine ⟨1392019353344929559282581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29696412871358497264695061 1392019353344929559282581)
                    ·
                      rfl

theorem cell22_4066422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4066422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066422 prefixEnd_4066422 := by exact prefixLift 4066422
  have htrace : WordTrace (prefixWord ++ tailWord_4066422) baseStart_4066422 baseEnd_4066422 := by
    simpa [prefixWord, tailWord_4066422, baseEnd_4066422] using wordTrace_append hprefix tailTrace_4066422
  have hstable : (prefixWord ++ tailWord_4066422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066422).length < 2 ^ (prefixWord ++ tailWord_4066422).sum := by decide
  have hdescent : baseEnd_4066422 < baseStart_4066422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066424 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 1, 3]
def baseStart_4066424 : Nat := 118140960795 + 4066424 * 2 ^ 59
def prefixEnd_4066424 : Nat := 4983230072969 + 3 ^ 40 * 4066424 * 2
def baseEnd_4066424 : Nat := 1392020037985802220732575

theorem tailTrace_4066424 : CollatzResearch.WordTrace tailWord_4066424 prefixEnd_4066424 1392020037985802220732575 := by
  unfold tailWord_4066424
  simp only [CollatzResearch.WordTrace]
  refine ⟨74157333910023906386571163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98876445213365208515428217 74157333910023906386571163)
  ·
    refine ⟨111236000865035859579856745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74157333910023906386571163 111236000865035859579856745)
    ·
      refine ⟨83427000648776894684892559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111236000865035859579856745 83427000648776894684892559)
      ·
        refine ⟨125140500973165342027338839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83427000648776894684892559 125140500973165342027338839)
        ·
          refine ⟨187710751459748013041008259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125140500973165342027338839 187710751459748013041008259)
          ·
            refine ⟨281566127189622019561512389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187710751459748013041008259 281566127189622019561512389)
            ·
              refine ⟨52793648848054128667783573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281566127189622019561512389 52793648848054128667783573)
              ·
                refine ⟨2474702289752537281302355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52793648848054128667783573 2474702289752537281302355)
                ·
                  refine ⟨3712053434628805921953533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474702289752537281302355 3712053434628805921953533)
                  ·
                    refine ⟨1392020037985802220732575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712053434628805921953533 1392020037985802220732575)
                    ·
                      rfl

theorem cell22_4066424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_4066424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066424 prefixEnd_4066424 := by exact prefixLift 4066424
  have htrace : WordTrace (prefixWord ++ tailWord_4066424) baseStart_4066424 baseEnd_4066424 := by
    simpa [prefixWord, tailWord_4066424, baseEnd_4066424] using wordTrace_append hprefix tailTrace_4066424
  have hstable : (prefixWord ++ tailWord_4066424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066424).length < 2 ^ (prefixWord ++ tailWord_4066424).sum := by decide
  have hdescent : baseEnd_4066424 < baseStart_4066424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066430 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4066430 : Nat := 118140960795 + 4066430 * 2 ^ 59
def prefixEnd_4066430 : Nat := 4983230072969 + 3 ^ 40 * 4066430 * 2
def baseEnd_4066430 : Nat := 1392022091908420205082557

theorem tailTrace_4066430 : CollatzResearch.WordTrace tailWord_4066430 prefixEnd_4066430 1392022091908420205082557 := by
  unfold tailWord_4066430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539360832253259474732593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98876591105350717198573829 18539360832253259474732593)
  ·
    refine ⟨13904520624189944606049445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18539360832253259474732593 13904520624189944606049445)
    ·
      refine ⟨2607097617035614613634271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13904520624189944606049445 2607097617035614613634271)
      ·
        refine ⟨3910646425553421920451407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607097617035614613634271 3910646425553421920451407)
        ·
          refine ⟨5865969638330132880677111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910646425553421920451407 5865969638330132880677111)
          ·
            refine ⟨8798954457495199321015667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865969638330132880677111 8798954457495199321015667)
            ·
              refine ⟨13198431686242798981523501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798954457495199321015667 13198431686242798981523501)
              ·
                refine ⟨4949411882341049618071313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13198431686242798981523501 4949411882341049618071313)
                ·
                  refine ⟨3712058911755787213553485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4949411882341049618071313 3712058911755787213553485)
                  ·
                    refine ⟨1392022091908420205082557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712058911755787213553485 1392022091908420205082557)
                    ·
                      rfl

theorem cell22_4066430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4066430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066430 prefixEnd_4066430 := by exact prefixLift 4066430
  have htrace : WordTrace (prefixWord ++ tailWord_4066430) baseStart_4066430 baseEnd_4066430 := by
    simpa [prefixWord, tailWord_4066430, baseEnd_4066430] using wordTrace_append hprefix tailTrace_4066430
  have hstable : (prefixWord ++ tailWord_4066430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066430).length < 2 ^ (prefixWord ++ tailWord_4066430).sum := by decide
  have hdescent : baseEnd_4066430 < baseStart_4066430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066435 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_4066435 : Nat := 118140960795 + 4066435 * 2 ^ 59
def prefixEnd_4066435 : Nat := 4983230072969 + 3 ^ 40 * 4066435 * 2
def baseEnd_4066435 : Nat := 1392023803510601858707541

theorem tailTrace_4066435 : CollatzResearch.WordTrace tailWord_4066435 prefixEnd_4066435 1392023803510601858707541 := by
  unfold tailWord_4066435
  simp only [CollatzResearch.WordTrace]
  refine ⟨148315069023007961651792759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98876712682005307767861839 148315069023007961651792759)
  ·
    refine ⟨222472603534511942477689139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148315069023007961651792759 222472603534511942477689139)
    ·
      refine ⟨333708905301767913716533709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222472603534511942477689139 333708905301767913716533709)
      ·
        refine ⟨125140839488162967643700141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333708905301767913716533709 125140839488162967643700141)
        ·
          refine ⟨46927814808061112866387553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125140839488162967643700141 46927814808061112866387553)
          ·
            refine ⟨35195861106045834649790665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46927814808061112866387553 35195861106045834649790665)
            ·
              refine ⟨26396895829534375987342999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35195861106045834649790665 26396895829534375987342999)
              ·
                refine ⟨39595343744301563981014499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26396895829534375987342999 39595343744301563981014499)
                ·
                  refine ⟨59393015616452345971521749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39595343744301563981014499 59393015616452345971521749)
                  ·
                    refine ⟨1392023803510601858707541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59393015616452345971521749 1392023803510601858707541)
                    ·
                      rfl

theorem cell22_4066435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_4066435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066435 prefixEnd_4066435 := by exact prefixLift 4066435
  have htrace : WordTrace (prefixWord ++ tailWord_4066435) baseStart_4066435 baseEnd_4066435 := by
    simpa [prefixWord, tailWord_4066435, baseEnd_4066435] using wordTrace_append hprefix tailTrace_4066435
  have hstable : (prefixWord ++ tailWord_4066435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066435).length < 2 ^ (prefixWord ++ tailWord_4066435).sum := by decide
  have hdescent : baseEnd_4066435 < baseStart_4066435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066467 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 1, 4]
def baseStart_4066467 : Nat := 118140960795 + 4066467 * 2 ^ 59
def prefixEnd_4066467 : Nat := 4983230072969 + 3 ^ 40 * 4066467 * 2
def baseEnd_4066467 : Nat := 1392034757764564441907443

theorem tailTrace_4066467 : CollatzResearch.WordTrace tailWord_4066467 prefixEnd_4066467 1392034757764564441907443 := by
  unfold tailWord_4066467
  simp only [CollatzResearch.WordTrace]
  refine ⟨148316236158892031116957655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98877490772594687411305103 148316236158892031116957655)
  ·
    refine ⟨222474354238338046675436483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148316236158892031116957655 222474354238338046675436483)
    ·
      refine ⟨333711531357507070013154725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222474354238338046675436483 333711531357507070013154725)
      ·
        refine ⟨62570912129532575627466511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333711531357507070013154725 62570912129532575627466511)
        ·
          refine ⟨93856368194298863441199767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62570912129532575627466511 93856368194298863441199767)
          ·
            refine ⟨140784552291448295161799651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93856368194298863441199767 140784552291448295161799651)
            ·
              refine ⟨211176828437172442742699477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140784552291448295161799651 211176828437172442742699477)
              ·
                refine ⟨4949456916496229126782019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 211176828437172442742699477 4949456916496229126782019)
                ·
                  refine ⟨7424185374744343690173029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949456916496229126782019 7424185374744343690173029)
                  ·
                    refine ⟨1392034757764564441907443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7424185374744343690173029 1392034757764564441907443)
                    ·
                      rfl

theorem cell22_4066467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 4].length) (baseStart_4066467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066467 prefixEnd_4066467 := by exact prefixLift 4066467
  have htrace : WordTrace (prefixWord ++ tailWord_4066467) baseStart_4066467 baseEnd_4066467 := by
    simpa [prefixWord, tailWord_4066467, baseEnd_4066467] using wordTrace_append hprefix tailTrace_4066467
  have hstable : (prefixWord ++ tailWord_4066467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066467).length < 2 ^ (prefixWord ++ tailWord_4066467).sum := by decide
  have hdescent : baseEnd_4066467 < baseStart_4066467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066514 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_4066514 : Nat := 118140960795 + 4066514 * 2 ^ 59
def prefixEnd_4066514 : Nat := 4983230072969 + 3 ^ 40 * 4066514 * 2
def baseEnd_4066514 : Nat := 1392050846825071985982299

theorem tailTrace_4066514 : CollatzResearch.WordTrace tailWord_4066514 prefixEnd_4066514 1392050846825071985982299 := by
  unfold tailWord_4066514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37079487597430439535979649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98878633593147838762612397 37079487597430439535979649)
  ·
    refine ⟨27809615698072829651984737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37079487597430439535979649 27809615698072829651984737)
    ·
      refine ⟨20857211773554622238988553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27809615698072829651984737 20857211773554622238988553)
      ·
        refine ⟨15642908830165966679241415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20857211773554622238988553 15642908830165966679241415)
        ·
          refine ⟨23464363245248950018862123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15642908830165966679241415 23464363245248950018862123)
          ·
            refine ⟨35196544867873425028293185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23464363245248950018862123 35196544867873425028293185)
            ·
              refine ⟨26397408650905068771219889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35196544867873425028293185 26397408650905068771219889)
              ·
                refine ⟨19798056488178801578414917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26397408650905068771219889 19798056488178801578414917)
                ·
                  refine ⟨3712135591533525295952797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19798056488178801578414917 3712135591533525295952797)
                  ·
                    refine ⟨1392050846825071985982299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712135591533525295952797 1392050846825071985982299)
                    ·
                      rfl

theorem cell22_4066514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_4066514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066514 prefixEnd_4066514 := by exact prefixLift 4066514
  have htrace : WordTrace (prefixWord ++ tailWord_4066514) baseStart_4066514 baseEnd_4066514 := by
    simpa [prefixWord, tailWord_4066514, baseEnd_4066514] using wordTrace_append hprefix tailTrace_4066514
  have hstable : (prefixWord ++ tailWord_4066514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066514).length < 2 ^ (prefixWord ++ tailWord_4066514).sum := by decide
  have hdescent : baseEnd_4066514 < baseStart_4066514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066518 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4066518 : Nat := 118140960795 + 4066518 * 2 ^ 59
def prefixEnd_4066518 : Nat := 4983230072969 + 3 ^ 40 * 4066518 * 2
def baseEnd_4066518 : Nat := 1392052216106817308882287

theorem tailTrace_4066518 : CollatzResearch.WordTrace tailWord_4066518 prefixEnd_4066518 1392052216106817308882287 := by
  unfold tailWord_4066518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269881017606704176691513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98878730854471511218042805 9269881017606704176691513)
  ·
    refine ⟨6952410763205028132518635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9269881017606704176691513 6952410763205028132518635)
    ·
      refine ⟨10428616144807542198777953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952410763205028132518635 10428616144807542198777953)
      ·
        refine ⟨7821462108605656649083465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10428616144807542198777953 7821462108605656649083465)
        ·
          refine ⟨5866096581454242486812599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7821462108605656649083465 5866096581454242486812599)
          ·
            refine ⟨8799144872181363730218899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866096581454242486812599 8799144872181363730218899)
            ·
              refine ⟨13198717308272045595328349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799144872181363730218899 13198717308272045595328349)
              ·
                refine ⟨4949518990602017098248131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13198717308272045595328349 4949518990602017098248131)
                ·
                  refine ⟨7424278485903025647372197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949518990602017098248131 7424278485903025647372197)
                  ·
                    refine ⟨1392052216106817308882287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7424278485903025647372197 1392052216106817308882287)
                    ·
                      rfl

theorem cell22_4066518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4066518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066518 prefixEnd_4066518 := by exact prefixLift 4066518
  have htrace : WordTrace (prefixWord ++ tailWord_4066518) baseStart_4066518 baseEnd_4066518 := by
    simpa [prefixWord, tailWord_4066518, baseEnd_4066518] using wordTrace_append hprefix tailTrace_4066518
  have hstable : (prefixWord ++ tailWord_4066518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066518).length < 2 ^ (prefixWord ++ tailWord_4066518).sum := by decide
  have hdescent : baseEnd_4066518 < baseStart_4066518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066559 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 3, 3]
def baseStart_4066559 : Nat := 118140960795 + 4066559 * 2 ^ 59
def prefixEnd_4066559 : Nat := 4983230072969 + 3 ^ 40 * 4066559 * 2
def baseEnd_4066559 : Nat := 1392066251244706868607161

theorem tailTrace_4066559 : CollatzResearch.WordTrace tailWord_4066559 prefixEnd_4066559 1392066251244706868607161 := by
  unfold tailWord_4066559
  simp only [CollatzResearch.WordTrace]
  refine ⟨148319591674558730829306731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98879727783039153886204487 148319591674558730829306731)
  ·
    refine ⟨222479387511838096243960097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148319591674558730829306731 222479387511838096243960097)
    ·
      refine ⟨166859540633878572182970073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222479387511838096243960097 166859540633878572182970073)
      ·
        refine ⟨125144655475408929137227555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166859540633878572182970073 125144655475408929137227555)
        ·
          refine ⟨187716983213113393705841333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125144655475408929137227555 187716983213113393705841333)
          ·
            refine ⟨17598467176229380659922625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187716983213113393705841333 17598467176229380659922625)
            ·
              refine ⟨13198850382172035494941969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17598467176229380659922625 13198850382172035494941969)
              ·
                refine ⟨9899137786629026621206477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13198850382172035494941969 9899137786629026621206477)
                ·
                  refine ⟨3712176669985884982952429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9899137786629026621206477 3712176669985884982952429)
                  ·
                    refine ⟨1392066251244706868607161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712176669985884982952429 1392066251244706868607161)
                    ·
                      rfl

theorem cell22_4066559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_4066559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066559 prefixEnd_4066559 := by exact prefixLift 4066559
  have htrace : WordTrace (prefixWord ++ tailWord_4066559) baseStart_4066559 baseEnd_4066559 := by
    simpa [prefixWord, tailWord_4066559, baseEnd_4066559] using wordTrace_append hprefix tailTrace_4066559
  have hstable : (prefixWord ++ tailWord_4066559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066559).length < 2 ^ (prefixWord ++ tailWord_4066559).sum := by decide
  have hdescent : baseEnd_4066559 < baseStart_4066559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066572 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_4066572 : Nat := 118140960795 + 4066572 * 2 ^ 59
def prefixEnd_4066572 : Nat := 4983230072969 + 3 ^ 40 * 4066572 * 2
def baseEnd_4066572 : Nat := 464023567136793056010707

theorem tailTrace_4066572 : CollatzResearch.WordTrace tailWord_4066572 prefixEnd_4066572 464023567136793056010707 := by
  unfold tailWord_4066572
  simp only [CollatzResearch.WordTrace]
  refine ⟨74160032911755817024764985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98880043882341089366353313 74160032911755817024764985)
  ·
    refine ⟨55620024683816862768573739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74160032911755817024764985 55620024683816862768573739)
    ·
      refine ⟨83430037025725294152860609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55620024683816862768573739 83430037025725294152860609)
      ·
        refine ⟨62572527769293970614645457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83430037025725294152860609 62572527769293970614645457)
        ·
          refine ⟨46929395826970477960984093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62572527769293970614645457 46929395826970477960984093)
          ·
            refine ⟨17598523435113929235369035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46929395826970477960984093 17598523435113929235369035)
            ·
              refine ⟨26397785152670893853053553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17598523435113929235369035 26397785152670893853053553)
              ·
                refine ⟨19798338864503170389790165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26397785152670893853053553 19798338864503170389790165)
                ·
                  refine ⟨464023567136793056010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19798338864503170389790165 464023567136793056010707)
                  ·
                    rfl

theorem cell22_4066572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_4066572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066572 prefixEnd_4066572 := by exact prefixLift 4066572
  have htrace : WordTrace (prefixWord ++ tailWord_4066572) baseStart_4066572 baseEnd_4066572 := by
    simpa [prefixWord, tailWord_4066572, baseEnd_4066572] using wordTrace_append hprefix tailTrace_4066572
  have hstable : (prefixWord ++ tailWord_4066572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066572).length < 2 ^ (prefixWord ++ tailWord_4066572).sum := by decide
  have hdescent : baseEnd_4066572 < baseStart_4066572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066578 : List Nat := [3, 2, 4, 2, 2, 1, 8]
def baseStart_4066578 : Nat := 118140960795 + 4066578 * 2 ^ 59
def prefixEnd_4066578 : Nat := 4983230072969 + 3 ^ 40 * 4066578 * 2
def baseEnd_4066578 : Nat := 51558250197518413051189

theorem tailTrace_4066578 : CollatzResearch.WordTrace tailWord_4066578 prefixEnd_4066578 51558250197518413051189 := by
  unfold tailWord_4066578
  simp only [CollatzResearch.WordTrace]
  refine ⟨37080071165372474268562097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98880189774326598049498925 37080071165372474268562097)
  ·
    refine ⟨27810053374029355701421573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37080071165372474268562097 27810053374029355701421573)
    ·
      refine ⟨5214385007630504194016545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27810053374029355701421573 5214385007630504194016545)
      ·
        refine ⟨3910788755722878145512409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5214385007630504194016545 3910788755722878145512409)
        ·
          refine ⟨2933091566792158609134307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910788755722878145512409 2933091566792158609134307)
          ·
            refine ⟨4399637350188237913701461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933091566792158609134307 4399637350188237913701461)
            ·
              refine ⟨51558250197518413051189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4399637350188237913701461 51558250197518413051189)
              ·
                rfl

theorem cell22_4066578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 8].length) (baseStart_4066578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066578 prefixEnd_4066578 := by exact prefixLift 4066578
  have htrace : WordTrace (prefixWord ++ tailWord_4066578) baseStart_4066578 baseEnd_4066578 := by
    simpa [prefixWord, tailWord_4066578, baseEnd_4066578] using wordTrace_append hprefix tailTrace_4066578
  have hstable : (prefixWord ++ tailWord_4066578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066578).length < 2 ^ (prefixWord ++ tailWord_4066578).sum := by decide
  have hdescent : baseEnd_4066578 < baseStart_4066578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066589 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 7]
def baseStart_4066589 : Nat := 118140960795 + 4066589 * 2 ^ 59
def prefixEnd_4066589 : Nat := 4983230072969 + 3 ^ 40 * 4066589 * 2
def baseEnd_4066589 : Nat := 464025506952598930119023

theorem tailTrace_4066589 : CollatzResearch.WordTrace tailWord_4066589 prefixEnd_4066589 464025506952598930119023 := by
  unfold tailWord_4066589
  simp only [CollatzResearch.WordTrace]
  refine ⟨148320685864450045952898821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98880457242966697301932547 148320685864450045952898821)
  ·
    refine ⟨27810128599584383616168529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148320685864450045952898821 27810128599584383616168529)
    ·
      refine ⟨20857596449688287712126397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27810128599584383616168529 20857596449688287712126397)
      ·
        refine ⟨7821598668633107892047399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20857596449688287712126397 7821598668633107892047399)
        ·
          refine ⟨11732398002949661838071099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821598668633107892047399 11732398002949661838071099)
          ·
            refine ⟨17598597004424492757106649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732398002949661838071099 17598597004424492757106649)
            ·
              refine ⟨13198947753318369567829987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17598597004424492757106649 13198947753318369567829987)
              ·
                refine ⟨19798421629977554351744981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13198947753318369567829987 19798421629977554351744981)
                ·
                  refine ⟨464025506952598930119023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19798421629977554351744981 464025506952598930119023)
                  ·
                    rfl

theorem cell22_4066589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_4066589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066589 prefixEnd_4066589 := by exact prefixLift 4066589
  have htrace : WordTrace (prefixWord ++ tailWord_4066589) baseStart_4066589 baseEnd_4066589 := by
    simpa [prefixWord, tailWord_4066589, baseEnd_4066589] using wordTrace_append hprefix tailTrace_4066589
  have hstable : (prefixWord ++ tailWord_4066589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066589).length < 2 ^ (prefixWord ++ tailWord_4066589).sum := by decide
  have hdescent : baseEnd_4066589 < baseStart_4066589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066649 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_4066649 : Nat := 118140960795 + 4066649 * 2 ^ 59
def prefixEnd_4066649 : Nat := 4983230072969 + 3 ^ 40 * 4066649 * 2
def baseEnd_4066649 : Nat := 1392097060083976633856885

theorem tailTrace_4066649 : CollatzResearch.WordTrace tailWord_4066649 prefixEnd_4066649 1392097060083976633856885 := by
  unfold tailWord_4066649
  simp only [CollatzResearch.WordTrace]
  refine ⟨148322874244232676200083001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98881916162821784133388667 148322874244232676200083001)
  ·
    refine ⟨111242155683174507150062251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148322874244232676200083001 111242155683174507150062251)
    ·
      refine ⟨166863233524761760725093377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111242155683174507150062251 166863233524761760725093377)
      ·
        refine ⟨125147425143571320543820033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166863233524761760725093377 125147425143571320543820033)
        ·
          refine ⟨93860568857678490407865025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125147425143571320543820033 93860568857678490407865025)
          ·
            refine ⟨70395426643258867805898769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93860568857678490407865025 70395426643258867805898769)
            ·
              refine ⟨52796569982444150854424077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70395426643258867805898769 52796569982444150854424077)
              ·
                refine ⟨19798713743416556570409029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52796569982444150854424077 19798713743416556570409029)
                ·
                  refine ⟨3712258826890604356951693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19798713743416556570409029 3712258826890604356951693)
                  ·
                    refine ⟨1392097060083976633856885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712258826890604356951693 1392097060083976633856885)
                    ·
                      rfl

theorem cell22_4066649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_4066649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066649 prefixEnd_4066649 := by exact prefixLift 4066649
  have htrace : WordTrace (prefixWord ++ tailWord_4066649) baseStart_4066649 baseEnd_4066649 := by
    simpa [prefixWord, tailWord_4066649, baseEnd_4066649] using wordTrace_append hprefix tailTrace_4066649
  have hstable : (prefixWord ++ tailWord_4066649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066649).length < 2 ^ (prefixWord ++ tailWord_4066649).sum := by decide
  have hdescent : baseEnd_4066649 < baseStart_4066649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066679 : List Nat := [1, 1, 3, 1, 1, 2, 7, 6]
def baseStart_4066679 : Nat := 118140960795 + 4066679 * 2 ^ 59
def prefixEnd_4066679 : Nat := 4983230072969 + 3 ^ 40 * 4066679 * 2
def baseEnd_4066679 : Nat := 154678592188562950622977

theorem tailTrace_4066679 : CollatzResearch.WordTrace tailWord_4066679 prefixEnd_4066679 154678592188562950622977 := by
  unfold tailWord_4066679
  simp only [CollatzResearch.WordTrace]
  refine ⟨148323968434123991323675091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98882645622749327549116727 148323968434123991323675091)
  ·
    refine ⟨222485952651185986985512637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148323968434123991323675091 222485952651185986985512637)
    ·
      refine ⟨83432232244194745119567239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222485952651185986985512637 83432232244194745119567239)
      ·
        refine ⟨125148348366292117679350859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83432232244194745119567239 125148348366292117679350859)
        ·
          refine ⟨187722522549438176519026289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125148348366292117679350859 187722522549438176519026289)
          ·
            refine ⟨140791891912078632389269717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187722522549438176519026289 140791891912078632389269717)
            ·
              refine ⟨3299809966689342946623509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140791891912078632389269717 3299809966689342946623509)
              ·
                refine ⟨154678592188562950622977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3299809966689342946623509 154678592188562950622977)
                ·
                  rfl

theorem cell22_4066679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 6].length) (baseStart_4066679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066679 prefixEnd_4066679 := by exact prefixLift 4066679
  have htrace : WordTrace (prefixWord ++ tailWord_4066679) baseStart_4066679 baseEnd_4066679 := by
    simpa [prefixWord, tailWord_4066679, baseEnd_4066679] using wordTrace_append hprefix tailTrace_4066679
  have hstable : (prefixWord ++ tailWord_4066679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066679).length < 2 ^ (prefixWord ++ tailWord_4066679).sum := by decide
  have hdescent : baseEnd_4066679 < baseStart_4066679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066799 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_4066799 : Nat := 118140960795 + 4066799 * 2 ^ 59
def prefixEnd_4066799 : Nat := 4983230072969 + 3 ^ 40 * 4066799 * 2
def baseEnd_4066799 : Nat := 1392148408149426242606425

theorem tailTrace_4066799 : CollatzResearch.WordTrace tailWord_4066799 prefixEnd_4066799 1392148408149426242606425 := by
  unfold tailWord_4066799
  simp only [CollatzResearch.WordTrace]
  refine ⟨148328345193689251818043451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98885563462459501212028967 148328345193689251818043451)
  ·
    refine ⟨222492517790533877727065177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148328345193689251818043451 222492517790533877727065177)
    ·
      refine ⟨166869388342900408295298883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222492517790533877727065177 166869388342900408295298883)
      ·
        refine ⟨250304082514350612442948325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166869388342900408295298883 250304082514350612442948325)
        ·
          refine ⟨46932015471440739833052811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250304082514350612442948325 46932015471440739833052811)
          ·
            refine ⟨70398023207161109749579217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46932015471440739833052811 70398023207161109749579217)
            ·
              refine ⟨52798517405370832312184413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70398023207161109749579217 52798517405370832312184413)
              ·
                refine ⟨19799444027014062117069155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52798517405370832312184413 19799444027014062117069155)
                ·
                  refine ⟨29699166040521093175603733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19799444027014062117069155 29699166040521093175603733)
                  ·
                    refine ⟨1392148408149426242606425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29699166040521093175603733 1392148408149426242606425)
                    ·
                      rfl

theorem cell22_4066799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_4066799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066799 prefixEnd_4066799 := by exact prefixLift 4066799
  have htrace : WordTrace (prefixWord ++ tailWord_4066799) baseStart_4066799 baseEnd_4066799 := by
    simpa [prefixWord, tailWord_4066799, baseEnd_4066799] using wordTrace_append hprefix tailTrace_4066799
  have hstable : (prefixWord ++ tailWord_4066799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066799).length < 2 ^ (prefixWord ++ tailWord_4066799).sum := by decide
  have hdescent : baseEnd_4066799 < baseStart_4066799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066801 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_4066801 : Nat := 118140960795 + 4066801 * 2 ^ 59
def prefixEnd_4066801 : Nat := 4983230072969 + 3 ^ 40 * 4066801 * 2
def baseEnd_4066801 : Nat := 1392149092790298904056419

theorem tailTrace_4066801 : CollatzResearch.WordTrace tailWord_4066801 prefixEnd_4066801 1392149092790298904056419 := by
  unfold tailWord_4066801
  simp only [CollatzResearch.WordTrace]
  refine ⟨148328418139682006159616257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98885612093121337439744171 148328418139682006159616257)
  ·
    refine ⟨111246313604761504619712193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148328418139682006159616257 111246313604761504619712193)
    ·
      refine ⟨83434735203571128464784145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111246313604761504619712193 83434735203571128464784145)
      ·
        refine ⟨62576051402678346348588109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83434735203571128464784145 62576051402678346348588109)
        ·
          refine ⟨23466019276004379880720541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62576051402678346348588109 23466019276004379880720541)
          ·
            refine ⟨8799757228501642455270203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23466019276004379880720541 8799757228501642455270203)
            ·
              refine ⟨13199635842752463682905305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799757228501642455270203 13199635842752463682905305)
              ·
                refine ⟨9899726882064347762178979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199635842752463682905305 9899726882064347762178979)
                ·
                  refine ⟨14849590323096521643268469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899726882064347762178979 14849590323096521643268469)
                  ·
                    refine ⟨1392149092790298904056419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14849590323096521643268469 1392149092790298904056419)
                    ·
                      rfl

theorem cell22_4066801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_4066801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066801 prefixEnd_4066801 := by exact prefixLift 4066801
  have htrace : WordTrace (prefixWord ++ tailWord_4066801) baseStart_4066801 baseEnd_4066801 := by
    simpa [prefixWord, tailWord_4066801, baseEnd_4066801] using wordTrace_append hprefix tailTrace_4066801
  have hstable : (prefixWord ++ tailWord_4066801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066801).length < 2 ^ (prefixWord ++ tailWord_4066801).sum := by decide
  have hdescent : baseEnd_4066801 < baseStart_4066801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066820 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_4066820 : Nat := 118140960795 + 4066820 * 2 ^ 59
def prefixEnd_4066820 : Nat := 4983230072969 + 3 ^ 40 * 4066820 * 2
def baseEnd_4066820 : Nat := 464051865626196395943787

theorem tailTrace_4066820 : CollatzResearch.WordTrace tailWord_4066820 prefixEnd_4066820 464051865626196395943787 := by
  unfold tailWord_4066820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74164555563306586202278957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98886074084408781603038609 74164555563306586202278957)
  ·
    refine ⟨27811708336239969825854609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74164555563306586202278957 27811708336239969825854609)
    ·
      refine ⟨20858781252179977369390957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27811708336239969825854609 20858781252179977369390957)
      ·
        refine ⟨7822042969567491513521609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20858781252179977369390957 7822042969567491513521609)
        ·
          refine ⟨5866532227175618635141207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7822042969567491513521609 5866532227175618635141207)
          ·
            refine ⟨8799798340763427952711811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866532227175618635141207 8799798340763427952711811)
            ·
              refine ⟨13199697511145141929067717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799798340763427952711811 13199697511145141929067717)
              ·
                refine ⟨2474943283339714111700197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13199697511145141929067717 2474943283339714111700197)
                ·
                  refine ⟨464051865626196395943787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474943283339714111700197 464051865626196395943787)
                  ·
                    rfl

theorem cell22_4066820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_4066820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066820 prefixEnd_4066820 := by exact prefixLift 4066820
  have htrace : WordTrace (prefixWord ++ tailWord_4066820) baseStart_4066820 baseEnd_4066820 := by
    simpa [prefixWord, tailWord_4066820, baseEnd_4066820] using wordTrace_append hprefix tailTrace_4066820
  have hstable : (prefixWord ++ tailWord_4066820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066820).length < 2 ^ (prefixWord ++ tailWord_4066820).sum := by decide
  have hdescent : baseEnd_4066820 < baseStart_4066820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066848 : List Nat := [2, 1, 1, 6, 1, 2, 3, 6]
def baseStart_4066848 : Nat := 118140960795 + 4066848 * 2 ^ 59
def prefixEnd_4066848 : Nat := 4983230072969 + 3 ^ 40 * 4066848 * 2
def baseEnd_4066848 : Nat := 154685020205645160903475

theorem tailTrace_4066848 : CollatzResearch.WordTrace tailWord_4066848 prefixEnd_4066848 154685020205645160903475 := by
  unfold tailWord_4066848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74165066185255866593288599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98886754913674488791051465 74165066185255866593288599)
  ·
    refine ⟨111247599277883799889932899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74165066185255866593288599 111247599277883799889932899)
    ·
      refine ⟨166871398916825699834899349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111247599277883799889932899 166871398916825699834899349)
      ·
        refine ⟨7822096824226204679760907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166871398916825699834899349 7822096824226204679760907)
        ·
          refine ⟨11733145236339307019641361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822096824226204679760907 11733145236339307019641361)
          ·
            refine ⟨8799858927254480264731021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11733145236339307019641361 8799858927254480264731021)
            ·
              refine ⟨3299947097720430099274133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8799858927254480264731021 3299947097720430099274133)
              ·
                refine ⟨154685020205645160903475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3299947097720430099274133 154685020205645160903475)
                ·
                  rfl

theorem cell22_4066848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_4066848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066848 prefixEnd_4066848 := by exact prefixLift 4066848
  have htrace : WordTrace (prefixWord ++ tailWord_4066848) baseStart_4066848 baseEnd_4066848 := by
    simpa [prefixWord, tailWord_4066848, baseEnd_4066848] using wordTrace_append hprefix tailTrace_4066848
  have hstable : (prefixWord ++ tailWord_4066848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066848).length < 2 ^ (prefixWord ++ tailWord_4066848).sum := by decide
  have hdescent : baseEnd_4066848 < baseStart_4066848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066906 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_4066906 : Nat := 118140960795 + 4066906 * 2 ^ 59
def prefixEnd_4066906 : Nat := 4983230072969 + 3 ^ 40 * 4066906 * 2
def baseEnd_4066906 : Nat := 1392185036436113630181097

theorem tailTrace_4066906 : CollatzResearch.WordTrace tailWord_4066906 prefixEnd_4066906 1392185036436113630181097 := by
  unfold tailWord_4066906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37083061951075402273047143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98888165202867739394792381 37083061951075402273047143)
  ·
    refine ⟨55624592926613103409570715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37083061951075402273047143 55624592926613103409570715)
    ·
      refine ⟨83436889389919655114356073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55624592926613103409570715 83436889389919655114356073)
      ·
        refine ⟨62577667042439741335767055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83436889389919655114356073 62577667042439741335767055)
        ·
          refine ⟨93866500563659612003650583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62577667042439741335767055 93866500563659612003650583)
          ·
            refine ⟨140799750845489418005475875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93866500563659612003650583 140799750845489418005475875)
            ·
              refine ⟨211199626268234127008213813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140799750845489418005475875 211199626268234127008213813)
              ·
                refine ⟨19799964962646949407020045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211199626268234127008213813 19799964962646949407020045)
                ·
                  refine ⟨7424986860992606027632517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19799964962646949407020045 7424986860992606027632517)
                  ·
                    refine ⟨1392185036436113630181097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7424986860992606027632517 1392185036436113630181097)
                    ·
                      rfl

theorem cell22_4066906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_4066906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066906 prefixEnd_4066906 := by exact prefixLift 4066906
  have htrace : WordTrace (prefixWord ++ tailWord_4066906) baseStart_4066906 baseEnd_4066906 := by
    simpa [prefixWord, tailWord_4066906, baseEnd_4066906] using wordTrace_append hprefix tailTrace_4066906
  have hstable : (prefixWord ++ tailWord_4066906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066906).length < 2 ^ (prefixWord ++ tailWord_4066906).sum := by decide
  have hdescent : baseEnd_4066906 < baseStart_4066906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066968 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_4066968 : Nat := 118140960795 + 4066968 * 2 ^ 59
def prefixEnd_4066968 : Nat := 4983230072969 + 3 ^ 40 * 4066968 * 2
def baseEnd_4066968 : Nat := 1392206260303166135130907

theorem tailTrace_4066968 : CollatzResearch.WordTrace tailWord_4066968 prefixEnd_4066968 1392206260303166135130907 := by
  unfold tailWord_4066968
  simp only [CollatzResearch.WordTrace]
  refine ⟨74167254565038496840472779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98889672753384662453963705 74167254565038496840472779)
  ·
    refine ⟨111250881847557745260709169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74167254565038496840472779 111250881847557745260709169)
    ·
      refine ⟨83438161385668308945531877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111250881847557745260709169 83438161385668308945531877)
      ·
        refine ⟨15644655259812807927287227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83438161385668308945531877 15644655259812807927287227)
        ·
          refine ⟨23466982889719211890930841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15644655259812807927287227 23466982889719211890930841)
          ·
            refine ⟨17600237167289408918198131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23466982889719211890930841 17600237167289408918198131)
            ·
              refine ⟨26400355750934113377297197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17600237167289408918198131 26400355750934113377297197)
              ·
                refine ⟨9900133406600292516486449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26400355750934113377297197 9900133406600292516486449)
                ·
                  refine ⟨7425100054950219387364837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900133406600292516486449 7425100054950219387364837)
                  ·
                    refine ⟨1392206260303166135130907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425100054950219387364837 1392206260303166135130907)
                    ·
                      rfl

theorem cell22_4066968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_4066968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4066968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4066968 prefixEnd_4066968 := by exact prefixLift 4066968
  have htrace : WordTrace (prefixWord ++ tailWord_4066968) baseStart_4066968 baseEnd_4066968 := by
    simpa [prefixWord, tailWord_4066968, baseEnd_4066968] using wordTrace_append hprefix tailTrace_4066968
  have hstable : (prefixWord ++ tailWord_4066968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066968).length < 2 ^ (prefixWord ++ tailWord_4066968).sum := by decide
  have hdescent : baseEnd_4066968 < baseStart_4066968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067032 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 1, 3]
def baseStart_4067032 : Nat := 118140960795 + 4067032 * 2 ^ 59
def prefixEnd_4067032 : Nat := 4983230072969 + 3 ^ 40 * 4067032 * 2
def baseEnd_4067032 : Nat := 1392228168811091301530711

theorem tailTrace_4067032 : CollatzResearch.WordTrace tailWord_4067032 prefixEnd_4067032 1392228168811091301530711 := by
  unfold tailWord_4067032
  simp only [CollatzResearch.WordTrace]
  refine ⟨74168421700922566305637675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98891228934563421740850233 74168421700922566305637675)
  ·
    refine ⟨111252632551383849458456513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74168421700922566305637675 111252632551383849458456513)
    ·
      refine ⟨83439474413537887093842385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111252632551383849458456513 83439474413537887093842385)
      ·
        refine ⟨62579605810153415320381789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83439474413537887093842385 62579605810153415320381789)
        ·
          refine ⟨23467352178807530745143171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62579605810153415320381789 23467352178807530745143171)
          ·
            refine ⟨35201028268211296117714757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23467352178807530745143171 35201028268211296117714757)
            ·
              refine ⟨6600192800289618022071517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35201028268211296117714757 6600192800289618022071517)
              ·
                refine ⟨2475072300108606758276819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6600192800289618022071517 2475072300108606758276819)
                ·
                  refine ⟨3712608450162910137415229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475072300108606758276819 3712608450162910137415229)
                  ·
                    refine ⟨1392228168811091301530711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712608450162910137415229 1392228168811091301530711)
                    ·
                      rfl

theorem cell22_4067032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_4067032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067032 prefixEnd_4067032 := by exact prefixLift 4067032
  have htrace : WordTrace (prefixWord ++ tailWord_4067032) baseStart_4067032 baseEnd_4067032 := by
    simpa [prefixWord, tailWord_4067032, baseEnd_4067032] using wordTrace_append hprefix tailTrace_4067032
  have hstable : (prefixWord ++ tailWord_4067032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067032).length < 2 ^ (prefixWord ++ tailWord_4067032).sum := by decide
  have hdescent : baseEnd_4067032 < baseStart_4067032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067062 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_4067062 : Nat := 118140960795 + 4067062 * 2 ^ 59
def prefixEnd_4067062 : Nat := 4983230072969 + 3 ^ 40 * 4067062 * 2
def baseEnd_4067062 : Nat := 464079479474727074426873

theorem tailTrace_4067062 : CollatzResearch.WordTrace tailWord_4067062 prefixEnd_4067062 464079479474727074426873 := by
  unfold tailWord_4067062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271121099483527983429215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98891958394490965156578293 9271121099483527983429215)
  ·
    refine ⟨13906681649225291975143823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9271121099483527983429215 13906681649225291975143823)
    ·
      refine ⟨20860022473837937962715735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13906681649225291975143823 20860022473837937962715735)
      ·
        refine ⟨31290033710756906944073603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20860022473837937962715735 31290033710756906944073603)
        ·
          refine ⟨46935050566135360416110405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31290033710756906944073603 46935050566135360416110405)
          ·
            refine ⟨8800321981150380078020701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46935050566135360416110405 8800321981150380078020701)
            ·
              refine ⟨3300120742931392529257763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8800321981150380078020701 3300120742931392529257763)
              ·
                refine ⟨4950181114397088793886645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300120742931392529257763 4950181114397088793886645)
                ·
                  refine ⟨464079479474727074426873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950181114397088793886645 464079479474727074426873)
                  ·
                    rfl

theorem cell22_4067062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_4067062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067062 prefixEnd_4067062 := by exact prefixLift 4067062
  have htrace : WordTrace (prefixWord ++ tailWord_4067062) baseStart_4067062 baseEnd_4067062 := by
    simpa [prefixWord, tailWord_4067062, baseEnd_4067062] using wordTrace_append hprefix tailTrace_4067062
  have hstable : (prefixWord ++ tailWord_4067062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067062).length < 2 ^ (prefixWord ++ tailWord_4067062).sum := by decide
  have hdescent : baseEnd_4067062 < baseStart_4067062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067073 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 6]
def baseStart_4067073 : Nat := 118140960795 + 4067073 * 2 ^ 59
def prefixEnd_4067073 : Nat := 4983230072969 + 3 ^ 40 * 4067073 * 2
def baseEnd_4067073 : Nat := 464080734649660287085195

theorem tailTrace_4067073 : CollatzResearch.WordTrace tailWord_4067073 prefixEnd_4067073 464080734649660287085195 := by
  unfold tailWord_4067073
  simp only [CollatzResearch.WordTrace]
  refine ⟨148338338794696596613517873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98892225863131064409011915 148338338794696596613517873)
  ·
    refine ⟨111253754096022447460138405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148338338794696596613517873 111253754096022447460138405)
    ·
      refine ⟨20860078893004208898775951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111253754096022447460138405 20860078893004208898775951)
      ·
        refine ⟨31290118339506313348163927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20860078893004208898775951 31290118339506313348163927)
        ·
          refine ⟨46935177509259470022245891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31290118339506313348163927 46935177509259470022245891)
          ·
            refine ⟨70402766263889205033368837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46935177509259470022245891 70402766263889205033368837)
            ·
              refine ⟨13200518674479225943756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70402766263889205033368837 13200518674479225943756657)
              ·
                refine ⟨9900389005859419457817493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200518674479225943756657 9900389005859419457817493)
                ·
                  refine ⟨464080734649660287085195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9900389005859419457817493 464080734649660287085195)
                  ·
                    rfl

theorem cell22_4067073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_4067073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067073 prefixEnd_4067073 := by exact prefixLift 4067073
  have htrace : WordTrace (prefixWord ++ tailWord_4067073) baseStart_4067073 baseEnd_4067073 := by
    simpa [prefixWord, tailWord_4067073, baseEnd_4067073] using wordTrace_append hprefix tailTrace_4067073
  have hstable : (prefixWord ++ tailWord_4067073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067073).length < 2 ^ (prefixWord ++ tailWord_4067073).sum := by decide
  have hdescent : baseEnd_4067073 < baseStart_4067073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067105 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_4067105 : Nat := 118140960795 + 4067105 * 2 ^ 59
def prefixEnd_4067105 : Nat := 4983230072969 + 3 ^ 40 * 4067105 * 2
def baseEnd_4067105 : Nat := 1392253158202943444455487

theorem tailTrace_4067105 : CollatzResearch.WordTrace tailWord_4067105 prefixEnd_4067105 1392253158202943444455487 := by
  unfold tailWord_4067105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148339505930580666078682769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98893003953720444052455179 148339505930580666078682769)
  ·
    refine ⟨111254629447935499559012077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148339505930580666078682769 111254629447935499559012077)
    ·
      refine ⟨41720486042975812334629529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111254629447935499559012077 41720486042975812334629529)
      ·
        refine ⟨31290364532231859250972147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41720486042975812334629529 31290364532231859250972147)
        ·
          refine ⟨46935546798347788876458221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31290364532231859250972147 46935546798347788876458221)
          ·
            refine ⟨17600830049380420828671833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46935546798347788876458221 17600830049380420828671833)
            ·
              refine ⟨13200622537035315621503875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17600830049380420828671833 13200622537035315621503875)
              ·
                refine ⟨19800933805552973432255813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13200622537035315621503875 19800933805552973432255813)
                ·
                  refine ⟨3712675088541182518547965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19800933805552973432255813 3712675088541182518547965)
                  ·
                    refine ⟨1392253158202943444455487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712675088541182518547965 1392253158202943444455487)
                    ·
                      rfl

theorem cell22_4067105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_4067105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067105 prefixEnd_4067105 := by exact prefixLift 4067105
  have htrace : WordTrace (prefixWord ++ tailWord_4067105) baseStart_4067105 baseEnd_4067105 := by
    simpa [prefixWord, tailWord_4067105, baseEnd_4067105] using wordTrace_append hprefix tailTrace_4067105
  have hstable : (prefixWord ++ tailWord_4067105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067105).length < 2 ^ (prefixWord ++ tailWord_4067105).sum := by decide
  have hdescent : baseEnd_4067105 < baseStart_4067105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067122 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_4067122 : Nat := 118140960795 + 4067122 * 2 ^ 59
def prefixEnd_4067122 : Nat := 4983230072969 + 3 ^ 40 * 4067122 * 2
def baseEnd_4067122 : Nat := 1392258977650361066780435

theorem tailTrace_4067122 : CollatzResearch.WordTrace tailWord_4067122 prefixEnd_4067122 1392258977650361066780435 := by
  unfold tailWord_4067122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37085031492879769495512905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98893417314346051988034413 37085031492879769495512905)
  ·
    refine ⟨27813773619659827121634679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37085031492879769495512905 27813773619659827121634679)
    ·
      refine ⟨41720660429489740682452019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27813773619659827121634679 41720660429489740682452019)
      ·
        refine ⟨62580990644234611023678029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41720660429489740682452019 62580990644234611023678029)
        ·
          refine ⟨23467871491587979133879261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62580990644234611023678029 23467871491587979133879261)
          ·
            refine ⟨8800451809345492175204723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23467871491587979133879261 8800451809345492175204723)
            ·
              refine ⟨13200677714018238262807085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800451809345492175204723 13200677714018238262807085)
              ·
                refine ⟨4950254142756839348552657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13200677714018238262807085 4950254142756839348552657)
                ·
                  refine ⟨3712690607067629511414493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950254142756839348552657 3712690607067629511414493)
                  ·
                    refine ⟨1392258977650361066780435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3712690607067629511414493 1392258977650361066780435)
                    ·
                      rfl

theorem cell22_4067122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_4067122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067122 prefixEnd_4067122 := by exact prefixLift 4067122
  have htrace : WordTrace (prefixWord ++ tailWord_4067122) baseStart_4067122 baseEnd_4067122 := by
    simpa [prefixWord, tailWord_4067122, baseEnd_4067122] using wordTrace_append hprefix tailTrace_4067122
  have hstable : (prefixWord ++ tailWord_4067122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067122).length < 2 ^ (prefixWord ++ tailWord_4067122).sum := by decide
  have hdescent : baseEnd_4067122 < baseStart_4067122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067180 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_4067180 : Nat := 118140960795 + 4067180 * 2 ^ 59
def prefixEnd_4067180 : Nat := 4983230072969 + 3 ^ 40 * 4067180 * 2
def baseEnd_4067180 : Nat := 464092944078556082943419

theorem tailTrace_4067180 : CollatzResearch.WordTrace tailWord_4067180 prefixEnd_4067180 464092944078556082943419 := by
  unfold tailWord_4067180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74171120702654476943831497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98894827603539302591775329 74171120702654476943831497)
  ·
    refine ⟨55628340526990857707873623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74171120702654476943831497 55628340526990857707873623)
    ·
      refine ⟨83442510790486286561810435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55628340526990857707873623 83442510790486286561810435)
      ·
        refine ⟨125163766185729429842715653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83442510790486286561810435 125163766185729429842715653)
        ·
          refine ⟨23468206159824268095509185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125163766185729429842715653 23468206159824268095509185)
          ·
            refine ⟨17601154619868201071631889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23468206159824268095509185 17601154619868201071631889)
            ·
              refine ⟨13200865964901150803723917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17601154619868201071631889 13200865964901150803723917)
              ·
                refine ⟨4950324736837931551396469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13200865964901150803723917 4950324736837931551396469)
                ·
                  refine ⟨464092944078556082943419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950324736837931551396469 464092944078556082943419)
                  ·
                    rfl

theorem cell22_4067180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_4067180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067180 prefixEnd_4067180 := by exact prefixLift 4067180
  have htrace : WordTrace (prefixWord ++ tailWord_4067180) baseStart_4067180 baseEnd_4067180 := by
    simpa [prefixWord, tailWord_4067180, baseEnd_4067180] using wordTrace_append hprefix tailTrace_4067180
  have hstable : (prefixWord ++ tailWord_4067180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067180).length < 2 ^ (prefixWord ++ tailWord_4067180).sum := by decide
  have hdescent : baseEnd_4067180 < baseStart_4067180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067255 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_4067255 : Nat := 118140960795 + 4067255 * 2 ^ 59
def prefixEnd_4067255 : Nat := 4983230072969 + 3 ^ 40 * 4067255 * 2
def baseEnd_4067255 : Nat := 1392304506268393053205027

theorem tailTrace_4067255 : CollatzResearch.WordTrace tailWord_4067255 prefixEnd_4067255 1392304506268393053205027 := by
  unfold tailWord_4067255
  simp only [CollatzResearch.WordTrace]
  refine ⟨148344976880037241696643219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98896651253358161131095479 148344976880037241696643219)
  ·
    refine ⟨222517465320055862544964829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148344976880037241696643219 222517465320055862544964829)
    ·
      refine ⟨83444049495020948454361811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222517465320055862544964829 83444049495020948454361811)
      ·
        refine ⟨125166074242531422681542717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83444049495020948454361811 125166074242531422681542717)
        ·
          refine ⟨46937277840949283505578519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125166074242531422681542717 46937277840949283505578519)
          ·
            refine ⟨70405916761423925258367779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46937277840949283505578519 70405916761423925258367779)
            ·
              refine ⟨105608875142135887887551669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70405916761423925258367779 105608875142135887887551669)
              ·
                refine ⟨9900832044575239489457969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105608875142135887887551669 9900832044575239489457969)
                ·
                  refine ⟨7425624033431429617093477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900832044575239489457969 7425624033431429617093477)
                  ·
                    refine ⟨1392304506268393053205027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425624033431429617093477 1392304506268393053205027)
                    ·
                      rfl

theorem cell22_4067255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_4067255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067255 prefixEnd_4067255 := by exact prefixLift 4067255
  have htrace : WordTrace (prefixWord ++ tailWord_4067255) baseStart_4067255 baseEnd_4067255 := by
    simpa [prefixWord, tailWord_4067255, baseEnd_4067255] using wordTrace_append hprefix tailTrace_4067255
  have hstable : (prefixWord ++ tailWord_4067255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067255).length < 2 ^ (prefixWord ++ tailWord_4067255).sum := by decide
  have hdescent : baseEnd_4067255 < baseStart_4067255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067272 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4067272 : Nat := 118140960795 + 4067272 * 2 ^ 59
def prefixEnd_4067272 : Nat := 4983230072969 + 3 ^ 40 * 4067272 * 2
def baseEnd_4067272 : Nat := 1392310325715810675529975

theorem tailTrace_4067272 : CollatzResearch.WordTrace tailWord_4067272 prefixEnd_4067272 1392310325715810675529975 := by
  unfold tailWord_4067272
  simp only [CollatzResearch.WordTrace]
  refine ⟨74172798460487826800006035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98897064613983769066674713 74172798460487826800006035)
  ·
    refine ⟨111259197690731740200009053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74172798460487826800006035 111259197690731740200009053)
    ·
      refine ⟨41722199134024402575003395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111259197690731740200009053 41722199134024402575003395)
      ·
        refine ⟨62583298701036603862505093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41722199134024402575003395 62583298701036603862505093)
        ·
          refine ⟨11734368506444363224219705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62583298701036603862505093 11734368506444363224219705)
          ·
            refine ⟨8800776379833272418164779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11734368506444363224219705 8800776379833272418164779)
            ·
              refine ⟨13201164569749908627247169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800776379833272418164779 13201164569749908627247169)
              ·
                refine ⟨9900873427312431470435377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13201164569749908627247169 9900873427312431470435377)
                ·
                  refine ⟨7425655070484323602826533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9900873427312431470435377 7425655070484323602826533)
                  ·
                    refine ⟨1392310325715810675529975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425655070484323602826533 1392310325715810675529975)
                    ·
                      rfl

theorem cell22_4067272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4067272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067272 prefixEnd_4067272 := by exact prefixLift 4067272
  have htrace : WordTrace (prefixWord ++ tailWord_4067272) baseStart_4067272 baseEnd_4067272 := by
    simpa [prefixWord, tailWord_4067272, baseEnd_4067272] using wordTrace_append hprefix tailTrace_4067272
  have hstable : (prefixWord ++ tailWord_4067272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067272).length < 2 ^ (prefixWord ++ tailWord_4067272).sum := by decide
  have hdescent : baseEnd_4067272 < baseStart_4067272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067362 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4067362 : Nat := 118140960795 + 4067362 * 2 ^ 59
def prefixEnd_4067362 : Nat := 4983230072969 + 3 ^ 40 * 4067362 * 2
def baseEnd_4067362 : Nat := 1392341134555080440779699

theorem tailTrace_4067362 : CollatzResearch.WordTrace tailWord_4067362 prefixEnd_4067362 1392341134555080440779699 := by
  unfold tailWord_4067362
  simp only [CollatzResearch.WordTrace]
  refine ⟨37087219872662399742697085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98899252993766399313858893 37087219872662399742697085)
  ·
    refine ⟨13907707452248399903511407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37087219872662399742697085 13907707452248399903511407)
    ·
      refine ⟨20861561178372599855267111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13907707452248399903511407 20861561178372599855267111)
      ·
        refine ⟨31292341767558899782900667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20861561178372599855267111 31292341767558899782900667)
        ·
          refine ⟨46938512651338349674351001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31292341767558899782900667 46938512651338349674351001)
          ·
            refine ⟨35203884488503762255763251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46938512651338349674351001 35203884488503762255763251)
            ·
              refine ⟨52805826732755643383644877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35203884488503762255763251 52805826732755643383644877)
              ·
                refine ⟨19802185024783366268866829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52805826732755643383644877 19802185024783366268866829)
                ·
                  refine ⟨7425819384293762350825061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19802185024783366268866829 7425819384293762350825061)
                  ·
                    refine ⟨1392341134555080440779699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425819384293762350825061 1392341134555080440779699)
                    ·
                      rfl

theorem cell22_4067362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4067362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067362 prefixEnd_4067362 := by exact prefixLift 4067362
  have htrace : WordTrace (prefixWord ++ tailWord_4067362) baseStart_4067362 baseEnd_4067362 := by
    simpa [prefixWord, tailWord_4067362, baseEnd_4067362] using wordTrace_append hprefix tailTrace_4067362
  have hstable : (prefixWord ++ tailWord_4067362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067362).length < 2 ^ (prefixWord ++ tailWord_4067362).sum := by decide
  have hdescent : baseEnd_4067362 < baseStart_4067362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067375 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_4067375 : Nat := 118140960795 + 4067375 * 2 ^ 59
def prefixEnd_4067375 : Nat := 4983230072969 + 3 ^ 40 * 4067375 * 2
def baseEnd_4067375 : Nat := 1392345584720752740204659

theorem tailTrace_4067375 : CollatzResearch.WordTrace tailWord_4067375 prefixEnd_4067375 1392345584720752740204659 := by
  unfold tailWord_4067375
  simp only [CollatzResearch.WordTrace]
  refine ⟨148349353639602502191011579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98899569093068334794007719 148349353639602502191011579)
  ·
    refine ⟨222524030459403753286517369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148349353639602502191011579 222524030459403753286517369)
    ·
      refine ⟨166893022844552814964888027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222524030459403753286517369 166893022844552814964888027)
      ·
        refine ⟨250339534266829222447332041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166893022844552814964888027 250339534266829222447332041)
        ·
          refine ⟨187754650700121916835499031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250339534266829222447332041 187754650700121916835499031)
          ·
            refine ⟨281631976050182875253248547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187754650700121916835499031 281631976050182875253248547)
            ·
              refine ⟨422447964075274312879872821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281631976050182875253248547 422447964075274312879872821)
              ·
                refine ⟨39604496632056966832488077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 422447964075274312879872821 39604496632056966832488077)
                ·
                  refine ⟨14851686237021362562183029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39604496632056966832488077 14851686237021362562183029)
                  ·
                    refine ⟨1392345584720752740204659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14851686237021362562183029 1392345584720752740204659)
                    ·
                      rfl

theorem cell22_4067375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_4067375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067375 prefixEnd_4067375 := by exact prefixLift 4067375
  have htrace : WordTrace (prefixWord ++ tailWord_4067375) baseStart_4067375 baseEnd_4067375 := by
    simpa [prefixWord, tailWord_4067375, baseEnd_4067375] using wordTrace_append hprefix tailTrace_4067375
  have hstable : (prefixWord ++ tailWord_4067375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067375).length < 2 ^ (prefixWord ++ tailWord_4067375).sum := by decide
  have hdescent : baseEnd_4067375 < baseStart_4067375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067379 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 1, 4]
def baseStart_4067379 : Nat := 118140960795 + 4067379 * 2 ^ 59
def prefixEnd_4067379 : Nat := 4983230072969 + 3 ^ 40 * 4067379 * 2
def baseEnd_4067379 : Nat := 1392346954002498063104647

theorem tailTrace_4067379 : CollatzResearch.WordTrace tailWord_4067379 prefixEnd_4067379 1392346954002498063104647 := by
  unfold tailWord_4067379
  simp only [CollatzResearch.WordTrace]
  refine ⟨148349499531588010874157191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98899666354392007249438127 148349499531588010874157191)
  ·
    refine ⟨222524249297382016311235787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148349499531588010874157191 222524249297382016311235787)
    ·
      refine ⟨333786373946073024466853681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222524249297382016311235787 333786373946073024466853681)
      ·
        refine ⟨250339780459554768350140261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333786373946073024466853681 250339780459554768350140261)
        ·
          refine ⟨46938708836166519065651299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250339780459554768350140261 46938708836166519065651299)
          ·
            refine ⟨70408063254249778598476949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46938708836166519065651299 70408063254249778598476949)
            ·
              refine ⟨3300377965042958371803607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70408063254249778598476949 3300377965042958371803607)
              ·
                refine ⟨4950566947564437557705411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300377965042958371803607 4950566947564437557705411)
                ·
                  refine ⟨7425850421346656336558117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950566947564437557705411 7425850421346656336558117)
                  ·
                    refine ⟨1392346954002498063104647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7425850421346656336558117 1392346954002498063104647)
                    ·
                      rfl

theorem cell22_4067379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 4].length) (baseStart_4067379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067379 prefixEnd_4067379 := by exact prefixLift 4067379
  have htrace : WordTrace (prefixWord ++ tailWord_4067379) baseStart_4067379 baseEnd_4067379 := by
    simpa [prefixWord, tailWord_4067379, baseEnd_4067379] using wordTrace_append hprefix tailTrace_4067379
  have hstable : (prefixWord ++ tailWord_4067379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067379).length < 2 ^ (prefixWord ++ tailWord_4067379).sum := by decide
  have hdescent : baseEnd_4067379 < baseStart_4067379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067501 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 5]
def baseStart_4067501 : Nat := 118140960795 + 4067501 * 2 ^ 59
def prefixEnd_4067501 : Nat := 4983230072969 + 3 ^ 40 * 4067501 * 2
def baseEnd_4067501 : Nat := 464129572365243470518091

theorem tailTrace_4067501 : CollatzResearch.WordTrace tailWord_4067501 prefixEnd_4067501 464129572365243470518091 := by
  unfold tailWord_4067501
  simp only [CollatzResearch.WordTrace]
  refine ⟨148353949237146025710098357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98902632824764017140065571 148353949237146025710098357)
  ·
    refine ⟨13908182740982439910321721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148353949237146025710098357 13908182740982439910321721)
    ·
      refine ⟨10431137055736829932741291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13908182740982439910321721 10431137055736829932741291)
      ·
        refine ⟨15646705583605244899111937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431137055736829932741291 15646705583605244899111937)
        ·
          refine ⟨11735029187703933674333953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15646705583605244899111937 11735029187703933674333953)
          ·
            refine ⟨8801271890777950255750465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11735029187703933674333953 8801271890777950255750465)
            ·
              refine ⟨6600953918083462691812849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8801271890777950255750465 6600953918083462691812849)
              ·
                refine ⟨4950715438562597018859637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6600953918083462691812849 4950715438562597018859637)
                ·
                  refine ⟨464129572365243470518091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950715438562597018859637 464129572365243470518091)
                  ·
                    rfl

theorem cell22_4067501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_4067501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067501 prefixEnd_4067501 := by exact prefixLift 4067501
  have htrace : WordTrace (prefixWord ++ tailWord_4067501) baseStart_4067501 baseEnd_4067501 := by
    simpa [prefixWord, tailWord_4067501, baseEnd_4067501] using wordTrace_append hprefix tailTrace_4067501
  have hstable : (prefixWord ++ tailWord_4067501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067501).length < 2 ^ (prefixWord ++ tailWord_4067501).sum := by decide
  have hdescent : baseEnd_4067501 < baseStart_4067501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067512 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_4067512 : Nat := 118140960795 + 4067512 * 2 ^ 59
def prefixEnd_4067512 : Nat := 4983230072969 + 3 ^ 40 * 4067512 * 2
def baseEnd_4067512 : Nat := 464130827540176683176413

theorem tailTrace_4067512 : CollatzResearch.WordTrace tailWord_4067512 prefixEnd_4067512 464130827540176683176413 := by
  unfold tailWord_4067512
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177175220053087294374395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98902900293404116392499193 74177175220053087294374395)
  ·
    refine ⟨111265762830079630941561593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74177175220053087294374395 111265762830079630941561593)
    ·
      refine ⟨83449322122559723206171195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111265762830079630941561593 83449322122559723206171195)
      ·
        refine ⟨125173983183839584809256793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83449322122559723206171195 125173983183839584809256793)
        ·
          refine ⟨93880487387879688606942595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125173983183839584809256793 93880487387879688606942595)
          ·
            refine ⟨140820731081819532910413893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93880487387879688606942595 140820731081819532910413893)
            ·
              refine ⟨26403887077841162420702605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140820731081819532910413893 26403887077841162420702605)
              ·
                refine ⟨9901457654190435907763477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26403887077841162420702605 9901457654190435907763477)
                ·
                  refine ⟨464130827540176683176413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9901457654190435907763477 464130827540176683176413)
                  ·
                    rfl

theorem cell22_4067512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_4067512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067512 prefixEnd_4067512 := by exact prefixLift 4067512
  have htrace : WordTrace (prefixWord ++ tailWord_4067512) baseStart_4067512 baseEnd_4067512 := by
    simpa [prefixWord, tailWord_4067512, baseEnd_4067512] using wordTrace_append hprefix tailTrace_4067512
  have hstable : (prefixWord ++ tailWord_4067512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067512).length < 2 ^ (prefixWord ++ tailWord_4067512).sum := by decide
  have hdescent : baseEnd_4067512 < baseStart_4067512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067544 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_4067544 : Nat := 118140960795 + 4067544 * 2 ^ 59
def prefixEnd_4067544 : Nat := 4983230072969 + 3 ^ 40 * 4067544 * 2
def baseEnd_4067544 : Nat := 1392403436874492632729141

theorem tailTrace_4067544 : CollatzResearch.WordTrace tailWord_4067544 prefixEnd_4067544 1392403436874492632729141 := by
  unfold tailWord_4067544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177758787995122026956843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98903678383993496035942457 74177758787995122026956843)
  ·
    refine ⟨111266638181992683040435265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74177758787995122026956843 111266638181992683040435265)
    ·
      refine ⟨83449978636494512280326449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111266638181992683040435265 83449978636494512280326449)
      ·
        refine ⟨62587483977370884210244837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83449978636494512280326449 62587483977370884210244837)
        ·
          refine ⟨11735153245757040789420907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62587483977370884210244837 11735153245757040789420907)
          ·
            refine ⟨17602729868635561184131361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735153245757040789420907 17602729868635561184131361)
            ·
              refine ⟨13202047401476670888098521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17602729868635561184131361 13202047401476670888098521)
              ·
                refine ⟨9901535551107503166073891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13202047401476670888098521 9901535551107503166073891)
                ·
                  refine ⟨14852303326661254749110837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901535551107503166073891 14852303326661254749110837)
                  ·
                    refine ⟨1392403436874492632729141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14852303326661254749110837 1392403436874492632729141)
                    ·
                      rfl

theorem cell22_4067544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_4067544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067544 prefixEnd_4067544 := by exact prefixLift 4067544
  have htrace : WordTrace (prefixWord ++ tailWord_4067544) baseStart_4067544 baseEnd_4067544 := by
    simpa [prefixWord, tailWord_4067544, baseEnd_4067544] using wordTrace_append hprefix tailTrace_4067544
  have hstable : (prefixWord ++ tailWord_4067544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067544).length < 2 ^ (prefixWord ++ tailWord_4067544).sum := by decide
  have hdescent : baseEnd_4067544 < baseStart_4067544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067578 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_4067578 : Nat := 118140960795 + 4067578 * 2 ^ 59
def prefixEnd_4067578 : Nat := 4983230072969 + 3 ^ 40 * 4067578 * 2
def baseEnd_4067578 : Nat := 1392415075769327877379037

theorem tailTrace_4067578 : CollatzResearch.WordTrace tailWord_4067578 prefixEnd_4067578 1392415075769327877379037 := by
  unfold tailWord_4067578
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089189414466766965162847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98904505105244711907100925 37089189414466766965162847)
  ·
    refine ⟨55633784121700150447744271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089189414466766965162847 55633784121700150447744271)
    ·
      refine ⟨83450676182550225671616407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55633784121700150447744271 83450676182550225671616407)
      ·
        refine ⟨125176014273825338507424611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83450676182550225671616407 125176014273825338507424611)
        ·
          refine ⟨187764021410738007761136917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125176014273825338507424611 187764021410738007761136917)
          ·
            refine ⟨8801438503628344113803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187764021410738007761136917 8801438503628344113803293)
            ·
              refine ⟨3300539438860629042676235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8801438503628344113803293 3300539438860629042676235)
              ·
                refine ⟨4950809158290943564014353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300539438860629042676235 4950809158290943564014353)
                ·
                  refine ⟨3713106868718207673010765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950809158290943564014353 3713106868718207673010765)
                  ·
                    refine ⟨1392415075769327877379037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713106868718207673010765 1392415075769327877379037)
                    ·
                      rfl

theorem cell22_4067578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_4067578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067578 prefixEnd_4067578 := by exact prefixLift 4067578
  have htrace : WordTrace (prefixWord ++ tailWord_4067578) baseStart_4067578 baseEnd_4067578 := by
    simpa [prefixWord, tailWord_4067578, baseEnd_4067578] using wordTrace_append hprefix tailTrace_4067578
  have hstable : (prefixWord ++ tailWord_4067578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067578).length < 2 ^ (prefixWord ++ tailWord_4067578).sum := by decide
  have hdescent : baseEnd_4067578 < baseStart_4067578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067589 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_4067589 : Nat := 118140960795 + 4067589 * 2 ^ 59
def prefixEnd_4067589 : Nat := 4983230072969 + 3 ^ 40 * 4067589 * 2
def baseEnd_4067589 : Nat := 1392418841294127515354003

theorem tailTrace_4067589 : CollatzResearch.WordTrace tailWord_4067589 prefixEnd_4067589 1392418841294127515354003 := by
  unfold tailWord_4067589
  simp only [CollatzResearch.WordTrace]
  refine ⟨148357158860827216739301821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98904772573884811159534547 148357158860827216739301821)
  ·
    refine ⟨55633934572810206277238183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148357158860827216739301821 55633934572810206277238183)
    ·
      refine ⟨83450901859215309415857275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55633934572810206277238183 83450901859215309415857275)
      ·
        refine ⟨125176352788822964123785913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83450901859215309415857275 125176352788822964123785913)
        ·
          refine ⟨93882264591617223092839435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125176352788822964123785913 93882264591617223092839435)
          ·
            refine ⟨140823396887425834639259153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93882264591617223092839435 140823396887425834639259153)
            ·
              refine ⟨105617547665569375979444365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140823396887425834639259153 105617547665569375979444365)
              ·
                refine ⟨39606580374588515992291637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105617547665569375979444365 39606580374588515992291637)
                ·
                  refine ⟨3713116910117673374277341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39606580374588515992291637 3713116910117673374277341)
                  ·
                    refine ⟨1392418841294127515354003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713116910117673374277341 1392418841294127515354003)
                    ·
                      rfl

theorem cell22_4067589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_4067589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067589 prefixEnd_4067589 := by exact prefixLift 4067589
  have htrace : WordTrace (prefixWord ++ tailWord_4067589) baseStart_4067589 baseEnd_4067589 := by
    simpa [prefixWord, tailWord_4067589, baseEnd_4067589] using wordTrace_append hprefix tailTrace_4067589
  have hstable : (prefixWord ++ tailWord_4067589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067589).length < 2 ^ (prefixWord ++ tailWord_4067589).sum := by decide
  have hdescent : baseEnd_4067589 < baseStart_4067589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067591 : List Nat := [1, 1, 4, 5, 1, 1, 1, 8]
def baseStart_4067591 : Nat := 118140960795 + 4067591 * 2 ^ 59
def prefixEnd_4067591 : Nat := 4983230072969 + 3 ^ 40 * 4067591 * 2
def baseEnd_4067591 : Nat := 154713280659444464089333

theorem tailTrace_4067591 : CollatzResearch.WordTrace tailWord_4067591 prefixEnd_4067591 154713280659444464089333 := by
  unfold tailWord_4067591
  simp only [CollatzResearch.WordTrace]
  refine ⟨148357231806819971080874627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98904821204546647387249751 148357231806819971080874627)
  ·
    refine ⟨222535847710229956621311941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148357231806819971080874627 222535847710229956621311941)
    ·
      refine ⟨41725471445668116866495989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222535847710229956621311941 41725471445668116866495989)
      ·
        refine ⟨3911762948031385956233999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41725471445668116866495989 3911762948031385956233999)
        ·
          refine ⟨5867644422047078934350999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911762948031385956233999 5867644422047078934350999)
          ·
            refine ⟨8801466633070618401526499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867644422047078934350999 8801466633070618401526499)
            ·
              refine ⟨13202199949605927602289749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801466633070618401526499 13202199949605927602289749)
              ·
                refine ⟨154713280659444464089333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13202199949605927602289749 154713280659444464089333)
                ·
                  rfl

theorem cell22_4067591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 8].length) (baseStart_4067591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067591 prefixEnd_4067591 := by exact prefixLift 4067591
  have htrace : WordTrace (prefixWord ++ tailWord_4067591) baseStart_4067591 baseEnd_4067591 := by
    simpa [prefixWord, tailWord_4067591, baseEnd_4067591] using wordTrace_append hprefix tailTrace_4067591
  have hstable : (prefixWord ++ tailWord_4067591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067591).length < 2 ^ (prefixWord ++ tailWord_4067591).sum := by decide
  have hdescent : baseEnd_4067591 < baseStart_4067591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067619 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 5]
def baseStart_4067619 : Nat := 118140960795 + 4067619 * 2 ^ 59
def prefixEnd_4067619 : Nat := 4983230072969 + 3 ^ 40 * 4067619 * 2
def baseEnd_4067619 : Nat := 464143036969072479034637

theorem tailTrace_4067619 : CollatzResearch.WordTrace tailWord_4067619 prefixEnd_4067619 464143036969072479034637 := by
  unfold tailWord_4067619
  simp only [CollatzResearch.WordTrace]
  refine ⟨148358253050718531862893911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98905502033812354575262607 148358253050718531862893911)
  ·
    refine ⟨222537379576077797794340867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148358253050718531862893911 222537379576077797794340867)
    ·
      refine ⟨333806069364116696691511301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222537379576077797794340867 333806069364116696691511301)
      ·
        refine ⟨62588638005771880629658369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333806069364116696691511301 62588638005771880629658369)
        ·
          refine ⟨46941478504328910472243777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62588638005771880629658369 46941478504328910472243777)
          ·
            refine ⟨35206108878246682854182833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46941478504328910472243777 35206108878246682854182833)
            ·
              refine ⟨26404581658685012140637125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35206108878246682854182833 26404581658685012140637125)
              ·
                refine ⟨4950859061003439776369461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26404581658685012140637125 4950859061003439776369461)
                ·
                  refine ⟨464143036969072479034637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4950859061003439776369461 464143036969072479034637)
                  ·
                    rfl

theorem cell22_4067619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 5].length) (baseStart_4067619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067619 prefixEnd_4067619 := by exact prefixLift 4067619
  have htrace : WordTrace (prefixWord ++ tailWord_4067619) baseStart_4067619 baseEnd_4067619 := by
    simpa [prefixWord, tailWord_4067619, baseEnd_4067619] using wordTrace_append hprefix tailTrace_4067619
  have hstable : (prefixWord ++ tailWord_4067619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067619).length < 2 ^ (prefixWord ++ tailWord_4067619).sum := by decide
  have hdescent : baseEnd_4067619 < baseStart_4067619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067629 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4067629 : Nat := 118140960795 + 4067629 * 2 ^ 59
def prefixEnd_4067629 : Nat := 4983230072969 + 3 ^ 40 * 4067629 * 2
def baseEnd_4067629 : Nat := 1392432534111580744353881

theorem tailTrace_4067629 : CollatzResearch.WordTrace tailWord_4067629 prefixEnd_4067629 1392432534111580744353881 := by
  unfold tailWord_4067629
  simp only [CollatzResearch.WordTrace]
  refine ⟨148358617780682303570757941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98905745187121535713838627 148358617780682303570757941)
  ·
    refine ⟨13908620416938965959758557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148358617780682303570757941 13908620416938965959758557)
    ·
      refine ⟨5215732656352112234909459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13908620416938965959758557 5215732656352112234909459)
      ·
        refine ⟨7823598984528168352364189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215732656352112234909459 7823598984528168352364189)
        ·
          refine ⟨2933849619198063132136571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7823598984528168352364189 2933849619198063132136571)
          ·
            refine ⟨4400774428797094698204857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933849619198063132136571 4400774428797094698204857)
            ·
              refine ⟨3300580821597821023653643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400774428797094698204857 3300580821597821023653643)
              ·
                refine ⟨4950871232396731535480465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300580821597821023653643 4950871232396731535480465)
                ·
                  refine ⟨3713153424297548651610349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950871232396731535480465 3713153424297548651610349)
                  ·
                    refine ⟨1392432534111580744353881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713153424297548651610349 1392432534111580744353881)
                    ·
                      rfl

theorem cell22_4067629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4067629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067629 prefixEnd_4067629 := by exact prefixLift 4067629
  have htrace : WordTrace (prefixWord ++ tailWord_4067629) baseStart_4067629 baseEnd_4067629 := by
    simpa [prefixWord, tailWord_4067629, baseEnd_4067629] using wordTrace_append hprefix tailTrace_4067629
  have hstable : (prefixWord ++ tailWord_4067629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067629).length < 2 ^ (prefixWord ++ tailWord_4067629).sum := by decide
  have hdescent : baseEnd_4067629 < baseStart_4067629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067666 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_4067666 : Nat := 118140960795 + 4067666 * 2 ^ 59
def prefixEnd_4067666 : Nat := 4983230072969 + 3 ^ 40 * 4067666 * 2
def baseEnd_4067666 : Nat := 1392445199967724981178767

theorem tailTrace_4067666 : CollatzResearch.WordTrace tailWord_4067666 prefixEnd_4067666 1392445199967724981178767 := by
  unfold tailWord_4067666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089991820387064722463713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98906644854365505926569901 37089991820387064722463713)
  ·
    refine ⟨27817493865290298541847785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37089991820387064722463713 27817493865290298541847785)
    ·
      refine ⟨20863120398967723906385839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27817493865290298541847785 20863120398967723906385839)
      ·
        refine ⟨31294680598451585859578759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20863120398967723906385839 31294680598451585859578759)
        ·
          refine ⟨46942020897677378789368139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31294680598451585859578759 46942020897677378789368139)
          ·
            refine ⟨70413031346516068184052209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46942020897677378789368139 70413031346516068184052209)
            ·
              refine ⟨52809773509887051138039157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70413031346516068184052209 52809773509887051138039157)
              ·
                refine ⟨4950916266551911044191171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52809773509887051138039157 4950916266551911044191171)
                ·
                  refine ⟨7426374399827866566286757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950916266551911044191171 7426374399827866566286757)
                  ·
                    refine ⟨1392445199967724981178767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426374399827866566286757 1392445199967724981178767)
                    ·
                      rfl

theorem cell22_4067666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_4067666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067666 prefixEnd_4067666 := by exact prefixLift 4067666
  have htrace : WordTrace (prefixWord ++ tailWord_4067666) baseStart_4067666 baseEnd_4067666 := by
    simpa [prefixWord, tailWord_4067666, baseEnd_4067666] using wordTrace_append hprefix tailTrace_4067666
  have hstable : (prefixWord ++ tailWord_4067666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067666).length < 2 ^ (prefixWord ++ tailWord_4067666).sum := by decide
  have hdescent : baseEnd_4067666 < baseStart_4067666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067696 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_4067696 : Nat := 118140960795 + 4067696 * 2 ^ 59
def prefixEnd_4067696 : Nat := 4983230072969 + 3 ^ 40 * 4067696 * 2
def baseEnd_4067696 : Nat := 1392455469580814902928675

theorem tailTrace_4067696 : CollatzResearch.WordTrace tailWord_4067696 prefixEnd_4067696 1392455469580814902928675 := by
  unfold tailWord_4067696
  simp only [CollatzResearch.WordTrace]
  refine ⟨74180530735719787006723471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98907374314293049342297961 74180530735719787006723471)
  ·
    refine ⟨111270796103579680510085207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74180530735719787006723471 111270796103579680510085207)
    ·
      refine ⟨166906194155369520765127811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111270796103579680510085207 166906194155369520765127811)
      ·
        refine ⟨250359291233054281147691717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166906194155369520765127811 250359291233054281147691717)
        ·
          refine ⟨46942367106197677715192197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250359291233054281147691717 46942367106197677715192197)
          ·
            refine ⟨8801693832412064571598537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46942367106197677715192197 8801693832412064571598537)
            ·
              refine ⟨6601270374309048428698903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8801693832412064571598537 6601270374309048428698903)
              ·
                refine ⟨9901905561463572643048355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601270374309048428698903 9901905561463572643048355)
                ·
                  refine ⟨14852858342195358964572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9901905561463572643048355 14852858342195358964572533)
                  ·
                    refine ⟨1392455469580814902928675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14852858342195358964572533 1392455469580814902928675)
                    ·
                      rfl

theorem cell22_4067696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_4067696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067696 prefixEnd_4067696 := by exact prefixLift 4067696
  have htrace : WordTrace (prefixWord ++ tailWord_4067696) baseStart_4067696 baseEnd_4067696 := by
    simpa [prefixWord, tailWord_4067696, baseEnd_4067696] using wordTrace_append hprefix tailTrace_4067696
  have hstable : (prefixWord ++ tailWord_4067696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067696).length < 2 ^ (prefixWord ++ tailWord_4067696).sum := by decide
  have hdescent : baseEnd_4067696 < baseStart_4067696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067726 : List Nat := [4, 1, 1, 4, 1, 2, 9]
def baseStart_4067726 : Nat := 118140960795 + 4067726 * 2 ^ 59
def prefixEnd_4067726 : Nat := 4983230072969 + 3 ^ 40 * 4067726 * 2
def baseEnd_4067726 : Nat := 51572805155329808321429

theorem tailTrace_4067726 : CollatzResearch.WordTrace tailWord_4067726 prefixEnd_4067726 51572805155329808321429 := by
  unfold tailWord_4067726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545269457666361142129879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98908103774220592758026021 18545269457666361142129879)
  ·
    refine ⟨27817904186499541713194819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18545269457666361142129879 27817904186499541713194819)
    ·
      refine ⟨41726856279749312569792229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27817904186499541713194819 41726856279749312569792229)
      ·
        refine ⟨7823785552452996106836043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41726856279749312569792229 7823785552452996106836043)
        ·
          refine ⟨11735678328679494160254065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823785552452996106836043 11735678328679494160254065)
          ·
            refine ⟨8801758746509620620190549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11735678328679494160254065 8801758746509620620190549)
            ·
              refine ⟨51572805155329808321429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8801758746509620620190549 51572805155329808321429)
              ·
                rfl

theorem cell22_4067726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 9].length) (baseStart_4067726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067726 prefixEnd_4067726 := by exact prefixLift 4067726
  have htrace : WordTrace (prefixWord ++ tailWord_4067726) baseStart_4067726 baseEnd_4067726 := by
    simpa [prefixWord, tailWord_4067726, baseEnd_4067726] using wordTrace_append hprefix tailTrace_4067726
  have hstable : (prefixWord ++ tailWord_4067726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067726).length < 2 ^ (prefixWord ++ tailWord_4067726).sum := by decide
  have hdescent : baseEnd_4067726 < baseStart_4067726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067777 : List Nat := [1, 2, 7, 1, 2, 1, 8]
def baseStart_4067777 : Nat := 118140960795 + 4067777 * 2 ^ 59
def prefixEnd_4067777 : Nat := 4983230072969 + 3 ^ 40 * 4067777 * 2
def baseEnd_4067777 : Nat := 51573451760598433024201

theorem tailTrace_4067777 : CollatzResearch.WordTrace tailWord_4067777 prefixEnd_4067777 51573451760598433024201 := by
  unfold tailWord_4067777
  simp only [CollatzResearch.WordTrace]
  refine ⟨148364015784146124847145585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98909343856097416564763723 148364015784146124847145585)
  ·
    refine ⟨111273011838109593635359189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148364015784146124847145585 111273011838109593635359189)
    ·
      refine ⟨2607961214955693600828731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 111273011838109593635359189 2607961214955693600828731)
      ·
        refine ⟨3911941822433540401243097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607961214955693600828731 3911941822433540401243097)
        ·
          refine ⟨2933956366825155300932323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911941822433540401243097 2933956366825155300932323)
          ·
            refine ⟨4400934550237732951398485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933956366825155300932323 4400934550237732951398485)
            ·
              refine ⟨51573451760598433024201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4400934550237732951398485 51573451760598433024201)
              ·
                rfl

theorem cell22_4067777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 8].length) (baseStart_4067777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067777 prefixEnd_4067777 := by exact prefixLift 4067777
  have htrace : WordTrace (prefixWord ++ tailWord_4067777) baseStart_4067777 baseEnd_4067777 := by
    simpa [prefixWord, tailWord_4067777, baseEnd_4067777] using wordTrace_append hprefix tailTrace_4067777
  have hstable : (prefixWord ++ tailWord_4067777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067777).length < 2 ^ (prefixWord ++ tailWord_4067777).sum := by decide
  have hdescent : baseEnd_4067777 < baseStart_4067777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067801 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_4067801 : Nat := 118140960795 + 4067801 * 2 ^ 59
def prefixEnd_4067801 : Nat := 4983230072969 + 3 ^ 40 * 4067801 * 2
def baseEnd_4067801 : Nat := 1392491413226629629053353

theorem tailTrace_4067801 : CollatzResearch.WordTrace tailWord_4067801 prefixEnd_4067801 1392491413226629629053353 := by
  unfold tailWord_4067801
  simp only [CollatzResearch.WordTrace]
  refine ⟨148364891136059176946019257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98909927424039451297346171 148364891136059176946019257)
  ·
    refine ⟨111273668352044382709514443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148364891136059176946019257 111273668352044382709514443)
    ·
      refine ⟨166910502528066574064271665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111273668352044382709514443 166910502528066574064271665)
      ·
        refine ⟨125182876896049930548203749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166910502528066574064271665 125182876896049930548203749)
        ·
          refine ⟨23471789418009361977788203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125182876896049930548203749 23471789418009361977788203)
          ·
            refine ⟨35207684127014042966682305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23471789418009361977788203 35207684127014042966682305)
            ·
              refine ⟨26405763095260532225011729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35207684127014042966682305 26405763095260532225011729)
              ·
                refine ⟨19804322321445399168758797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26405763095260532225011729 19804322321445399168758797)
                ·
                  refine ⟨7426620870542024688284549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19804322321445399168758797 7426620870542024688284549)
                  ·
                    refine ⟨1392491413226629629053353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426620870542024688284549 1392491413226629629053353)
                    ·
                      rfl

theorem cell22_4067801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_4067801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067801 prefixEnd_4067801 := by exact prefixLift 4067801
  have htrace : WordTrace (prefixWord ++ tailWord_4067801) baseStart_4067801 baseEnd_4067801 := by
    simpa [prefixWord, tailWord_4067801, baseEnd_4067801] using wordTrace_append hprefix tailTrace_4067801
  have hstable : (prefixWord ++ tailWord_4067801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067801).length < 2 ^ (prefixWord ++ tailWord_4067801).sum := by decide
  have hdescent : baseEnd_4067801 < baseStart_4067801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067818 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_4067818 : Nat := 118140960795 + 4067818 * 2 ^ 59
def prefixEnd_4067818 : Nat := 4983230072969 + 3 ^ 40 * 4067818 * 2
def baseEnd_4067818 : Nat := 1392497232674047251378301

theorem tailTrace_4067818 : CollatzResearch.WordTrace tailWord_4067818 prefixEnd_4067818 1392497232674047251378301 := by
  unfold tailWord_4067818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37091377794249397212347027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98910340784665059232925405 37091377794249397212347027)
  ·
    refine ⟨55637066691374095818520541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37091377794249397212347027 55637066691374095818520541)
    ·
      refine ⟨20863900009265285931945203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55637066691374095818520541 20863900009265285931945203)
      ·
        refine ⟨31295850013897928897917805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20863900009265285931945203 31295850013897928897917805)
        ·
          refine ⟨11735943755211723336719177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31295850013897928897917805 11735943755211723336719177)
          ·
            refine ⟨8801957816408792502539383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11735943755211723336719177 8801957816408792502539383)
            ·
              refine ⟨13202936724613188753809075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801957816408792502539383 13202936724613188753809075)
              ·
                refine ⟨19804405086919783130713613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202936724613188753809075 19804405086919783130713613)
                ·
                  refine ⟨7426651907594918674017605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19804405086919783130713613 7426651907594918674017605)
                  ·
                    refine ⟨1392497232674047251378301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426651907594918674017605 1392497232674047251378301)
                    ·
                      rfl

theorem cell22_4067818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_4067818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067818 prefixEnd_4067818 := by exact prefixLift 4067818
  have htrace : WordTrace (prefixWord ++ tailWord_4067818) baseStart_4067818 baseEnd_4067818 := by
    simpa [prefixWord, tailWord_4067818, baseEnd_4067818] using wordTrace_append hprefix tailTrace_4067818
  have hstable : (prefixWord ++ tailWord_4067818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067818).length < 2 ^ (prefixWord ++ tailWord_4067818).sum := by decide
  have hdescent : baseEnd_4067818 < baseStart_4067818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067880 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4067880 : Nat := 118140960795 + 4067880 * 2 ^ 59
def prefixEnd_4067880 : Nat := 4983230072969 + 3 ^ 40 * 4067880 * 2
def baseEnd_4067880 : Nat := 1392518456541099756328111

theorem tailTrace_4067880 : CollatzResearch.WordTrace tailWord_4067880 prefixEnd_4067880 1392518456541099756328111 := by
  unfold tailWord_4067880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74183886251386486719072547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98911848335181982292096729 74183886251386486719072547)
  ·
    refine ⟨111275829377079730078608821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74183886251386486719072547 111275829377079730078608821)
    ·
      refine ⟨10432109004101224694869577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111275829377079730078608821 10432109004101224694869577)
      ·
        refine ⟨7824081753075918521152183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10432109004101224694869577 7824081753075918521152183)
        ·
          refine ⟨11736122629613877781728275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824081753075918521152183 11736122629613877781728275)
          ·
            refine ⟨17604183944420816672592413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736122629613877781728275 17604183944420816672592413)
            ·
              refine ⟨6601568979157806252222155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17604183944420816672592413 6601568979157806252222155)
              ·
                refine ⟨9902353468736709378333233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601568979157806252222155 9902353468736709378333233)
                ·
                  refine ⟨7426765101552532033749925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902353468736709378333233 7426765101552532033749925)
                  ·
                    refine ⟨1392518456541099756328111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7426765101552532033749925 1392518456541099756328111)
                    ·
                      rfl

theorem cell22_4067880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4067880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067880 prefixEnd_4067880 := by exact prefixLift 4067880
  have htrace : WordTrace (prefixWord ++ tailWord_4067880) baseStart_4067880 baseEnd_4067880 := by
    simpa [prefixWord, tailWord_4067880, baseEnd_4067880] using wordTrace_append hprefix tailTrace_4067880
  have hstable : (prefixWord ++ tailWord_4067880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067880).length < 2 ^ (prefixWord ++ tailWord_4067880).sum := by decide
  have hdescent : baseEnd_4067880 < baseStart_4067880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067893 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4067893 : Nat := 118140960795 + 4067893 * 2 ^ 59
def prefixEnd_4067893 : Nat := 4983230072969 + 3 ^ 40 * 4067893 * 2
def baseEnd_4067893 : Nat := 1392522906706772055753071

theorem tailTrace_4067893 : CollatzResearch.WordTrace tailWord_4067893 prefixEnd_4067893 1392522906706772055753071 := by
  unfold tailWord_4067893
  simp only [CollatzResearch.WordTrace]
  refine ⟨148368246651725876658368333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98912164434483917772245555 148368246651725876658368333)
  ·
    refine ⟨55638092494397203746888125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148368246651725876658368333 55638092494397203746888125)
    ·
      refine ⟨20864284685398951405083047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55638092494397203746888125 20864284685398951405083047)
      ·
        refine ⟨31296427028098427107624571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20864284685398951405083047 31296427028098427107624571)
        ·
          refine ⟨46944640542147640661436857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31296427028098427107624571 46944640542147640661436857)
          ·
            refine ⟨35208480406610730496077643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46944640542147640661436857 35208480406610730496077643)
            ·
              refine ⟨52812720609916095744116465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35208480406610730496077643 52812720609916095744116465)
              ·
                refine ⟨39609540457437071808087349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52812720609916095744116465 39609540457437071808087349)
                ·
                  refine ⟨3713394417884725482008189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39609540457437071808087349 3713394417884725482008189)
                  ·
                    refine ⟨1392522906706772055753071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713394417884725482008189 1392522906706772055753071)
                    ·
                      rfl

theorem cell22_4067893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4067893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067893 prefixEnd_4067893 := by exact prefixLift 4067893
  have htrace : WordTrace (prefixWord ++ tailWord_4067893) baseStart_4067893 baseEnd_4067893 := by
    simpa [prefixWord, tailWord_4067893, baseEnd_4067893] using wordTrace_append hprefix tailTrace_4067893
  have hstable : (prefixWord ++ tailWord_4067893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067893).length < 2 ^ (prefixWord ++ tailWord_4067893).sum := by decide
  have hdescent : baseEnd_4067893 < baseStart_4067893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067951 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 8]
def baseStart_4067951 : Nat := 118140960795 + 4067951 * 2 ^ 59
def prefixEnd_4067951 : Nat := 4983230072969 + 3 ^ 40 * 4067951 * 2
def baseEnd_4067951 : Nat := 464180920430693079267631

theorem tailTrace_4067951 : CollatzResearch.WordTrace tailWord_4067951 prefixEnd_4067951 464180920430693079267631 := by
  unfold tailWord_4067951
  simp only [CollatzResearch.WordTrace]
  refine ⟨148370362085515752563979707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98913574723677168375986471 148370362085515752563979707)
  ·
    refine ⟨222555543128273628845969561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148370362085515752563979707 222555543128273628845969561)
    ·
      refine ⟨166916657346205221634477171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222555543128273628845969561 166916657346205221634477171)
      ·
        refine ⟨250374986019307832451715757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166916657346205221634477171 250374986019307832451715757)
        ·
          refine ⟨93890619757240437169393409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250374986019307832451715757 93890619757240437169393409)
          ·
            refine ⟨70417964817930327877045057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93890619757240437169393409 70417964817930327877045057)
            ·
              refine ⟨52813473613447745907783793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70417964817930327877045057 52813473613447745907783793)
              ·
                refine ⟨39610105210085809430837845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52813473613447745907783793 39610105210085809430837845)
                ·
                  refine ⟨464180920430693079267631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39610105210085809430837845 464180920430693079267631)
                  ·
                    rfl

theorem cell22_4067951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_4067951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067951 prefixEnd_4067951 := by exact prefixLift 4067951
  have htrace : WordTrace (prefixWord ++ tailWord_4067951) baseStart_4067951 baseEnd_4067951 := by
    simpa [prefixWord, tailWord_4067951, baseEnd_4067951] using wordTrace_append hprefix tailTrace_4067951
  have hstable : (prefixWord ++ tailWord_4067951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067951).length < 2 ^ (prefixWord ++ tailWord_4067951).sum := by decide
  have hdescent : baseEnd_4067951 < baseStart_4067951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067968 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_4067968 : Nat := 118140960795 + 4067968 * 2 ^ 59
def prefixEnd_4067968 : Nat := 4983230072969 + 3 ^ 40 * 4067968 * 2
def baseEnd_4067968 : Nat := 464182860246498953375947

theorem tailTrace_4067968 : CollatzResearch.WordTrace tailWord_4067968 prefixEnd_4067968 464182860246498953375947 := by
  unfold tailWord_4067968
  simp only [CollatzResearch.WordTrace]
  refine ⟨74185491063227082233674279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98913988084302776311565705 74185491063227082233674279)
  ·
    refine ⟨111278236594840623350511419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74185491063227082233674279 111278236594840623350511419)
    ·
      refine ⟨166917354892260935025767129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111278236594840623350511419 166917354892260935025767129)
      ·
        refine ⟨125188016169195701269325347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166917354892260935025767129 125188016169195701269325347)
        ·
          refine ⟨187782024253793551903988021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125188016169195701269325347 187782024253793551903988021)
          ·
            refine ⟨17604564773793145490998877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187782024253793551903988021 17604564773793145490998877)
            ·
              refine ⟨6601711790172429559124579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17604564773793145490998877 6601711790172429559124579)
              ·
                refine ⟨9902567685258644338686869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601711790172429559124579 9902567685258644338686869)
                ·
                  refine ⟨464182860246498953375947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9902567685258644338686869 464182860246498953375947)
                  ·
                    rfl

theorem cell22_4067968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_4067968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4067968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4067968 prefixEnd_4067968 := by exact prefixLift 4067968
  have htrace : WordTrace (prefixWord ++ tailWord_4067968) baseStart_4067968 baseEnd_4067968 := by
    simpa [prefixWord, tailWord_4067968, baseEnd_4067968] using wordTrace_append hprefix tailTrace_4067968
  have hstable : (prefixWord ++ tailWord_4067968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067968).length < 2 ^ (prefixWord ++ tailWord_4067968).sum := by decide
  have hdescent : baseEnd_4067968 < baseStart_4067968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068000 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_4068000 : Nat := 118140960795 + 4068000 * 2 ^ 59
def prefixEnd_4068000 : Nat := 4983230072969 + 3 ^ 40 * 4068000 * 2
def baseEnd_4068000 : Nat := 1392559534993459443327743

theorem tailTrace_4068000 : CollatzResearch.WordTrace tailWord_4068000 prefixEnd_4068000 1392559534993459443327743 := by
  unfold tailWord_4068000
  simp only [CollatzResearch.WordTrace]
  refine ⟨74186074631169116966256727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98914766174892155955008969 74186074631169116966256727)
  ·
    refine ⟨111279111946753675449385091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74186074631169116966256727 111279111946753675449385091)
    ·
      refine ⟨166918667920130513174077637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111279111946753675449385091 166918667920130513174077637)
      ·
        refine ⟨31297250235024471220139557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166918667920130513174077637 31297250235024471220139557)
        ·
          refine ⟨5868234419067088353776167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31297250235024471220139557 5868234419067088353776167)
          ·
            refine ⟨8802351628600632530664251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868234419067088353776167 8802351628600632530664251)
            ·
              refine ⟨13203527442900948795996377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8802351628600632530664251 13203527442900948795996377)
              ·
                refine ⟨9902645582175711596997283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13203527442900948795996377 9902645582175711596997283)
                ·
                  refine ⟨14853968373263567395495925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9902645582175711596997283 14853968373263567395495925)
                  ·
                    refine ⟨1392559534993459443327743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14853968373263567395495925 1392559534993459443327743)
                    ·
                      rfl

theorem cell22_4068000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_4068000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068000 prefixEnd_4068000 := by exact prefixLift 4068000
  have htrace : WordTrace (prefixWord ++ tailWord_4068000) baseStart_4068000 baseEnd_4068000 := by
    simpa [prefixWord, tailWord_4068000, baseEnd_4068000] using wordTrace_append hprefix tailTrace_4068000
  have hstable : (prefixWord ++ tailWord_4068000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068000).length < 2 ^ (prefixWord ++ tailWord_4068000).sum := by decide
  have hdescent : baseEnd_4068000 < baseStart_4068000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068013 : List Nat := [1, 5, 2, 1, 1, 12]
def baseStart_4068013 : Nat := 118140960795 + 4068013 * 2 ^ 59
def prefixEnd_4068013 : Nat := 4983230072969 + 3 ^ 40 * 4068013 * 2
def baseEnd_4068013 : Nat := 17192147964927552379663

theorem tailTrace_4068013 : CollatzResearch.WordTrace tailWord_4068013 prefixEnd_4068013 17192147964927552379663 := by
  unfold tailWord_4068013
  simp only [CollatzResearch.WordTrace]
  refine ⟨148372623411291137152736693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98915082274194091435157795 148372623411291137152736693)
  ·
    refine ⟨13909933444808544108069065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148372623411291137152736693 13909933444808544108069065)
    ·
      refine ⟨10432450083606408081051799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13909933444808544108069065 10432450083606408081051799)
      ·
        refine ⟨15648675125409612121577699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10432450083606408081051799 15648675125409612121577699)
        ·
          refine ⟨23473012688114418182366549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15648675125409612121577699 23473012688114418182366549)
          ·
            refine ⟨17192147964927552379663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23473012688114418182366549 17192147964927552379663)
            ·
              rfl

theorem cell22_4068013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 12].length) (baseStart_4068013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068013 prefixEnd_4068013 := by exact prefixLift 4068013
  have htrace : WordTrace (prefixWord ++ tailWord_4068013) baseStart_4068013 baseEnd_4068013 := by
    simpa [prefixWord, tailWord_4068013, baseEnd_4068013] using wordTrace_append hprefix tailTrace_4068013
  have hstable : (prefixWord ++ tailWord_4068013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068013).length < 2 ^ (prefixWord ++ tailWord_4068013).sum := by decide
  have hdescent : baseEnd_4068013 < baseStart_4068013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068058 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_4068058 : Nat := 118140960795 + 4068058 * 2 ^ 59
def prefixEnd_4068058 : Nat := 4983230072969 + 3 ^ 40 * 4068058 * 2
def baseEnd_4068058 : Nat := 464193129859588875125855

theorem tailTrace_4068058 : CollatzResearch.WordTrace tailWord_4068058 prefixEnd_4068058 464193129859588875125855 := by
  unfold tailWord_4068058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37093566174032027459531207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98916176464085406558749885 37093566174032027459531207)
  ·
    refine ⟨55640349261048041189296811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37093566174032027459531207 55640349261048041189296811)
    ·
      refine ⟨83460523891572061783945217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55640349261048041189296811 83460523891572061783945217)
      ·
        refine ⟨62595392918679046337958913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83460523891572061783945217 62595392918679046337958913)
        ·
          refine ⟨46946544689009284753469185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62595392918679046337958913 46946544689009284753469185)
          ·
            refine ⟨35209908516756963565101889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46946544689009284753469185 35209908516756963565101889)
            ·
              refine ⟨26407431387567722673826417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35209908516756963565101889 26407431387567722673826417)
              ·
                refine ⟨19805573540675792005369813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26407431387567722673826417 19805573540675792005369813)
                ·
                  refine ⟨464193129859588875125855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19805573540675792005369813 464193129859588875125855)
                  ·
                    rfl

theorem cell22_4068058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_4068058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068058 prefixEnd_4068058 := by exact prefixLift 4068058
  have htrace : WordTrace (prefixWord ++ tailWord_4068058) baseStart_4068058 baseEnd_4068058 := by
    simpa [prefixWord, tailWord_4068058, baseEnd_4068058] using wordTrace_append hprefix tailTrace_4068058
  have hstable : (prefixWord ++ tailWord_4068058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068058).length < 2 ^ (prefixWord ++ tailWord_4068058).sum := by decide
  have hdescent : baseEnd_4068058 < baseStart_4068058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068073 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_4068073 : Nat := 118140960795 + 4068073 * 2 ^ 59
def prefixEnd_4068073 : Nat := 4983230072969 + 3 ^ 40 * 4068073 * 2
def baseEnd_4068073 : Nat := 1392584524385311586252519

theorem tailTrace_4068073 : CollatzResearch.WordTrace tailWord_4068073 prefixEnd_4068073 1392584524385311586252519 := by
  unfold tailWord_4068073
  simp only [CollatzResearch.WordTrace]
  refine ⟨148374811791073767399920873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98916541194049178266613915 148374811791073767399920873)
  ·
    refine ⟨111281108843305325549940655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148374811791073767399920873 111281108843305325549940655)
    ·
      refine ⟨166921663264957988324910983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111281108843305325549940655 166921663264957988324910983)
      ·
        refine ⟨250382494897436982487366475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166921663264957988324910983 250382494897436982487366475)
        ·
          refine ⟨375573742346155473731049713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250382494897436982487366475 375573742346155473731049713)
          ·
            refine ⟨281680306759616605298287285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375573742346155473731049713 281680306759616605298287285)
            ·
              refine ⟨26407528758714056746714433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281680306759616605298287285 26407528758714056746714433)
              ·
                refine ⟨19805646569035542560035825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26407528758714056746714433 19805646569035542560035825)
                ·
                  refine ⟨14854234926776656920026869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19805646569035542560035825 14854234926776656920026869)
                  ·
                    refine ⟨1392584524385311586252519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14854234926776656920026869 1392584524385311586252519)
                    ·
                      rfl

theorem cell22_4068073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_4068073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068073 prefixEnd_4068073 := by exact prefixLift 4068073
  have htrace : WordTrace (prefixWord ++ tailWord_4068073) baseStart_4068073 baseEnd_4068073 := by
    simpa [prefixWord, tailWord_4068073, baseEnd_4068073] using wordTrace_append hprefix tailTrace_4068073
  have hstable : (prefixWord ++ tailWord_4068073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068073).length < 2 ^ (prefixWord ++ tailWord_4068073).sum := by decide
  have hdescent : baseEnd_4068073 < baseStart_4068073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068092 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_4068092 : Nat := 118140960795 + 4068092 * 2 ^ 59
def prefixEnd_4068092 : Nat := 4983230072969 + 3 ^ 40 * 4068092 * 2
def baseEnd_4068092 : Nat := 464197009491200623342487

theorem tailTrace_4068092 : CollatzResearch.WordTrace tailWord_4068092 prefixEnd_4068092 464197009491200623342487 := by
  unfold tailWord_4068092
  simp only [CollatzResearch.WordTrace]
  refine ⟨74187752389002466822431265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98917003185336622429908353 74187752389002466822431265)
  ·
    refine ⟨55640814291751850116823449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74187752389002466822431265 55640814291751850116823449)
    ·
      refine ⟨41730610718813887587617587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55640814291751850116823449 41730610718813887587617587)
      ·
        refine ⟨62595916078220831381426381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41730610718813887587617587 62595916078220831381426381)
        ·
          refine ⟨23473468529332811768034893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62595916078220831381426381 23473468529332811768034893)
          ·
            refine ⟨8802550698499804413013085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23473468529332811768034893 8802550698499804413013085)
            ·
              refine ⟨3300956511937426654879907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8802550698499804413013085 3300956511937426654879907)
              ·
                refine ⟨4951434767906139982319861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300956511937426654879907 4951434767906139982319861)
                ·
                  refine ⟨464197009491200623342487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4951434767906139982319861 464197009491200623342487)
                  ·
                    rfl

theorem cell22_4068092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_4068092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068092 prefixEnd_4068092 := by exact prefixLift 4068092
  have htrace : WordTrace (prefixWord ++ tailWord_4068092) baseStart_4068092 baseEnd_4068092 := by
    simpa [prefixWord, tailWord_4068092, baseEnd_4068092] using wordTrace_append hprefix tailTrace_4068092
  have hstable : (prefixWord ++ tailWord_4068092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068092).length < 2 ^ (prefixWord ++ tailWord_4068092).sum := by decide
  have hdescent : baseEnd_4068092 < baseStart_4068092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068105 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_4068105 : Nat := 118140960795 + 4068105 * 2 ^ 59
def prefixEnd_4068105 : Nat := 4983230072969 + 3 ^ 40 * 4068105 * 2
def baseEnd_4068105 : Nat := 1392595478639274169452421

theorem tailTrace_4068105 : CollatzResearch.WordTrace tailWord_4068105 prefixEnd_4068105 1392595478639274169452421 := by
  unfold tailWord_4068105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148375978926957836865085769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98917319284638557910057179 148375978926957836865085769)
  ·
    refine ⟨111281984195218377648814327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148375978926957836865085769 111281984195218377648814327)
    ·
      refine ⟨166922976292827566473221491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111281984195218377648814327 166922976292827566473221491)
      ·
        refine ⟨250384464439241349709832237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166922976292827566473221491 250384464439241349709832237)
        ·
          refine ⟨93894174164715506141187089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250384464439241349709832237 93894174164715506141187089)
          ·
            refine ⟨70420630623536629605890317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93894174164715506141187089 70420630623536629605890317)
            ·
              refine ⟨26407736483826236102208869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70420630623536629605890317 26407736483826236102208869)
              ·
                refine ⟨4951450590717419269164163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26407736483826236102208869 4951450590717419269164163)
                ·
                  refine ⟨7427175886076128903746245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951450590717419269164163 7427175886076128903746245)
                  ·
                    refine ⟨1392595478639274169452421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427175886076128903746245 1392595478639274169452421)
                    ·
                      rfl

theorem cell22_4068105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_4068105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068105 prefixEnd_4068105 := by exact prefixLift 4068105
  have htrace : WordTrace (prefixWord ++ tailWord_4068105) baseStart_4068105 baseEnd_4068105 := by
    simpa [prefixWord, tailWord_4068105, baseEnd_4068105] using wordTrace_append hprefix tailTrace_4068105
  have hstable : (prefixWord ++ tailWord_4068105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068105).length < 2 ^ (prefixWord ++ tailWord_4068105).sum := by decide
  have hdescent : baseEnd_4068105 < baseStart_4068105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068152 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_4068152 : Nat := 118140960795 + 4068152 * 2 ^ 59
def prefixEnd_4068152 : Nat := 4983230072969 + 3 ^ 40 * 4068152 * 2
def baseEnd_4068152 : Nat := 1392611567699781713527277

theorem tailTrace_4068152 : CollatzResearch.WordTrace tailWord_4068152 prefixEnd_4068152 1392611567699781713527277 := by
  unfold tailWord_4068152
  simp only [CollatzResearch.WordTrace]
  refine ⟨74188846578893781946023355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98918462105191709261364473 74188846578893781946023355)
  ·
    refine ⟨111283269868340672919035033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74188846578893781946023355 111283269868340672919035033)
    ·
      refine ⟨83462452401255504689276275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111283269868340672919035033 83462452401255504689276275)
      ·
        refine ⟨125193678601883257033914413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83462452401255504689276275 125193678601883257033914413)
        ·
          refine ⟨46947629475706221387717905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125193678601883257033914413 46947629475706221387717905)
          ·
            refine ⟨35210722106779666040788429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46947629475706221387717905 35210722106779666040788429)
            ·
              refine ⟨13204020790042374765295661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35210722106779666040788429 13204020790042374765295661)
              ·
                refine ⟨4951507796265890536985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13204020790042374765295661 4951507796265890536985873)
                ·
                  refine ⟨3713630847199417902739405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951507796265890536985873 3713630847199417902739405)
                  ·
                    refine ⟨1392611567699781713527277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713630847199417902739405 1392611567699781713527277)
                    ·
                      rfl

theorem cell22_4068152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_4068152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068152 prefixEnd_4068152 := by exact prefixLift 4068152
  have htrace : WordTrace (prefixWord ++ tailWord_4068152) baseStart_4068152 baseEnd_4068152 := by
    simpa [prefixWord, tailWord_4068152, baseEnd_4068152] using wordTrace_append hprefix tailTrace_4068152
  have hstable : (prefixWord ++ tailWord_4068152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068152).length < 2 ^ (prefixWord ++ tailWord_4068152).sum := by decide
  have hdescent : baseEnd_4068152 < baseStart_4068152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068195 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_4068195 : Nat := 118140960795 + 4068195 * 2 ^ 59
def prefixEnd_4068195 : Nat := 4983230072969 + 3 ^ 40 * 4068195 * 2
def baseEnd_4068195 : Nat := 1392626287478543934702145

theorem tailTrace_4068195 : CollatzResearch.WordTrace tailWord_4068195 prefixEnd_4068195 1392626287478543934702145 := by
  unfold tailWord_4068195
  simp only [CollatzResearch.WordTrace]
  refine ⟨148379261496631782235862039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98919507664421188157241359 148379261496631782235862039)
  ·
    refine ⟨222568892244947673353793059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148379261496631782235862039 222568892244947673353793059)
    ·
      refine ⟨333853338367421510030689589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222568892244947673353793059 333853338367421510030689589)
      ·
        refine ⟨31298750471945766565377149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333853338367421510030689589 31298750471945766565377149)
        ·
          refine ⟨11737031426979662462016431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31298750471945766565377149 11737031426979662462016431)
          ·
            refine ⟨17605547140469493693024647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737031426979662462016431 17605547140469493693024647)
            ·
              refine ⟨26408320710704240539536971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17605547140469493693024647 26408320710704240539536971)
              ·
                refine ⟨39612481066056360809305457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26408320710704240539536971 39612481066056360809305457)
                ·
                  refine ⟨29709360799542270606979093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39612481066056360809305457 29709360799542270606979093)
                  ·
                    refine ⟨1392626287478543934702145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29709360799542270606979093 1392626287478543934702145)
                    ·
                      rfl

theorem cell22_4068195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_4068195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068195 prefixEnd_4068195 := by exact prefixLift 4068195
  have htrace : WordTrace (prefixWord ++ tailWord_4068195) baseStart_4068195 baseEnd_4068195 := by
    simpa [prefixWord, tailWord_4068195, baseEnd_4068195] using wordTrace_append hprefix tailTrace_4068195
  have hstable : (prefixWord ++ tailWord_4068195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068195).length < 2 ^ (prefixWord ++ tailWord_4068195).sum := by decide
  have hdescent : baseEnd_4068195 < baseStart_4068195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068214 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_4068214 : Nat := 118140960795 + 4068214 * 2 ^ 59
def prefixEnd_4068214 : Nat := 4983230072969 + 3 ^ 40 * 4068214 * 2
def baseEnd_4068214 : Nat := 1392632791566834218477087

theorem tailTrace_4068214 : CollatzResearch.WordTrace tailWord_4068214 prefixEnd_4068214 1392632791566834218477087 := by
  unfold tailWord_4068214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273747155222684280050231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98919969655708632320535797 9273747155222684280050231)
  ·
    refine ⟨13910620732834026420075347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273747155222684280050231 13910620732834026420075347)
    ·
      refine ⟨20865931099251039630113021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910620732834026420075347 20865931099251039630113021)
      ·
        refine ⟨7824724162219139861292383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20865931099251039630113021 7824724162219139861292383)
        ·
          refine ⟨11737086243328709791938575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824724162219139861292383 11737086243328709791938575)
          ·
            refine ⟨17605629364993064687907863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737086243328709791938575 17605629364993064687907863)
            ·
              refine ⟨26408444047489597031861795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17605629364993064687907863 26408444047489597031861795)
              ·
                refine ⟨39612666071234395547792693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26408444047489597031861795 39612666071234395547792693)
                ·
                  refine ⟨3713687444178224582605565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39612666071234395547792693 3713687444178224582605565)
                  ·
                    refine ⟨1392632791566834218477087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713687444178224582605565 1392632791566834218477087)
                    ·
                      rfl

theorem cell22_4068214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_4068214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068214 prefixEnd_4068214 := by exact prefixLift 4068214
  have htrace : WordTrace (prefixWord ++ tailWord_4068214) baseStart_4068214 baseEnd_4068214 := by
    simpa [prefixWord, tailWord_4068214, baseEnd_4068214] using wordTrace_append hprefix tailTrace_4068214
  have hstable : (prefixWord ++ tailWord_4068214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068214).length < 2 ^ (prefixWord ++ tailWord_4068214).sum := by decide
  have hdescent : baseEnd_4068214 < baseStart_4068214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068231 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 1, 3]
def baseStart_4068231 : Nat := 118140960795 + 4068231 * 2 ^ 59
def prefixEnd_4068231 : Nat := 4983230072969 + 3 ^ 40 * 4068231 * 2
def baseEnd_4068231 : Nat := 1392638611014251840802035

theorem tailTrace_4068231 : CollatzResearch.WordTrace tailWord_4068231 prefixEnd_4068231 1392638611014251840802035 := by
  unfold tailWord_4068231
  simp only [CollatzResearch.WordTrace]
  refine ⟨148380574524501360384172547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98920383016334240256115031 148380574524501360384172547)
  ·
    refine ⟨222570861786752040576258821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148380574524501360384172547 222570861786752040576258821)
    ·
      refine ⟨41732036585016007608048529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222570861786752040576258821 41732036585016007608048529)
      ·
        refine ⟨31299027438762005706036397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41732036585016007608048529 31299027438762005706036397)
        ·
          refine ⟨11737135289535752139763649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31299027438762005706036397 11737135289535752139763649)
          ·
            refine ⟨8802851467151814104822737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11737135289535752139763649 8802851467151814104822737)
            ·
              refine ⟨6602138600363860578617053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8802851467151814104822737 6602138600363860578617053)
              ·
                refine ⟨2475801975136447716981395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6602138600363860578617053 2475801975136447716981395)
                ·
                  refine ⟨3713702962704671575472093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475801975136447716981395 3713702962704671575472093)
                  ·
                    refine ⟨1392638611014251840802035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3713702962704671575472093 1392638611014251840802035)
                    ·
                      rfl

theorem cell22_4068231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_4068231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068231 prefixEnd_4068231 := by exact prefixLift 4068231
  have htrace : WordTrace (prefixWord ++ tailWord_4068231) baseStart_4068231 baseEnd_4068231 := by
    simpa [prefixWord, tailWord_4068231, baseEnd_4068231] using wordTrace_append hprefix tailTrace_4068231
  have hstable : (prefixWord ++ tailWord_4068231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068231).length < 2 ^ (prefixWord ++ tailWord_4068231).sum := by decide
  have hdescent : baseEnd_4068231 < baseStart_4068231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068302 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_4068302 : Nat := 118140960795 + 4068302 * 2 ^ 59
def prefixEnd_4068302 : Nat := 4983230072969 + 3 ^ 40 * 4068302 * 2
def baseEnd_4068302 : Nat := 1392662915765231322276817

theorem tailTrace_4068302 : CollatzResearch.WordTrace tailWord_4068302 prefixEnd_4068302 1392662915765231322276817 := by
  unfold tailWord_4068302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18547895513405517438750895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98922109404829426340004773 18547895513405517438750895)
  ·
    refine ⟨27821843270108276158126343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18547895513405517438750895 27821843270108276158126343)
    ·
      refine ⟨41732764905162414237189515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27821843270108276158126343 41732764905162414237189515)
      ·
        refine ⟨62599147357743621355784273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41732764905162414237189515 62599147357743621355784273)
        ·
          refine ⟨46949360518307716016838205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62599147357743621355784273 46949360518307716016838205)
          ·
            refine ⟨17606010194365393506314327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46949360518307716016838205 17606010194365393506314327)
            ·
              refine ⟨26409015291548090259471491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606010194365393506314327 26409015291548090259471491)
              ·
                refine ⟨39613522937322135389207237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26409015291548090259471491 39613522937322135389207237)
                ·
                  refine ⟨7427535550747900385476357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39613522937322135389207237 7427535550747900385476357)
                  ·
                    refine ⟨1392662915765231322276817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7427535550747900385476357 1392662915765231322276817)
                    ·
                      rfl

theorem cell22_4068302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_4068302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068302 prefixEnd_4068302 := by exact prefixLift 4068302
  have htrace : WordTrace (prefixWord ++ tailWord_4068302) baseStart_4068302 baseEnd_4068302 := by
    simpa [prefixWord, tailWord_4068302, baseEnd_4068302] using wordTrace_append hprefix tailTrace_4068302
  have hstable : (prefixWord ++ tailWord_4068302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068302).length < 2 ^ (prefixWord ++ tailWord_4068302).sum := by decide
  have hdescent : baseEnd_4068302 < baseStart_4068302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068317 : List Nat := [1, 4, 3, 1, 2, 1, 1, 9]
def baseStart_4068317 : Nat := 118140960795 + 4068317 * 2 ^ 59
def prefixEnd_4068317 : Nat := 4983230072969 + 3 ^ 40 * 4068317 * 2
def baseEnd_4068317 : Nat := 154740894507975142572419

theorem tailTrace_4068317 : CollatzResearch.WordTrace tailWord_4068317 prefixEnd_4068317 154740894507975142572419 := by
  unfold tailWord_4068317
  simp only [CollatzResearch.WordTrace]
  refine ⟨148383711202189797071803205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98922474134793198047868803 148383711202189797071803205)
  ·
    refine ⟨27821945850410586950963101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148383711202189797071803205 27821945850410586950963101)
    ·
      refine ⟨10433229693903970106611163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27821945850410586950963101 10433229693903970106611163)
      ·
        refine ⟨15649844540855955159916745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433229693903970106611163 15649844540855955159916745)
        ·
          refine ⟨11737383405641966369937559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15649844540855955159916745 11737383405641966369937559)
          ·
            refine ⟨17606075108462949554906339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11737383405641966369937559 17606075108462949554906339)
            ·
              refine ⟨26409112662694424332359509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17606075108462949554906339 26409112662694424332359509)
              ·
                refine ⟨154740894507975142572419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26409112662694424332359509 154740894507975142572419)
                ·
                  rfl

theorem cell22_4068317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 9].length) (baseStart_4068317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068317 prefixEnd_4068317 := by exact prefixLift 4068317
  have htrace : WordTrace (prefixWord ++ tailWord_4068317) baseStart_4068317 baseEnd_4068317 := by
    simpa [prefixWord, tailWord_4068317, baseEnd_4068317] using wordTrace_append hprefix tailTrace_4068317
  have hstable : (prefixWord ++ tailWord_4068317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068317).length < 2 ^ (prefixWord ++ tailWord_4068317).sum := by decide
  have hdescent : baseEnd_4068317 < baseStart_4068317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068424 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_4068424 : Nat := 118140960795 + 4068424 * 2 ^ 59
def prefixEnd_4068424 : Nat := 4983230072969 + 3 ^ 40 * 4068424 * 2
def baseEnd_4068424 : Nat := 464234892952821223575481

theorem tailTrace_4068424 : CollatzResearch.WordTrace tailWord_4068424 prefixEnd_4068424 464234892952821223575481 := by
  unfold tailWord_4068424
  simp only [CollatzResearch.WordTrace]
  refine ⟨74193806906401077172974163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98925075875201436230632217 74193806906401077172974163)
  ·
    refine ⟨111290710359601615759461245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74193806906401077172974163 111290710359601615759461245)
    ·
      refine ⟨41734016384850605909797967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111290710359601615759461245 41734016384850605909797967)
      ·
        refine ⟨62601024577275908864696951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41734016384850605909797967 62601024577275908864696951)
        ·
          refine ⟨93901536865913863297045427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62601024577275908864696951 93901536865913863297045427)
          ·
            refine ⟨140852305298870794945568141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93901536865913863297045427 140852305298870794945568141)
            ·
              refine ⟨52819614487076548104588053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140852305298870794945568141 52819614487076548104588053)
              ·
                refine ⟨2475919429081713192402565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52819614487076548104588053 2475919429081713192402565)
                ·
                  refine ⟨464234892952821223575481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475919429081713192402565 464234892952821223575481)
                  ·
                    rfl

theorem cell22_4068424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_4068424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068424 prefixEnd_4068424 := by exact prefixLift 4068424
  have htrace : WordTrace (prefixWord ++ tailWord_4068424) baseStart_4068424 baseEnd_4068424 := by
    simpa [prefixWord, tailWord_4068424, baseEnd_4068424] using wordTrace_append hprefix tailTrace_4068424
  have hstable : (prefixWord ++ tailWord_4068424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068424).length < 2 ^ (prefixWord ++ tailWord_4068424).sum := by decide
  have hdescent : baseEnd_4068424 < baseStart_4068424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068437 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4068437 : Nat := 118140960795 + 4068437 * 2 ^ 59
def prefixEnd_4068437 : Nat := 4983230072969 + 3 ^ 40 * 4068437 * 2
def baseEnd_4068437 : Nat := 1392709129024135970151403

theorem tailTrace_4068437 : CollatzResearch.WordTrace tailWord_4068437 prefixEnd_4068437 1392709129024135970151403 := by
  unfold tailWord_4068437
  simp only [CollatzResearch.WordTrace]
  refine ⟨148388087961755057566171565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98925391974503371710781043 148388087961755057566171565)
  ·
    refine ⟨55645532985658146587314337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148388087961755057566171565 55645532985658146587314337)
    ·
      refine ⟨41734149739243609940485753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55645532985658146587314337 41734149739243609940485753)
      ·
        refine ⟨31300612304432707455364315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41734149739243609940485753 31300612304432707455364315)
        ·
          refine ⟨46950918456649061183046473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31300612304432707455364315 46950918456649061183046473)
          ·
            refine ⟨35213188842486795887284855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46950918456649061183046473 35213188842486795887284855)
            ·
              refine ⟨52819783263730193830927283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35213188842486795887284855 52819783263730193830927283)
              ·
                refine ⟨79229674895595290746390925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52819783263730193830927283 79229674895595290746390925)
                ·
                  refine ⟨29711128085848234029896597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79229674895595290746390925 29711128085848234029896597)
                  ·
                    refine ⟨1392709129024135970151403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29711128085848234029896597 1392709129024135970151403)
                    ·
                      rfl

theorem cell22_4068437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4068437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068437 prefixEnd_4068437 := by exact prefixLift 4068437
  have htrace : WordTrace (prefixWord ++ tailWord_4068437) baseStart_4068437 baseEnd_4068437 := by
    simpa [prefixWord, tailWord_4068437, baseEnd_4068437] using wordTrace_append hprefix tailTrace_4068437
  have hstable : (prefixWord ++ tailWord_4068437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068437).length < 2 ^ (prefixWord ++ tailWord_4068437).sum := by decide
  have hdescent : baseEnd_4068437 < baseStart_4068437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068458 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_4068458 : Nat := 118140960795 + 4068458 * 2 ^ 59
def prefixEnd_4068458 : Nat := 4983230072969 + 3 ^ 40 * 4068458 * 2
def baseEnd_4068458 : Nat := 464238772584432971792113

theorem tailTrace_4068458 : CollatzResearch.WordTrace tailWord_4068458 prefixEnd_4068458 464238772584432971792113 := by
  unfold tailWord_4068458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37097213473669744538171507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98925902596452652101790685 37097213473669744538171507)
  ·
    refine ⟨55645820210504616807257261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37097213473669744538171507 55645820210504616807257261)
    ·
      refine ⟨20867182578939231302721473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55645820210504616807257261 20867182578939231302721473)
      ·
        refine ⟨15650386934204423477041105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20867182578939231302721473 15650386934204423477041105)
        ·
          refine ⟨11737790200653317607780829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15650386934204423477041105 11737790200653317607780829)
          ·
            refine ⟨4401671325244994102917811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11737790200653317607780829 4401671325244994102917811)
            ·
              refine ⟨6602506987867491154376717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4401671325244994102917811 6602506987867491154376717)
              ·
                refine ⟨2475940120450309182891269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6602506987867491154376717 2475940120450309182891269)
                ·
                  refine ⟨464238772584432971792113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2475940120450309182891269 464238772584432971792113)
                  ·
                    rfl

theorem cell22_4068458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_4068458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068458 prefixEnd_4068458 := by exact prefixLift 4068458
  have htrace : WordTrace (prefixWord ++ tailWord_4068458) baseStart_4068458 baseEnd_4068458 := by
    simpa [prefixWord, tailWord_4068458, baseEnd_4068458] using wordTrace_append hprefix tailTrace_4068458
  have hstable : (prefixWord ++ tailWord_4068458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068458).length < 2 ^ (prefixWord ++ tailWord_4068458).sum := by decide
  have hdescent : baseEnd_4068458 < baseStart_4068458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068576 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_4068576 : Nat := 118140960795 + 4068576 * 2 ^ 59
def prefixEnd_4068576 : Nat := 4983230072969 + 3 ^ 40 * 4068576 * 2
def baseEnd_4068576 : Nat := 464252237188261980308659

theorem tailTrace_4068576 : CollatzResearch.WordTrace tailWord_4068576 prefixEnd_4068576 464252237188261980308659 := by
  unfold tailWord_4068576
  simp only [CollatzResearch.WordTrace]
  refine ⟨74196578854125742152740791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98928771805500989536987721 74196578854125742152740791)
  ·
    refine ⟨111294868281188613229111187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74196578854125742152740791 111294868281188613229111187)
    ·
      refine ⟨166942302421782919843666781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111294868281188613229111187 166942302421782919843666781)
      ·
        refine ⟨62603363408168594941375043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166942302421782919843666781 62603363408168594941375043)
        ·
          refine ⟨93905045112252892412062565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62603363408168594941375043 93905045112252892412062565)
          ·
            refine ⟨17607195958547417327261731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93905045112252892412062565 17607195958547417327261731)
            ·
              refine ⟨26410793937821125990892597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17607195958547417327261731 26410793937821125990892597)
              ·
                refine ⟨2476011931670730561646181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26410793937821125990892597 2476011931670730561646181)
                ·
                  refine ⟨464252237188261980308659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476011931670730561646181 464252237188261980308659)
                  ·
                    rfl

theorem cell22_4068576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_4068576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068576 prefixEnd_4068576 := by exact prefixLift 4068576
  have htrace : WordTrace (prefixWord ++ tailWord_4068576) baseStart_4068576 baseEnd_4068576 := by
    simpa [prefixWord, tailWord_4068576, baseEnd_4068576] using wordTrace_append hprefix tailTrace_4068576
  have hstable : (prefixWord ++ tailWord_4068576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068576).length < 2 ^ (prefixWord ++ tailWord_4068576).sum := by decide
  have hdescent : baseEnd_4068576 < baseStart_4068576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068606 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4068606 : Nat := 118140960795 + 4068606 * 2 ^ 59
def prefixEnd_4068606 : Nat := 4983230072969 + 3 ^ 40 * 4068606 * 2
def baseEnd_4068606 : Nat := 1392766981177875862675885

theorem tailTrace_4068606 : CollatzResearch.WordTrace tailWord_4068606 prefixEnd_4068606 1392766981177875862675885 := by
  unfold tailWord_4068606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549281487267849928634209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98929501265428532952715781 18549281487267849928634209)
  ·
    refine ⟨13911961115450887446475657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18549281487267849928634209 13911961115450887446475657)
    ·
      refine ⟨10433970836588165584856743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13911961115450887446475657 10433970836588165584856743)
      ·
        refine ⟨15650956254882248377285115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10433970836588165584856743 15650956254882248377285115)
        ·
          refine ⟨23476434382323372565927673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15650956254882248377285115 23476434382323372565927673)
          ·
            refine ⟨17607325786742529424445755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23476434382323372565927673 17607325786742529424445755)
            ·
              refine ⟨26410988680113794136668633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17607325786742529424445755 26410988680113794136668633)
              ·
                refine ⟨19808241510085345602501475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26410988680113794136668633 19808241510085345602501475)
                ·
                  refine ⟨29712362265128018403752213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19808241510085345602501475 29712362265128018403752213)
                  ·
                    refine ⟨1392766981177875862675885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29712362265128018403752213 1392766981177875862675885)
                    ·
                      rfl

theorem cell22_4068606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4068606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068606 prefixEnd_4068606 := by exact prefixLift 4068606
  have htrace : WordTrace (prefixWord ++ tailWord_4068606) baseStart_4068606 baseEnd_4068606 := by
    simpa [prefixWord, tailWord_4068606, baseEnd_4068606] using wordTrace_append hprefix tailTrace_4068606
  have hstable : (prefixWord ++ tailWord_4068606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068606).length < 2 ^ (prefixWord ++ tailWord_4068606).sum := by decide
  have hdescent : baseEnd_4068606 < baseStart_4068606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068636 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_4068636 : Nat := 118140960795 + 4068636 * 2 ^ 59
def prefixEnd_4068636 : Nat := 4983230072969 + 3 ^ 40 * 4068636 * 2
def baseEnd_4068636 : Nat := 1392777250790965784425793

theorem tailTrace_4068636 : CollatzResearch.WordTrace tailWord_4068636 prefixEnd_4068636 1392777250790965784425793 := by
  unfold tailWord_4068636
  simp only [CollatzResearch.WordTrace]
  refine ⟨74197673044017057276332881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98930230725356076368443841 74197673044017057276332881)
  ·
    refine ⟨55648254783012792957249661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74197673044017057276332881 55648254783012792957249661)
    ·
      refine ⟨20868095543629797358968623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55648254783012792957249661 20868095543629797358968623)
      ·
        refine ⟨31302143315444696038452935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20868095543629797358968623 31302143315444696038452935)
        ·
          refine ⟨46953214973167044057679403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31302143315444696038452935 46953214973167044057679403)
          ·
            refine ⟨70429822459750566086519105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46953214973167044057679403 70429822459750566086519105)
            ·
              refine ⟨52822366844812924564889329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70429822459750566086519105 52822366844812924564889329)
              ·
                refine ⟨39616775133609693423666997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52822366844812924564889329 39616775133609693423666997)
                ·
                  refine ⟨3714072668775908758468781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39616775133609693423666997 3714072668775908758468781)
                  ·
                    refine ⟨1392777250790965784425793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714072668775908758468781 1392777250790965784425793)
                    ·
                      rfl

theorem cell22_4068636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_4068636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068636 prefixEnd_4068636 := by exact prefixLift 4068636
  have htrace : WordTrace (prefixWord ++ tailWord_4068636) baseStart_4068636 baseEnd_4068636 := by
    simpa [prefixWord, tailWord_4068636, baseEnd_4068636] using wordTrace_append hprefix tailTrace_4068636
  have hstable : (prefixWord ++ tailWord_4068636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068636).length < 2 ^ (prefixWord ++ tailWord_4068636).sum := by decide
  have hdescent : baseEnd_4068636 < baseStart_4068636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068664 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_4068664 : Nat := 118140960795 + 4068664 * 2 ^ 59
def prefixEnd_4068664 : Nat := 4983230072969 + 3 ^ 40 * 4068664 * 2
def baseEnd_4068664 : Nat := 1392786835763183044725707

theorem tailTrace_4068664 : CollatzResearch.WordTrace tailWord_4068664 prefixEnd_4068664 1392786835763183044725707 := by
  unfold tailWord_4068664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74198183665966337667342523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98930911554621783556456697 74198183665966337667342523)
  ·
    refine ⟨111297275498949506501013785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74198183665966337667342523 111297275498949506501013785)
    ·
      refine ⟨83472956624212129875760339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111297275498949506501013785 83472956624212129875760339)
      ·
        refine ⟨125209434936318194813640509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83472956624212129875760339 125209434936318194813640509)
        ·
          refine ⟨46953538101119323055115191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125209434936318194813640509 46953538101119323055115191)
          ·
            refine ⟨70430307151678984582672787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46953538101119323055115191 70430307151678984582672787)
            ·
              refine ⟨105645460727518476874009181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70430307151678984582672787 105645460727518476874009181)
              ·
                refine ⟨39617047772819428827753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105645460727518476874009181 39617047772819428827753443)
                ·
                  refine ⟨59425571659229143241630165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39617047772819428827753443 59425571659229143241630165)
                  ·
                    refine ⟨1392786835763183044725707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59425571659229143241630165 1392786835763183044725707)
                    ·
                      rfl

theorem cell22_4068664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_4068664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068664 prefixEnd_4068664 := by exact prefixLift 4068664
  have htrace : WordTrace (prefixWord ++ tailWord_4068664) baseStart_4068664 baseEnd_4068664 := by
    simpa [prefixWord, tailWord_4068664, baseEnd_4068664] using wordTrace_append hprefix tailTrace_4068664
  have hstable : (prefixWord ++ tailWord_4068664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068664).length < 2 ^ (prefixWord ++ tailWord_4068664).sum := by decide
  have hdescent : baseEnd_4068664 < baseStart_4068664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068666 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_4068666 : Nat := 118140960795 + 4068666 * 2 ^ 59
def prefixEnd_4068666 : Nat := 4983230072969 + 3 ^ 40 * 4068666 * 2
def baseEnd_4068666 : Nat := 464262506801351902058567

theorem tailTrace_4068666 : CollatzResearch.WordTrace tailWord_4068666 prefixEnd_4068666 464262506801351902058567 := by
  unfold tailWord_4068666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37099110069481357419064463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98930960185283619784171901 37099110069481357419064463)
  ·
    refine ⟨55648665104222036128596695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37099110069481357419064463 55648665104222036128596695)
    ·
      refine ⟨83472997656333054192895043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55648665104222036128596695 83472997656333054192895043)
      ·
        refine ⟨125209496484499581289342565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83472997656333054192895043 125209496484499581289342565)
        ·
          refine ⟨23476780590843671491751731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125209496484499581289342565 23476780590843671491751731)
          ·
            refine ⟨35215170886265507237627597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23476780590843671491751731 35215170886265507237627597)
            ·
              refine ⟨13205689082349565214110349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35215170886265507237627597 13205689082349565214110349)
              ·
                refine ⟨4952133405881086955291381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13205689082349565214110349 4952133405881086955291381)
                ·
                  refine ⟨464262506801351902058567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4952133405881086955291381 464262506801351902058567)
                  ·
                    rfl

theorem cell22_4068666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_4068666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068666 prefixEnd_4068666 := by exact prefixLift 4068666
  have htrace : WordTrace (prefixWord ++ tailWord_4068666) baseStart_4068666 baseEnd_4068666 := by
    simpa [prefixWord, tailWord_4068666, baseEnd_4068666] using wordTrace_append hprefix tailTrace_4068666
  have hstable : (prefixWord ++ tailWord_4068666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068666).length < 2 ^ (prefixWord ++ tailWord_4068666).sum := by decide
  have hdescent : baseEnd_4068666 < baseStart_4068666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068745 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 4]
def baseStart_4068745 : Nat := 118140960795 + 4068745 * 2 ^ 59
def prefixEnd_4068745 : Nat := 4983230072969 + 3 ^ 40 * 4068745 * 2
def baseEnd_4068745 : Nat := 464271521239508611150153

theorem tailTrace_4068745 : CollatzResearch.WordTrace tailWord_4068745 prefixEnd_4068745 464271521239508611150153 := by
  unfold tailWord_4068745
  simp only [CollatzResearch.WordTrace]
  refine ⟨148399321644639226168383689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98932881096426150778922459 148399321644639226168383689)
  ·
    refine ⟨111299491233479419626287767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148399321644639226168383689 111299491233479419626287767)
    ·
      refine ⟨166949236850219129439431651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111299491233479419626287767 166949236850219129439431651)
      ·
        refine ⟨250423855275328694159147477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166949236850219129439431651 250423855275328694159147477)
        ·
          refine ⟨5869309108015516269355019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 250423855275328694159147477 5869309108015516269355019)
          ·
            refine ⟨8803963662023274404032529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869309108015516269355019 8803963662023274404032529)
            ·
              refine ⟨6602972746517455803024397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8803963662023274404032529 6602972746517455803024397)
              ·
                refine ⟨2476114779944045926134149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6602972746517455803024397 2476114779944045926134149)
                ·
                  refine ⟨464271521239508611150153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476114779944045926134149 464271521239508611150153)
                  ·
                    rfl

theorem cell22_4068745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_4068745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068745 prefixEnd_4068745 := by exact prefixLift 4068745
  have htrace : WordTrace (prefixWord ++ tailWord_4068745) baseStart_4068745 baseEnd_4068745 := by
    simpa [prefixWord, tailWord_4068745, baseEnd_4068745] using wordTrace_append hprefix tailTrace_4068745
  have hstable : (prefixWord ++ tailWord_4068745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068745).length < 2 ^ (prefixWord ++ tailWord_4068745).sum := by decide
  have hdescent : baseEnd_4068745 < baseStart_4068745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068760 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_4068760 : Nat := 118140960795 + 4068760 * 2 ^ 59
def prefixEnd_4068760 : Nat := 4983230072969 + 3 ^ 40 * 4068760 * 2
def baseEnd_4068760 : Nat := 1392819698525070794325413

theorem tailTrace_4068760 : CollatzResearch.WordTrace tailWord_4068760 prefixEnd_4068760 1392819698525070794325413 := by
  unfold tailWord_4068760
  simp only [CollatzResearch.WordTrace]
  refine ⟨74199934369792441865089867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98933245826389922486786489 74199934369792441865089867)
  ·
    refine ⟨111299901554688662797634801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74199934369792441865089867 111299901554688662797634801)
    ·
      refine ⟨83474926166016497098226101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111299901554688662797634801 83474926166016497098226101)
      ·
        refine ⟨7825774328064046602958697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83474926166016497098226101 7825774328064046602958697)
        ·
          refine ⟨5869330746048034952219023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7825774328064046602958697 5869330746048034952219023)
          ·
            refine ⟨8803996119072052428328535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869330746048034952219023 8803996119072052428328535)
            ·
              refine ⟨13205994178608078642492803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8803996119072052428328535 13205994178608078642492803)
              ·
                refine ⟨19808991267912117963739205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13205994178608078642492803 19808991267912117963739205)
                ·
                  refine ⟨3714185862733522118201101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19808991267912117963739205 3714185862733522118201101)
                  ·
                    refine ⟨1392819698525070794325413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714185862733522118201101 1392819698525070794325413)
                    ·
                      rfl

theorem cell22_4068760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_4068760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068760 prefixEnd_4068760 := by exact prefixLift 4068760
  have htrace : WordTrace (prefixWord ++ tailWord_4068760) baseStart_4068760 baseEnd_4068760 := by
    simpa [prefixWord, tailWord_4068760, baseEnd_4068760] using wordTrace_append hprefix tailTrace_4068760
  have hstable : (prefixWord ++ tailWord_4068760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068760).length < 2 ^ (prefixWord ++ tailWord_4068760).sum := by decide
  have hdescent : baseEnd_4068760 < baseStart_4068760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068822 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4068822 : Nat := 118140960795 + 4068822 * 2 ^ 59
def prefixEnd_4068822 : Nat := 4983230072969 + 3 ^ 40 * 4068822 * 2
def baseEnd_4068822 : Nat := 1392840922392123299275223

theorem tailTrace_4068822 : CollatzResearch.WordTrace tailWord_4068822 prefixEnd_4068822 1392840922392123299275223 := by
  unfold tailWord_4068822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275133129085016769933545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98934753376906845545957813 9275133129085016769933545)
  ·
    refine ⟨6956349846813762577450159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9275133129085016769933545 6956349846813762577450159)
    ·
      refine ⟨10434524770220643866175239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6956349846813762577450159 10434524770220643866175239)
      ·
        refine ⟨15651787155330965799262859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434524770220643866175239 15651787155330965799262859)
        ·
          refine ⟨23477680732996448698894289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651787155330965799262859 23477680732996448698894289)
          ·
            refine ⟨17608260549747336524170717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23477680732996448698894289 17608260549747336524170717)
            ·
              refine ⟨6603097706155251196564019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17608260549747336524170717 6603097706155251196564019)
              ·
                refine ⟨9904646559232876794846029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6603097706155251196564019 9904646559232876794846029)
                ·
                  refine ⟨3714242459712328798067261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9904646559232876794846029 3714242459712328798067261)
                  ·
                    refine ⟨1392840922392123299275223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714242459712328798067261 1392840922392123299275223)
                    ·
                      rfl

theorem cell22_4068822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4068822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068822 prefixEnd_4068822 := by exact prefixLift 4068822
  have htrace : WordTrace (prefixWord ++ tailWord_4068822) baseStart_4068822 baseEnd_4068822 := by
    simpa [prefixWord, tailWord_4068822, baseEnd_4068822] using wordTrace_append hprefix tailTrace_4068822
  have hstable : (prefixWord ++ tailWord_4068822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068822).length < 2 ^ (prefixWord ++ tailWord_4068822).sum := by decide
  have hdescent : baseEnd_4068822 < baseStart_4068822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068835 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 5]
def baseStart_4068835 : Nat := 118140960795 + 4068835 * 2 ^ 59
def prefixEnd_4068835 : Nat := 4983230072969 + 3 ^ 40 * 4068835 * 2
def baseEnd_4068835 : Nat := 464281790852598532900061

theorem tailTrace_4068835 : CollatzResearch.WordTrace tailWord_4068835 prefixEnd_4068835 464281790852598532900061 := by
  unfold tailWord_4068835
  simp only [CollatzResearch.WordTrace]
  refine ⟨148402604214313171539159959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98935069476208781026106639 148402604214313171539159959)
  ·
    refine ⟨222603906321469757308739939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148402604214313171539159959 222603906321469757308739939)
    ·
      refine ⟨333905859482204635963109909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222603906321469757308739939 333905859482204635963109909)
      ·
        refine ⟨15651837163228342310770777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333905859482204635963109909 15651837163228342310770777)
        ·
          refine ⟨11738877872421256733078083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15651837163228342310770777 11738877872421256733078083)
          ·
            refine ⟨17608316808631885099617125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11738877872421256733078083 17608316808631885099617125)
            ·
              refine ⟨3301559401618478456178211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17608316808631885099617125 3301559401618478456178211)
              ·
                refine ⟨4952339102427717684267317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301559401618478456178211 4952339102427717684267317)
                ·
                  refine ⟨464281790852598532900061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4952339102427717684267317 464281790852598532900061)
                  ·
                    rfl

theorem cell22_4068835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 5].length) (baseStart_4068835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068835 prefixEnd_4068835 := by exact prefixLift 4068835
  have htrace : WordTrace (prefixWord ++ tailWord_4068835) baseStart_4068835 baseEnd_4068835 := by
    simpa [prefixWord, tailWord_4068835, baseEnd_4068835] using wordTrace_append hprefix tailTrace_4068835
  have hstable : (prefixWord ++ tailWord_4068835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068835).length < 2 ^ (prefixWord ++ tailWord_4068835).sum := by decide
  have hdescent : baseEnd_4068835 < baseStart_4068835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068848 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_4068848 : Nat := 118140960795 + 4068848 * 2 ^ 59
def prefixEnd_4068848 : Nat := 4983230072969 + 3 ^ 40 * 4068848 * 2
def baseEnd_4068848 : Nat := 1392849822723467898125143

theorem tailTrace_4068848 : CollatzResearch.WordTrace tailWord_4068848 prefixEnd_4068848 1392849822723467898125143 := by
  unfold tailWord_4068848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74201539181633037379691599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98935385575510716506255465 74201539181633037379691599)
  ·
    refine ⟨111302308772449556069537399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74201539181633037379691599 111302308772449556069537399)
    ·
      refine ⟨166953463158674334104306099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111302308772449556069537399 166953463158674334104306099)
      ·
        refine ⟨250430194738011501156459149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166953463158674334104306099 250430194738011501156459149)
        ·
          refine ⟨93911323026754312933672181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250430194738011501156459149 93911323026754312933672181)
          ·
            refine ⟨8804186533758216837531767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93911323026754312933672181 8804186533758216837531767)
            ·
              refine ⟨13206279800637325256297651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804186533758216837531767 13206279800637325256297651)
              ·
                refine ⟨19809419700955987884446477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13206279800637325256297651 19809419700955987884446477)
                ·
                  refine ⟨7428532387858495456667429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19809419700955987884446477 7428532387858495456667429)
                  ·
                    refine ⟨1392849822723467898125143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428532387858495456667429 1392849822723467898125143)
                    ·
                      rfl

theorem cell22_4068848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_4068848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068848 prefixEnd_4068848 := by exact prefixLift 4068848
  have htrace : WordTrace (prefixWord ++ tailWord_4068848) baseStart_4068848 baseEnd_4068848 := by
    simpa [prefixWord, tailWord_4068848, baseEnd_4068848] using wordTrace_append hprefix tailTrace_4068848
  have hstable : (prefixWord ++ tailWord_4068848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068848).length < 2 ^ (prefixWord ++ tailWord_4068848).sum := by decide
  have hdescent : baseEnd_4068848 < baseStart_4068848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068893 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4068893 : Nat := 118140960795 + 4068893 * 2 ^ 59
def prefixEnd_4068893 : Nat := 4983230072969 + 3 ^ 40 * 4068893 * 2
def baseEnd_4068893 : Nat := 1392865227143102780750005

theorem tailTrace_4068893 : CollatzResearch.WordTrace tailWord_4068893 prefixEnd_4068893 1392865227143102780750005 := by
  unfold tailWord_4068893
  simp only [CollatzResearch.WordTrace]
  refine ⟨148404719648103047444771333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98936479765402031629847555 148404719648103047444771333)
  ·
    refine ⟨27825884934019321395894625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148404719648103047444771333 27825884934019321395894625)
    ·
      refine ⟨20869413700514491046920969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27825884934019321395894625 20869413700514491046920969)
      ·
        refine ⟨15652060275385868285190727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20869413700514491046920969 15652060275385868285190727)
        ·
          refine ⟨23478090413078802427786091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15652060275385868285190727 23478090413078802427786091)
          ·
            refine ⟨35217135619618203641679137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23478090413078802427786091 35217135619618203641679137)
            ·
              refine ⟨26412851714713652731259353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35217135619618203641679137 26412851714713652731259353)
              ·
                refine ⟨19809638786035239548444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26412851714713652731259353 19809638786035239548444515)
                ·
                  refine ⟨29714458179052859322666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19809638786035239548444515 29714458179052859322666773)
                  ·
                    refine ⟨1392865227143102780750005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29714458179052859322666773 1392865227143102780750005)
                    ·
                      rfl

theorem cell22_4068893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4068893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068893 prefixEnd_4068893 := by exact prefixLift 4068893
  have htrace : WordTrace (prefixWord ++ tailWord_4068893) baseStart_4068893 baseEnd_4068893 := by
    simpa [prefixWord, tailWord_4068893, baseEnd_4068893] using wordTrace_append hprefix tailTrace_4068893
  have hstable : (prefixWord ++ tailWord_4068893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068893).length < 2 ^ (prefixWord ++ tailWord_4068893).sum := by decide
  have hdescent : baseEnd_4068893 < baseStart_4068893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068895 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 2, 3]
def baseStart_4068895 : Nat := 118140960795 + 4068895 * 2 ^ 59
def prefixEnd_4068895 : Nat := 4983230072969 + 3 ^ 40 * 4068895 * 2
def baseEnd_4068895 : Nat := 1392865911783975442199999

theorem tailTrace_4068895 : CollatzResearch.WordTrace tailWord_4068895 prefixEnd_4068895 1392865911783975442199999 := by
  unfold tailWord_4068895
  simp only [CollatzResearch.WordTrace]
  refine ⟨148404792594095801786344139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98936528396063867857562759 148404792594095801786344139)
  ·
    refine ⟨222607188891143702679516209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148404792594095801786344139 222607188891143702679516209)
    ·
      refine ⟨166955391668357777009637157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222607188891143702679516209 166955391668357777009637157)
      ·
        refine ⟨31304135937817083189306967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166955391668357777009637157 31304135937817083189306967)
        ·
          refine ⟨46956203906725624783960451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31304135937817083189306967 46956203906725624783960451)
          ·
            refine ⟨70434305860088437175940677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46956203906725624783960451 70434305860088437175940677)
            ·
              refine ⟨13206432348766581970488877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70434305860088437175940677 13206432348766581970488877)
              ·
                refine ⟨4952412130787468238933329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13206432348766581970488877 4952412130787468238933329)
                ·
                  refine ⟨3714309098090601179199997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4952412130787468238933329 3714309098090601179199997)
                  ·
                    refine ⟨1392865911783975442199999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714309098090601179199997 1392865911783975442199999)
                    ·
                      rfl

theorem cell22_4068895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_4068895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068895 prefixEnd_4068895 := by exact prefixLift 4068895
  have htrace : WordTrace (prefixWord ++ tailWord_4068895) baseStart_4068895 baseEnd_4068895 := by
    simpa [prefixWord, tailWord_4068895, baseEnd_4068895] using wordTrace_append hprefix tailTrace_4068895
  have hstable : (prefixWord ++ tailWord_4068895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068895).length < 2 ^ (prefixWord ++ tailWord_4068895).sum := by decide
  have hdescent : baseEnd_4068895 < baseStart_4068895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068910 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4068910 : Nat := 118140960795 + 4068910 * 2 ^ 59
def prefixEnd_4068910 : Nat := 4983230072969 + 3 ^ 40 * 4068910 * 2
def baseEnd_4068910 : Nat := 1392871046590520403074953

theorem tailTrace_4068910 : CollatzResearch.WordTrace tailWord_4068910 prefixEnd_4068910 1392871046590520403074953 := by
  unfold tailWord_4068910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550667461130182418517523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98936893126027639565426789 18550667461130182418517523)
  ·
    refine ⟨27826001191695273627776285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18550667461130182418517523 27826001191695273627776285)
    ·
      refine ⟨10434750446885727610416107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27826001191695273627776285 10434750446885727610416107)
      ·
        refine ⟨15652125670328591415624161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434750446885727610416107 15652125670328591415624161)
        ·
          refine ⟨11739094252746443561718121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15652125670328591415624161 11739094252746443561718121)
          ·
            refine ⟨8804320689559832671288591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11739094252746443561718121 8804320689559832671288591)
            ·
              refine ⟨13206481034339749006932887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804320689559832671288591 13206481034339749006932887)
              ·
                refine ⟨19809721551509623510399331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13206481034339749006932887 19809721551509623510399331)
                ·
                  refine ⟨29714582327264435265598997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19809721551509623510399331 29714582327264435265598997)
                  ·
                    refine ⟨1392871046590520403074953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29714582327264435265598997 1392871046590520403074953)
                    ·
                      rfl

theorem cell22_4068910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4068910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068910 prefixEnd_4068910 := by exact prefixLift 4068910
  have htrace : WordTrace (prefixWord ++ tailWord_4068910) baseStart_4068910 baseEnd_4068910 := by
    simpa [prefixWord, tailWord_4068910, baseEnd_4068910] using wordTrace_append hprefix tailTrace_4068910
  have hstable : (prefixWord ++ tailWord_4068910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068910).length < 2 ^ (prefixWord ++ tailWord_4068910).sum := by decide
  have hdescent : baseEnd_4068910 < baseStart_4068910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068940 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_4068940 : Nat := 118140960795 + 4068940 * 2 ^ 59
def prefixEnd_4068940 : Nat := 4983230072969 + 3 ^ 40 * 4068940 * 2
def baseEnd_4068940 : Nat := 1392881316203610324824861

theorem tailTrace_4068940 : CollatzResearch.WordTrace tailWord_4068940 prefixEnd_4068940 1392881316203610324824861 := by
  unfold tailWord_4068940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74203216939466387235866137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98937622585955182981154849 74203216939466387235866137)
  ·
    refine ⟨55652412704599790426899603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74203216939466387235866137 55652412704599790426899603)
    ·
      refine ⟨83478619056899685640349405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55652412704599790426899603 83478619056899685640349405)
      ·
        refine ⟨31304482146337382115131027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83478619056899685640349405 31304482146337382115131027)
        ·
          refine ⟨46956723219506073172696541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31304482146337382115131027 46956723219506073172696541)
          ·
            refine ⟨17608771207314777439761203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46956723219506073172696541 17608771207314777439761203)
            ·
              refine ⟨26413156810972166159641805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17608771207314777439761203 26413156810972166159641805)
              ·
                refine ⟨9904933804114562309865677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26413156810972166159641805 9904933804114562309865677)
                ·
                  refine ⟨3714350176542960866199629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9904933804114562309865677 3714350176542960866199629)
                  ·
                    refine ⟨1392881316203610324824861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714350176542960866199629 1392881316203610324824861)
                    ·
                      rfl

theorem cell22_4068940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_4068940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068940 prefixEnd_4068940 := by exact prefixLift 4068940
  have htrace : WordTrace (prefixWord ++ tailWord_4068940) baseStart_4068940 baseEnd_4068940 := by
    simpa [prefixWord, tailWord_4068940, baseEnd_4068940] using wordTrace_append hprefix tailTrace_4068940
  have hstable : (prefixWord ++ tailWord_4068940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068940).length < 2 ^ (prefixWord ++ tailWord_4068940).sum := by decide
  have hdescent : baseEnd_4068940 < baseStart_4068940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068953 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 5]
def baseStart_4068953 : Nat := 118140960795 + 4068953 * 2 ^ 59
def prefixEnd_4068953 : Nat := 4983230072969 + 3 ^ 40 * 4068953 * 2
def baseEnd_4068953 : Nat := 464295255456427541416607

theorem tailTrace_4068953 : CollatzResearch.WordTrace tailWord_4068953 prefixEnd_4068953 464295255456427541416607 := by
  unfold tailWord_4068953
  simp only [CollatzResearch.WordTrace]
  refine ⟨148406908027885677691955513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98937938685257118461303675 148406908027885677691955513)
  ·
    refine ⟨111305181020914258268966635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148406908027885677691955513 111305181020914258268966635)
    ·
      refine ⟨166957771531371387403449953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111305181020914258268966635 166957771531371387403449953)
      ·
        refine ⟨125218328648528540552587465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166957771531371387403449953 125218328648528540552587465)
        ·
          refine ⟨93913746486396405414440599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125218328648528540552587465 93913746486396405414440599)
          ·
            refine ⟨140870619729594608121660899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93913746486396405414440599 140870619729594608121660899)
            ·
              refine ⟨211305929594391912182491349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140870619729594608121660899 211305929594391912182491349)
              ·
                refine ⟨4952482724868560441777141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 211305929594391912182491349 4952482724868560441777141)
                ·
                  refine ⟨464295255456427541416607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4952482724868560441777141 464295255456427541416607)
                  ·
                    rfl

theorem cell22_4068953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_4068953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068953 prefixEnd_4068953 := by exact prefixLift 4068953
  have htrace : WordTrace (prefixWord ++ tailWord_4068953) baseStart_4068953 baseEnd_4068953 := by
    simpa [prefixWord, tailWord_4068953, baseEnd_4068953] using wordTrace_append hprefix tailTrace_4068953
  have hstable : (prefixWord ++ tailWord_4068953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068953).length < 2 ^ (prefixWord ++ tailWord_4068953).sum := by decide
  have hdescent : baseEnd_4068953 < baseStart_4068953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068983 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_4068983 : Nat := 118140960795 + 4068983 * 2 ^ 59
def prefixEnd_4068983 : Nat := 4983230072969 + 3 ^ 40 * 4068983 * 2
def baseEnd_4068983 : Nat := 1392896035982372545999729

theorem tailTrace_4068983 : CollatzResearch.WordTrace tailWord_4068983 prefixEnd_4068983 1392896035982372545999729 := by
  unfold tailWord_4068983
  simp only [CollatzResearch.WordTrace]
  refine ⟨148408002217776992815547603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98938668145184661877031735 148408002217776992815547603)
  ·
    refine ⟨222612003326665489223321405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148408002217776992815547603 222612003326665489223321405)
    ·
      refine ⟨83479501247499558458745527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222612003326665489223321405 83479501247499558458745527)
      ·
        refine ⟨125219251871249337688118291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83479501247499558458745527 125219251871249337688118291)
        ·
          refine ⟨187828877806874006532177437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125219251871249337688118291 187828877806874006532177437)
          ·
            refine ⟨70435829177577752449566539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187828877806874006532177437 70435829177577752449566539)
            ·
              refine ⟨105653743766366628674349809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70435829177577752449566539 105653743766366628674349809)
              ·
                refine ⟨79240307824774971505762357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105653743766366628674349809 79240307824774971505762357)
                ·
                  refine ⟨7428778858572653578665221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79240307824774971505762357 7428778858572653578665221)
                  ·
                    refine ⟨1392896035982372545999729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7428778858572653578665221 1392896035982372545999729)
                    ·
                      rfl

theorem cell22_4068983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_4068983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4068983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4068983 prefixEnd_4068983 := by exact prefixLift 4068983
  have htrace : WordTrace (prefixWord ++ tailWord_4068983) baseStart_4068983 baseEnd_4068983 := by
    simpa [prefixWord, tailWord_4068983, baseEnd_4068983] using wordTrace_append hprefix tailTrace_4068983
  have hstable : (prefixWord ++ tailWord_4068983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068983).length < 2 ^ (prefixWord ++ tailWord_4068983).sum := by decide
  have hdescent : baseEnd_4068983 < baseStart_4068983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069013 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4069013 : Nat := 118140960795 + 4069013 * 2 ^ 59
def prefixEnd_4069013 : Nat := 4983230072969 + 3 ^ 40 * 4069013 * 2
def baseEnd_4069013 : Nat := 1392906305595462467749637

theorem tailTrace_4069013 : CollatzResearch.WordTrace tailWord_4069013 prefixEnd_4069013 1392906305595462467749637 := by
  unfold tailWord_4069013
  simp only [CollatzResearch.WordTrace]
  refine ⟨148409096407668307939139693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98939397605112205292759795 148409096407668307939139693)
  ·
    refine ⟨55653411152875615477177385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148409096407668307939139693 55653411152875615477177385)
    ·
      refine ⟨41740058364656711607883039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55653411152875615477177385 41740058364656711607883039)
      ·
        refine ⟨62610087546985067411824559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41740058364656711607883039 62610087546985067411824559)
        ·
          refine ⟨93915131320477601117736839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62610087546985067411824559 93915131320477601117736839)
          ·
            refine ⟨140872696980716401676605259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93915131320477601117736839 140872696980716401676605259)
            ·
              refine ⟨211309045471074602514907889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140872696980716401676605259 211309045471074602514907889)
              ·
                refine ⟨158481784103305951886180917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211309045471074602514907889 158481784103305951886180917)
                ·
                  refine ⟨14857667259684932989329461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158481784103305951886180917 14857667259684932989329461)
                  ·
                    refine ⟨1392906305595462467749637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14857667259684932989329461 1392906305595462467749637)
                    ·
                      rfl

theorem cell22_4069013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4069013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069013 prefixEnd_4069013 := by exact prefixLift 4069013
  have htrace : WordTrace (prefixWord ++ tailWord_4069013) baseStart_4069013 baseEnd_4069013 := by
    simpa [prefixWord, tailWord_4069013, baseEnd_4069013] using wordTrace_append hprefix tailTrace_4069013
  have hstable : (prefixWord ++ tailWord_4069013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069013).length < 2 ^ (prefixWord ++ tailWord_4069013).sum := by decide
  have hdescent : baseEnd_4069013 < baseStart_4069013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069047 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 2, 3]
def baseStart_4069047 : Nat := 118140960795 + 4069047 * 2 ^ 59
def prefixEnd_4069047 : Nat := 4983230072969 + 3 ^ 40 * 4069047 * 2
def baseEnd_4069047 : Nat := 1392917944490297712399533

theorem tailTrace_4069047 : CollatzResearch.WordTrace tailWord_4069047 prefixEnd_4069047 1392917944490297712399533 := by
  unfold tailWord_4069047
  simp only [CollatzResearch.WordTrace]
  refine ⟨148410336489545131745877395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98940224326363421163918263 148410336489545131745877395)
  ·
    refine ⟨222615504734317697618816093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148410336489545131745877395 222615504734317697618816093)
    ·
      refine ⟨83480814275369136607056035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222615504734317697618816093 83480814275369136607056035)
      ·
        refine ⟨125221221413053704910584053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83480814275369136607056035 125221221413053704910584053)
        ·
          refine ⟨11739489507473784835367255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125221221413053704910584053 11739489507473784835367255)
          ·
            refine ⟨17609234261210677253050883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11739489507473784835367255 17609234261210677253050883)
            ·
              refine ⟨26413851391816015879576325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17609234261210677253050883 26413851391816015879576325)
              ·
                refine ⟨4952597135965502977420561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26413851391816015879576325 4952597135965502977420561)
                ·
                  refine ⟨3714447851974127233065421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4952597135965502977420561 3714447851974127233065421)
                  ·
                    refine ⟨1392917944490297712399533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714447851974127233065421 1392917944490297712399533)
                    ·
                      rfl

theorem cell22_4069047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_4069047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069047 prefixEnd_4069047 := by exact prefixLift 4069047
  have htrace : WordTrace (prefixWord ++ tailWord_4069047) baseStart_4069047 baseEnd_4069047 := by
    simpa [prefixWord, tailWord_4069047, baseEnd_4069047] using wordTrace_append hprefix tailTrace_4069047
  have hstable : (prefixWord ++ tailWord_4069047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069047).length < 2 ^ (prefixWord ++ tailWord_4069047).sum := by decide
  have hdescent : baseEnd_4069047 < baseStart_4069047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069105 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 7]
def baseStart_4069105 : Nat := 118140960795 + 4069105 * 2 ^ 59
def prefixEnd_4069105 : Nat := 4983230072969 + 3 ^ 40 * 4069105 * 2
def baseEnd_4069105 : Nat := 464312599691868298149785

theorem tailTrace_4069105 : CollatzResearch.WordTrace tailWord_4069105 prefixEnd_4069105 464312599691868298149785 := by
  unfold tailWord_4069105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148412451923335007651488769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98941634615556671767659179 148412451923335007651488769)
  ·
    refine ⟨111309338942501255738616577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148412451923335007651488769 111309338942501255738616577)
    ·
      refine ⟨83482004206875941803962433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111309338942501255738616577 83482004206875941803962433)
      ·
        refine ⟨62611503155156956352971825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83482004206875941803962433 62611503155156956352971825)
        ·
          refine ⟨46958627366367717264728869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62611503155156956352971825 46958627366367717264728869)
          ·
            refine ⟨8804742631193946987136663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46958627366367717264728869 8804742631193946987136663)
            ·
              refine ⟨13207113946790920480704995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804742631193946987136663 13207113946790920480704995)
              ·
                refine ⟨19810670920186380721057493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13207113946790920480704995 19810670920186380721057493)
                ·
                  refine ⟨464312599691868298149785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19810670920186380721057493 464312599691868298149785)
                  ·
                    rfl

theorem cell22_4069105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_4069105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069105 prefixEnd_4069105 := by exact prefixLift 4069105
  have htrace : WordTrace (prefixWord ++ tailWord_4069105) baseStart_4069105 baseEnd_4069105 := by
    simpa [prefixWord, tailWord_4069105, baseEnd_4069105] using wordTrace_append hprefix tailTrace_4069105
  have hstable : (prefixWord ++ tailWord_4069105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069105).length < 2 ^ (prefixWord ++ tailWord_4069105).sum := by decide
  have hdescent : baseEnd_4069105 < baseStart_4069105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069152 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_4069152 : Nat := 118140960795 + 4069152 * 2 ^ 59
def prefixEnd_4069152 : Nat := 4983230072969 + 3 ^ 40 * 4069152 * 2
def baseEnd_4069152 : Nat := 1392953888136112438524211

theorem tailTrace_4069152 : CollatzResearch.WordTrace tailWord_4069152 prefixEnd_4069152 1392953888136112438524211 := by
  unfold tailWord_4069152
  simp only [CollatzResearch.WordTrace]
  refine ⟨74207083077082367339224855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98942777436109823118966473 74207083077082367339224855)
  ·
    refine ⟨111310624615623551008837283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74207083077082367339224855 111310624615623551008837283)
    ·
      refine ⟨166965936923435326513255925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111310624615623551008837283 166965936923435326513255925)
      ·
        refine ⟨15653056586572061860617743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166965936923435326513255925 15653056586572061860617743)
        ·
          refine ⟨23479584879858092790926615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15653056586572061860617743 23479584879858092790926615)
          ·
            refine ⟨35219377319787139186389923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23479584879858092790926615 35219377319787139186389923)
            ·
              refine ⟨52829065979680708779584885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35219377319787139186389923 52829065979680708779584885)
              ·
                refine ⟨4952724935595066448086083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52829065979680708779584885 4952724935595066448086083)
                ·
                  refine ⟨7429087403392599672129125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952724935595066448086083 7429087403392599672129125)
                  ·
                    refine ⟨1392953888136112438524211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429087403392599672129125 1392953888136112438524211)
                    ·
                      rfl

theorem cell22_4069152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_4069152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069152 prefixEnd_4069152 := by exact prefixLift 4069152
  have htrace : WordTrace (prefixWord ++ tailWord_4069152) baseStart_4069152 baseEnd_4069152 := by
    simpa [prefixWord, tailWord_4069152, baseEnd_4069152] using wordTrace_append hprefix tailTrace_4069152
  have hstable : (prefixWord ++ tailWord_4069152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069152).length < 2 ^ (prefixWord ++ tailWord_4069152).sum := by decide
  have hdescent : baseEnd_4069152 < baseStart_4069152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069180 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_4069180 : Nat := 118140960795 + 4069180 * 2 ^ 59
def prefixEnd_4069180 : Nat := 4983230072969 + 3 ^ 40 * 4069180 * 2
def baseEnd_4069180 : Nat := 1392963473108329698824125

theorem tailTrace_4069180 : CollatzResearch.WordTrace tailWord_4069180 prefixEnd_4069180 1392963473108329698824125 := by
  unfold tailWord_4069180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74207593699031647730234497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98943458265375530306979329 74207593699031647730234497)
  ·
    refine ⟨55655695274273735797675873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74207593699031647730234497 55655695274273735797675873)
    ·
      refine ⟨41741771455705301848256905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55655695274273735797675873 41741771455705301848256905)
      ·
        refine ⟨31306328591778976386192679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41741771455705301848256905 31306328591778976386192679)
        ·
          refine ⟨46959492887668464579289019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31306328591778976386192679 46959492887668464579289019)
          ·
            refine ⟨70439239331502696868933529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46959492887668464579289019 70439239331502696868933529)
            ·
              refine ⟨52829429498627022651700147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70439239331502696868933529 52829429498627022651700147)
              ·
                refine ⟨79244144247940533977550221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52829429498627022651700147 79244144247940533977550221)
                ·
                  refine ⟨29716554092977700241581333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79244144247940533977550221 29716554092977700241581333)
                  ·
                    refine ⟨1392963473108329698824125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29716554092977700241581333 1392963473108329698824125)
                    ·
                      rfl

theorem cell22_4069180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_4069180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069180 prefixEnd_4069180 := by exact prefixLift 4069180
  have htrace : WordTrace (prefixWord ++ tailWord_4069180) baseStart_4069180 baseEnd_4069180 := by
    simpa [prefixWord, tailWord_4069180, baseEnd_4069180] using wordTrace_append hprefix tailTrace_4069180
  have hstable : (prefixWord ++ tailWord_4069180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069180).length < 2 ^ (prefixWord ++ tailWord_4069180).sum := by decide
  have hdescent : baseEnd_4069180 < baseStart_4069180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069212 : List Nat := [2, 2, 4, 2, 2, 10]
def baseStart_4069212 : Nat := 118140960795 + 4069212 * 2 ^ 59
def prefixEnd_4069212 : Nat := 4983230072969 + 3 ^ 40 * 4069212 * 2
def baseEnd_4069212 : Nat := 17197215152620892370667

theorem tailTrace_4069212 : CollatzResearch.WordTrace tailWord_4069212 prefixEnd_4069212 17197215152620892370667 := by
  unfold tailWord_4069212
  simp only [CollatzResearch.WordTrace]
  refine ⟨74208177266973682462816945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98944236355964909950422593 74208177266973682462816945)
  ·
    refine ⟨55656132950230261847112709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74208177266973682462816945 55656132950230261847112709)
    ·
      refine ⟨10435524928168174096333633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55656132950230261847112709 10435524928168174096333633)
      ·
        refine ⟨7826643696126130572250225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10435524928168174096333633 7826643696126130572250225)
        ·
          refine ⟨5869982772094597929187669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7826643696126130572250225 5869982772094597929187669)
          ·
            refine ⟨17197215152620892370667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5869982772094597929187669 17197215152620892370667)
            ·
              rfl

theorem cell22_4069212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 10].length) (baseStart_4069212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069212 prefixEnd_4069212 := by exact prefixLift 4069212
  have htrace : WordTrace (prefixWord ++ tailWord_4069212) baseStart_4069212 baseEnd_4069212 := by
    simpa [prefixWord, tailWord_4069212, baseEnd_4069212] using wordTrace_append hprefix tailTrace_4069212
  have hstable : (prefixWord ++ tailWord_4069212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069212).length < 2 ^ (prefixWord ++ tailWord_4069212).sum := by decide
  have hdescent : baseEnd_4069212 < baseStart_4069212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069218 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_4069218 : Nat := 118140960795 + 4069218 * 2 ^ 59
def prefixEnd_4069218 : Nat := 4983230072969 + 3 ^ 40 * 4069218 * 2
def baseEnd_4069218 : Nat := 464325493761636755458003

theorem tailTrace_4069218 : CollatzResearch.WordTrace tailWord_4069218 prefixEnd_4069218 464325493761636755458003 := by
  unfold tailWord_4069218
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104143342981406987588077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98944382247950418633568205 37104143342981406987588077)
  ·
    refine ⟨13914053753618027620345529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37104143342981406987588077 13914053753618027620345529)
    ·
      refine ⟨10435540315213520715259147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13914053753618027620345529 10435540315213520715259147)
      ·
        refine ⟨15653310472820281072888721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10435540315213520715259147 15653310472820281072888721)
        ·
          refine ⟨11739982854615210804666541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15653310472820281072888721 11739982854615210804666541)
          ·
            refine ⟨4402493570480704051749953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11739982854615210804666541 4402493570480704051749953)
            ·
              refine ⟨3301870177860528038812465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402493570480704051749953 3301870177860528038812465)
              ·
                refine ⟨2476402633395396029109349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301870177860528038812465 2476402633395396029109349)
                ·
                  refine ⟨464325493761636755458003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476402633395396029109349 464325493761636755458003)
                  ·
                    rfl

theorem cell22_4069218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_4069218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069218 prefixEnd_4069218 := by exact prefixLift 4069218
  have htrace : WordTrace (prefixWord ++ tailWord_4069218) baseStart_4069218 baseEnd_4069218 := by
    simpa [prefixWord, tailWord_4069218, baseEnd_4069218] using wordTrace_append hprefix tailTrace_4069218
  have hstable : (prefixWord ++ tailWord_4069218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069218).length < 2 ^ (prefixWord ++ tailWord_4069218).sum := by decide
  have hdescent : baseEnd_4069218 < baseStart_4069218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069227 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 3, 3]
def baseStart_4069227 : Nat := 118140960795 + 4069227 * 2 ^ 59
def prefixEnd_4069227 : Nat := 4983230072969 + 3 ^ 40 * 4069227 * 2
def baseEnd_4069227 : Nat := 1392979562168837242898981

theorem tailTrace_4069227 : CollatzResearch.WordTrace tailWord_4069227 prefixEnd_4069227 1392979562168837242898981 := by
  unfold tailWord_4069227
  simp only [CollatzResearch.WordTrace]
  refine ⟨148416901628893022487429935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98944601085928681658286623 148416901628893022487429935)
  ·
    refine ⟨222625352443339533731144903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148416901628893022487429935 222625352443339533731144903)
    ·
      refine ⟨333938028665009300596717355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222625352443339533731144903 333938028665009300596717355)
      ·
        refine ⟨500907042997513950895076033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333938028665009300596717355 500907042997513950895076033)
        ·
          refine ⟨375680282248135463171307025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500907042997513950895076033 375680282248135463171307025)
          ·
            refine ⟨281760211686101597378480269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375680282248135463171307025 281760211686101597378480269)
            ·
              refine ⟨105660079382288099016930101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281760211686101597378480269 105660079382288099016930101)
              ·
                refine ⟨9905632442089509282837197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105660079382288099016930101 9905632442089509282837197)
                ·
                  refine ⟨3714612165783565981063949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9905632442089509282837197 3714612165783565981063949)
                  ·
                    refine ⟨1392979562168837242898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714612165783565981063949 1392979562168837242898981)
                    ·
                      rfl

theorem cell22_4069227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3].length) (baseStart_4069227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069227 prefixEnd_4069227 := by exact prefixLift 4069227
  have htrace : WordTrace (prefixWord ++ tailWord_4069227) baseStart_4069227 baseEnd_4069227 := by
    simpa [prefixWord, tailWord_4069227, baseEnd_4069227] using wordTrace_append hprefix tailTrace_4069227
  have hstable : (prefixWord ++ tailWord_4069227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069227).length < 2 ^ (prefixWord ++ tailWord_4069227).sum := by decide
  have hdescent : baseEnd_4069227 < baseStart_4069227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069246 : List Nat := [4, 2, 3, 1, 1, 2, 3, 6]
def baseStart_4069246 : Nat := 118140960795 + 4069246 * 2 ^ 59
def prefixEnd_4069246 : Nat := 4983230072969 + 3 ^ 40 * 4069246 * 2
def baseEnd_4069246 : Nat := 154776229584125280741547

theorem tailTrace_4069246 : CollatzResearch.WordTrace tailWord_4069246 prefixEnd_4069246 154776229584125280741547 := by
  unfold tailWord_4069246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18552199326978023591546449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98945063077216125821581061 18552199326978023591546449)
  ·
    refine ⟨13914149495233517693659837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18552199326978023591546449 13914149495233517693659837)
    ·
      refine ⟨5217806060712569135122439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13914149495233517693659837 5217806060712569135122439)
      ·
        refine ⟨7826709091068853702683659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217806060712569135122439 7826709091068853702683659)
        ·
          refine ⟨11740063636603280554025489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826709091068853702683659 11740063636603280554025489)
          ·
            refine ⟨8805047727452460415519117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11740063636603280554025489 8805047727452460415519117)
            ·
              refine ⟨3301892897794672655819669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8805047727452460415519117 3301892897794672655819669)
              ·
                refine ⟨154776229584125280741547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3301892897794672655819669 154776229584125280741547)
                ·
                  rfl

theorem cell22_4069246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_4069246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069246 prefixEnd_4069246 := by exact prefixLift 4069246
  have htrace : WordTrace (prefixWord ++ tailWord_4069246) baseStart_4069246 baseEnd_4069246 := by
    simpa [prefixWord, tailWord_4069246, baseEnd_4069246] using wordTrace_append hprefix tailTrace_4069246
  have hstable : (prefixWord ++ tailWord_4069246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069246).length < 2 ^ (prefixWord ++ tailWord_4069246).sum := by decide
  have hdescent : baseEnd_4069246 < baseStart_4069246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069274 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_4069274 : Nat := 118140960795 + 4069274 * 2 ^ 59
def prefixEnd_4069274 : Nat := 4983230072969 + 3 ^ 40 * 4069274 * 2
def baseEnd_4069274 : Nat := 464331883743114928991279

theorem tailTrace_4069274 : CollatzResearch.WordTrace tailWord_4069274 prefixEnd_4069274 464331883743114928991279 := by
  unfold tailWord_4069274
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104653964930687378597719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98945743906481833009593917 37104653964930687378597719)
  ·
    refine ⟨55656980947396031067896579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37104653964930687378597719 55656980947396031067896579)
    ·
      refine ⟨83485471421094046601844869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55656980947396031067896579 83485471421094046601844869)
      ·
        refine ⟨15653525891455133737845913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83485471421094046601844869 15653525891455133737845913)
        ·
          refine ⟨11740144418591350303384435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15653525891455133737845913 11740144418591350303384435)
          ·
            refine ⟨17610216627887025455076653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740144418591350303384435 17610216627887025455076653)
            ·
              refine ⟨6603831235457634545653745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17610216627887025455076653 6603831235457634545653745)
              ·
                refine ⟨4952873426593225909240309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6603831235457634545653745 4952873426593225909240309)
                ·
                  refine ⟨464331883743114928991279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4952873426593225909240309 464331883743114928991279)
                  ·
                    rfl

theorem cell22_4069274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_4069274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069274 prefixEnd_4069274 := by exact prefixLift 4069274
  have htrace : WordTrace (prefixWord ++ tailWord_4069274) baseStart_4069274 baseEnd_4069274 := by
    simpa [prefixWord, tailWord_4069274, baseEnd_4069274] using wordTrace_append hprefix tailTrace_4069274
  have hstable : (prefixWord ++ tailWord_4069274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069274).length < 2 ^ (prefixWord ++ tailWord_4069274).sum := by decide
  have hdescent : baseEnd_4069274 < baseStart_4069274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069304 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_4069304 : Nat := 118140960795 + 4069304 * 2 ^ 59
def prefixEnd_4069304 : Nat := 4983230072969 + 3 ^ 40 * 4069304 * 2
def baseEnd_4069304 : Nat := 1393005920842434708723745

theorem tailTrace_4069304 : CollatzResearch.WordTrace tailWord_4069304 prefixEnd_4069304 1393005920842434708723745 := by
  unfold tailWord_4069304
  simp only [CollatzResearch.WordTrace]
  refine ⟨74209855024807032318991483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98946473366409376425321977 74209855024807032318991483)
  ·
    refine ⟨111314782537210548478487225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74209855024807032318991483 111314782537210548478487225)
    ·
      refine ⟨83486086902907911358865419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111314782537210548478487225 83486086902907911358865419)
      ·
        refine ⟨125229130354361867038298129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83486086902907911358865419 125229130354361867038298129)
        ·
          refine ⟨93921847765771400278723597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125229130354361867038298129 93921847765771400278723597)
          ·
            refine ⟨35220692912164275104521349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93921847765771400278723597 35220692912164275104521349)
            ·
              refine ⟨6603879921030801582097753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35220692912164275104521349 6603879921030801582097753)
              ·
                refine ⟨4952909940773101186573315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6603879921030801582097753 4952909940773101186573315)
                ·
                  refine ⟨7429364911159651779859973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4952909940773101186573315 7429364911159651779859973)
                  ·
                    refine ⟨1393005920842434708723745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429364911159651779859973 1393005920842434708723745)
                    ·
                      rfl

theorem cell22_4069304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_4069304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069304 prefixEnd_4069304 := by exact prefixLift 4069304
  have htrace : WordTrace (prefixWord ++ tailWord_4069304) baseStart_4069304 baseEnd_4069304 := by
    simpa [prefixWord, tailWord_4069304, baseEnd_4069304] using wordTrace_append hprefix tailTrace_4069304
  have hstable : (prefixWord ++ tailWord_4069304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069304).length < 2 ^ (prefixWord ++ tailWord_4069304).sum := by decide
  have hdescent : baseEnd_4069304 < baseStart_4069304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069336 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_4069336 : Nat := 118140960795 + 4069336 * 2 ^ 59
def prefixEnd_4069336 : Nat := 4983230072969 + 3 ^ 40 * 4069336 * 2
def baseEnd_4069336 : Nat := 464338958365465763974549

theorem tailTrace_4069336 : CollatzResearch.WordTrace tailWord_4069336 prefixEnd_4069336 464338958365465763974549 := by
  unfold tailWord_4069336
  simp only [CollatzResearch.WordTrace]
  refine ⟨74210438592749067051573931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98947251456998756068765241 74210438592749067051573931)
  ·
    refine ⟨111315657889123600577360897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74210438592749067051573931 111315657889123600577360897)
    ·
      refine ⟨83486743416842700433020673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111315657889123600577360897 83486743416842700433020673)
      ·
        refine ⟨62615057562632025324765505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83486743416842700433020673 62615057562632025324765505)
        ·
          refine ⟨46961293171974018993574129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62615057562632025324765505 46961293171974018993574129)
          ·
            refine ⟨35220969878980514245180597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46961293171974018993574129 35220969878980514245180597)
            ·
              refine ⟨3301965926154423210485681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35220969878980514245180597 3301965926154423210485681)
              ·
                refine ⟨2476474444615817407864261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301965926154423210485681 2476474444615817407864261)
                ·
                  refine ⟨464338958365465763974549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476474444615817407864261 464338958365465763974549)
                  ·
                    rfl

theorem cell22_4069336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_4069336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069336 prefixEnd_4069336 := by exact prefixLift 4069336
  have htrace : WordTrace (prefixWord ++ tailWord_4069336) baseStart_4069336 baseEnd_4069336 := by
    simpa [prefixWord, tailWord_4069336, baseEnd_4069336] using wordTrace_append hprefix tailTrace_4069336
  have hstable : (prefixWord ++ tailWord_4069336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069336).length < 2 ^ (prefixWord ++ tailWord_4069336).sum := by decide
  have hdescent : baseEnd_4069336 < baseStart_4069336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069347 : List Nat := [1, 1, 1, 6, 1, 2, 1, 9]
def baseStart_4069347 : Nat := 118140960795 + 4069347 * 2 ^ 59
def prefixEnd_4069347 : Nat := 4983230072969 + 3 ^ 40 * 4069347 * 2
def baseEnd_4069347 : Nat := 154780071180132992210957

theorem tailTrace_4069347 : CollatzResearch.WordTrace tailWord_4069347 prefixEnd_4069347 154780071180132992210957 := by
  unfold tailWord_4069347
  simp only [CollatzResearch.WordTrace]
  refine ⟨148421278388458282981798295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98947518925638855321198863 148421278388458282981798295)
  ·
    refine ⟨222631917582687424472697443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148421278388458282981798295 222631917582687424472697443)
    ·
      refine ⟨333947876374031136709046165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222631917582687424472697443 333947876374031136709046165)
      ·
        refine ⟨15653806705032709533236539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333947876374031136709046165 15653806705032709533236539)
        ·
          refine ⟨23480710057549064299854809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15653806705032709533236539 23480710057549064299854809)
          ·
            refine ⟨17610532543161798224891107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23480710057549064299854809 17610532543161798224891107)
            ·
              refine ⟨26415798814742697337336661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17610532543161798224891107 26415798814742697337336661)
              ·
                refine ⟨154780071180132992210957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26415798814742697337336661 154780071180132992210957)
                ·
                  rfl

theorem cell22_4069347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 9].length) (baseStart_4069347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069347 prefixEnd_4069347 := by exact prefixLift 4069347
  have htrace : WordTrace (prefixWord ++ tailWord_4069347) baseStart_4069347 baseEnd_4069347 := by
    simpa [prefixWord, tailWord_4069347, baseEnd_4069347] using wordTrace_append hprefix tailTrace_4069347
  have hstable : (prefixWord ++ tailWord_4069347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069347).length < 2 ^ (prefixWord ++ tailWord_4069347).sum := by decide
  have hdescent : baseEnd_4069347 < baseStart_4069347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069430 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4069430 : Nat := 118140960795 + 4069430 * 2 ^ 59
def prefixEnd_4069430 : Nat := 4983230072969 + 3 ^ 40 * 4069430 * 2
def baseEnd_4069430 : Nat := 1393049053217412380073359

theorem tailTrace_4069430 : CollatzResearch.WordTrace tailWord_4069430 prefixEnd_4069430 1393049053217412380073359 := by
  unfold tailWord_4069430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276519102947349259816859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98949537098105058771379829 9276519102947349259816859)
  ·
    refine ⟨13914778654421023889725289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276519102947349259816859 13914778654421023889725289)
    ·
      refine ⟨10436083990815767917293967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13914778654421023889725289 10436083990815767917293967)
      ·
        refine ⟨15654125986223651875940951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10436083990815767917293967 15654125986223651875940951)
        ·
          refine ⟨23481188979335477813911427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15654125986223651875940951 23481188979335477813911427)
          ·
            refine ⟨35221783469003216720867141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23481188979335477813911427 35221783469003216720867141)
            ·
              refine ⟨6604084400438103135162589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35221783469003216720867141 6604084400438103135162589)
              ·
                refine ⟨2476531650164288675685971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6604084400438103135162589 2476531650164288675685971)
                ·
                  refine ⟨3714797475246433013528957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476531650164288675685971 3714797475246433013528957)
                  ·
                    refine ⟨1393049053217412380073359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714797475246433013528957 1393049053217412380073359)
                    ·
                      rfl

theorem cell22_4069430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4069430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069430 prefixEnd_4069430 := by exact prefixLift 4069430
  have htrace : WordTrace (prefixWord ++ tailWord_4069430) baseStart_4069430 baseEnd_4069430 := by
    simpa [prefixWord, tailWord_4069430, baseEnd_4069430] using wordTrace_append hprefix tailTrace_4069430
  have hstable : (prefixWord ++ tailWord_4069430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069430).length < 2 ^ (prefixWord ++ tailWord_4069430).sum := by decide
  have hdescent : baseEnd_4069430 < baseStart_4069430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069454 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_4069454 : Nat := 118140960795 + 4069454 * 2 ^ 59
def prefixEnd_4069454 : Nat := 4983230072969 + 3 ^ 40 * 4069454 * 2
def baseEnd_4069454 : Nat := 464352422969294772491095

theorem tailTrace_4069454 : CollatzResearch.WordTrace tailWord_4069454 prefixEnd_4069454 464352422969294772491095 := by
  unfold tailWord_4069454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553147624883830031992927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98950120666047093503962277 18553147624883830031992927)
  ·
    refine ⟨27829721437325745047989391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553147624883830031992927 27829721437325745047989391)
    ·
      refine ⟨41744582155988617571984087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27829721437325745047989391 41744582155988617571984087)
      ·
        refine ⟨62616873233982926357976131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41744582155988617571984087 62616873233982926357976131)
        ·
          refine ⟨93925309850974389536964197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62616873233982926357976131 93925309850974389536964197)
          ·
            refine ⟨17610995597057698038180787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93925309850974389536964197 17610995597057698038180787)
            ·
              refine ⟨26416493395586547057271181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17610995597057698038180787 26416493395586547057271181)
              ·
                refine ⟨9906185023344955146476693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26416493395586547057271181 9906185023344955146476693)
                ·
                  refine ⟨464352422969294772491095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9906185023344955146476693 464352422969294772491095)
                  ·
                    rfl

theorem cell22_4069454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_4069454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069454 prefixEnd_4069454 := by exact prefixLift 4069454
  have htrace : WordTrace (prefixWord ++ tailWord_4069454) baseStart_4069454 baseEnd_4069454 := by
    simpa [prefixWord, tailWord_4069454, baseEnd_4069454] using wordTrace_append hprefix tailTrace_4069454
  have hstable : (prefixWord ++ tailWord_4069454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069454).length < 2 ^ (prefixWord ++ tailWord_4069454).sum := by decide
  have hdescent : baseEnd_4069454 < baseStart_4069454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069484 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_4069484 : Nat := 118140960795 + 4069484 * 2 ^ 59
def prefixEnd_4069484 : Nat := 4983230072969 + 3 ^ 40 * 4069484 * 2
def baseEnd_4069484 : Nat := 1393067538520974239223193

theorem tailTrace_4069484 : CollatzResearch.WordTrace tailWord_4069484 prefixEnd_4069484 1393067538520974239223193 := by
  unfold tailWord_4069484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74213137594480977689767753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98950850125974636919690337 74213137594480977689767753)
  ·
    refine ⟨55659853195860733267325815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74213137594480977689767753 55659853195860733267325815)
    ·
      refine ⟨83489779793791099900988723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55659853195860733267325815 83489779793791099900988723)
      ·
        refine ⟨125234669690686649851483085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83489779793791099900988723 125234669690686649851483085)
        ·
          refine ⟨46963001134007493694306157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125234669690686649851483085 46963001134007493694306157)
          ·
            refine ⟨17611125425252810135364809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46963001134007493694306157 17611125425252810135364809)
            ·
              refine ⟨13208344068939607601523607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17611125425252810135364809 13208344068939607601523607)
              ·
                refine ⟨19812516103409411402285411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13208344068939607601523607 19812516103409411402285411)
                ·
                  refine ⟨29718774155114117103428117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19812516103409411402285411 29718774155114117103428117)
                  ·
                    refine ⟨1393067538520974239223193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29718774155114117103428117 1393067538520974239223193)
                    ·
                      rfl

theorem cell22_4069484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_4069484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069484 prefixEnd_4069484 := by exact prefixLift 4069484
  have htrace : WordTrace (prefixWord ++ tailWord_4069484) baseStart_4069484 baseEnd_4069484 := by
    simpa [prefixWord, tailWord_4069484, baseEnd_4069484] using wordTrace_append hprefix tailTrace_4069484
  have hstable : (prefixWord ++ tailWord_4069484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069484).length < 2 ^ (prefixWord ++ tailWord_4069484).sum := by decide
  have hdescent : baseEnd_4069484 < baseStart_4069484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069486 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4069486 : Nat := 118140960795 + 4069486 * 2 ^ 59
def prefixEnd_4069486 : Nat := 4983230072969 + 3 ^ 40 * 4069486 * 2
def baseEnd_4069486 : Nat := 1393068223161846900673187

theorem tailTrace_4069486 : CollatzResearch.WordTrace tailWord_4069486 prefixEnd_4069486 1393068223161846900673187 := by
  unfold tailWord_4069486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18553293516869338715138539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98950898756636473147405541 18553293516869338715138539)
  ·
    refine ⟨27829940275304008072707809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18553293516869338715138539 27829940275304008072707809)
    ·
      refine ⟨20872455206478006054530857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27829940275304008072707809 20872455206478006054530857)
      ·
        refine ⟨15654341404858504540898143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20872455206478006054530857 15654341404858504540898143)
        ·
          refine ⟨23481512107287756811347215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15654341404858504540898143 23481512107287756811347215)
          ·
            refine ⟨35222268160931635217020823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23481512107287756811347215 35222268160931635217020823)
            ·
              refine ⟨52833402241397452825531235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35222268160931635217020823 52833402241397452825531235)
              ·
                refine ⟨79250103362096179238296853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52833402241397452825531235 79250103362096179238296853)
                ·
                  refine ⟨3714848595098258401795165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79250103362096179238296853 3714848595098258401795165)
                  ·
                    refine ⟨1393068223161846900673187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3714848595098258401795165 1393068223161846900673187)
                    ·
                      rfl

theorem cell22_4069486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4069486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069486 prefixEnd_4069486 := by exact prefixLift 4069486
  have htrace : WordTrace (prefixWord ++ tailWord_4069486) baseStart_4069486 baseEnd_4069486 := by
    simpa [prefixWord, tailWord_4069486, baseEnd_4069486] using wordTrace_append hprefix tailTrace_4069486
  have hstable : (prefixWord ++ tailWord_4069486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069486).length < 2 ^ (prefixWord ++ tailWord_4069486).sum := by decide
  have hdescent : baseEnd_4069486 < baseStart_4069486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069488 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_4069488 : Nat := 118140960795 + 4069488 * 2 ^ 59
def prefixEnd_4069488 : Nat := 4983230072969 + 3 ^ 40 * 4069488 * 2
def baseEnd_4069488 : Nat := 464356302600906520707727

theorem tailTrace_4069488 : CollatzResearch.WordTrace tailWord_4069488 prefixEnd_4069488 464356302600906520707727 := by
  unfold tailWord_4069488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74213210540473732031340559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98950947387298309375120745 74213210540473732031340559)
  ·
    refine ⟨111319815810710598047010839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74213210540473732031340559 111319815810710598047010839)
    ·
      refine ⟨166979723716065897070516259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111319815810710598047010839 166979723716065897070516259)
      ·
        refine ⟨250469585574098845605774389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166979723716065897070516259 250469585574098845605774389)
        ·
          refine ⟨23481523647571766775541349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250469585574098845605774389 23481523647571766775541349)
          ·
            refine ⟨4402785683919706270414003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23481523647571766775541349 4402785683919706270414003)
            ·
              refine ⟨6604178525879559405621005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402785683919706270414003 6604178525879559405621005)
              ·
                refine ⟨2476566947204834777107877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6604178525879559405621005 2476566947204834777107877)
                ·
                  refine ⟨464356302600906520707727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476566947204834777107877 464356302600906520707727)
                  ·
                    rfl

theorem cell22_4069488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_4069488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069488 prefixEnd_4069488 := by exact prefixLift 4069488
  have htrace : WordTrace (prefixWord ++ tailWord_4069488) baseStart_4069488 baseEnd_4069488 := by
    simpa [prefixWord, tailWord_4069488, baseEnd_4069488] using wordTrace_append hprefix tailTrace_4069488
  have hstable : (prefixWord ++ tailWord_4069488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069488).length < 2 ^ (prefixWord ++ tailWord_4069488).sum := by decide
  have hdescent : baseEnd_4069488 < baseStart_4069488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069501 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_4069501 : Nat := 118140960795 + 4069501 * 2 ^ 59
def prefixEnd_4069501 : Nat := 4983230072969 + 3 ^ 40 * 4069501 * 2
def baseEnd_4069501 : Nat := 1393073357968391861548141

theorem tailTrace_4069501 : CollatzResearch.WordTrace tailWord_4069501 prefixEnd_4069501 1393073357968391861548141 := by
  unfold tailWord_4069501
  simp only [CollatzResearch.WordTrace]
  refine ⟨148426895229900367282904357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98951263486600244855269571 148426895229900367282904357)
  ·
    refine ⟨27830042855606318865544567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148426895229900367282904357 27830042855606318865544567)
    ·
      refine ⟨41745064283409478298316851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27830042855606318865544567 41745064283409478298316851)
      ·
        refine ⟨62617596425114217447475277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41745064283409478298316851 62617596425114217447475277)
        ·
          refine ⟨23481598659417831542803229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62617596425114217447475277 23481598659417831542803229)
          ·
            refine ⟨8805599497281686828551211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23481598659417831542803229 8805599497281686828551211)
            ·
              refine ⟨13208399245922530242826817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805599497281686828551211 13208399245922530242826817)
              ·
                refine ⟨9906299434441897682120113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13208399245922530242826817 9906299434441897682120113)
                ·
                  refine ⟨7429724575831423261590085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9906299434441897682120113 7429724575831423261590085)
                  ·
                    refine ⟨1393073357968391861548141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429724575831423261590085 1393073357968391861548141)
                    ·
                      rfl

theorem cell22_4069501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_4069501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069501 prefixEnd_4069501 := by exact prefixLift 4069501
  have htrace : WordTrace (prefixWord ++ tailWord_4069501) baseStart_4069501 baseEnd_4069501 := by
    simpa [prefixWord, tailWord_4069501, baseEnd_4069501] using wordTrace_append hprefix tailTrace_4069501
  have hstable : (prefixWord ++ tailWord_4069501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069501).length < 2 ^ (prefixWord ++ tailWord_4069501).sum := by decide
  have hdescent : baseEnd_4069501 < baseStart_4069501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069505 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 4]
def baseStart_4069505 : Nat := 118140960795 + 4069505 * 2 ^ 59
def prefixEnd_4069505 : Nat := 4983230072969 + 3 ^ 40 * 4069505 * 2
def baseEnd_4069505 : Nat := 464358242416712394816043

theorem tailTrace_4069505 : CollatzResearch.WordTrace tailWord_4069505 prefixEnd_4069505 464358242416712394816043 := by
  unfold tailWord_4069505
  simp only [CollatzResearch.WordTrace]
  refine ⟨148427041121885875966049969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98951360747923917310699979 148427041121885875966049969)
  ·
    refine ⟨111320280841414406974537477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148427041121885875966049969 111320280841414406974537477)
    ·
      refine ⟨20872552657765201307725777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111320280841414406974537477 20872552657765201307725777)
      ·
        refine ⟨15654414493323900980794333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20872552657765201307725777 15654414493323900980794333)
        ·
          refine ⟨5870405434996462867797875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15654414493323900980794333 5870405434996462867797875)
          ·
            refine ⟨8805608152494694301696813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870405434996462867797875 8805608152494694301696813)
            ·
              refine ⟨3302103057185510363136305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8805608152494694301696813 3302103057185510363136305)
              ·
                refine ⟨2476577292889132772352229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302103057185510363136305 2476577292889132772352229)
                ·
                  refine ⟨464358242416712394816043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476577292889132772352229 464358242416712394816043)
                  ·
                    rfl

theorem cell22_4069505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_4069505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069505 prefixEnd_4069505 := by exact prefixLift 4069505
  have htrace : WordTrace (prefixWord ++ tailWord_4069505) baseStart_4069505 baseEnd_4069505 := by
    simpa [prefixWord, tailWord_4069505, baseEnd_4069505] using wordTrace_append hprefix tailTrace_4069505
  have hstable : (prefixWord ++ tailWord_4069505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069505).length < 2 ^ (prefixWord ++ tailWord_4069505).sum := by decide
  have hdescent : baseEnd_4069505 < baseStart_4069505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069556 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4069556 : Nat := 118140960795 + 4069556 * 2 ^ 59
def prefixEnd_4069556 : Nat := 4983230072969 + 3 ^ 40 * 4069556 * 2
def baseEnd_4069556 : Nat := 464364061864130017140991

theorem tailTrace_4069556 : CollatzResearch.WordTrace tailWord_4069556 prefixEnd_4069556 464364061864130017140991 := by
  unfold tailWord_4069556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74214450622350555838078261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98952600829800741117437681 74214450622350555838078261)
  ·
    refine ⟨6957604745845364609819837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74214450622350555838078261 6957604745845364609819837)
    ·
      refine ⟨2609101779692011728682439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6957604745845364609819837 2609101779692011728682439)
      ·
        refine ⟨3913652669538017593023659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609101779692011728682439 3913652669538017593023659)
        ·
          refine ⟨5870479004307026389535489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913652669538017593023659 5870479004307026389535489)
          ·
            refine ⟨4402859253230269792151617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870479004307026389535489 4402859253230269792151617)
            ·
              refine ⟨3302144439922702344113713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402859253230269792151617 3302144439922702344113713)
              ·
                refine ⟨2476608329942026758085285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302144439922702344113713 2476608329942026758085285)
                ·
                  refine ⟨464364061864130017140991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476608329942026758085285 464364061864130017140991)
                  ·
                    rfl

theorem cell22_4069556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4069556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069556 prefixEnd_4069556 := by exact prefixLift 4069556
  have htrace : WordTrace (prefixWord ++ tailWord_4069556) baseStart_4069556 baseEnd_4069556 := by
    simpa [prefixWord, tailWord_4069556, baseEnd_4069556] using wordTrace_append hprefix tailTrace_4069556
  have hstable : (prefixWord ++ tailWord_4069556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069556).length < 2 ^ (prefixWord ++ tailWord_4069556).sum := by decide
  have hdescent : baseEnd_4069556 < baseStart_4069556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069561 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 5]
def baseStart_4069561 : Nat := 118140960795 + 4069561 * 2 ^ 59
def prefixEnd_4069561 : Nat := 4983230072969 + 3 ^ 40 * 4069561 * 2
def baseEnd_4069561 : Nat := 464364632398190568349319

theorem tailTrace_4069561 : CollatzResearch.WordTrace tailWord_4069561 prefixEnd_4069561 464364632398190568349319 := by
  unfold tailWord_4069561
  simp only [CollatzResearch.WordTrace]
  refine ⟨148429083609682997530088537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98952722406455331686725691 148429083609682997530088537)
  ·
    refine ⟨111321812707262248147566403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148429083609682997530088537 111321812707262248147566403)
    ·
      refine ⟨166982719060893372221349605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111321812707262248147566403 166982719060893372221349605)
      ·
        refine ⟨31309259823917507291503051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166982719060893372221349605 31309259823917507291503051)
        ·
          refine ⟨46963889735876260937254577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31309259823917507291503051 46963889735876260937254577)
          ·
            refine ⟨35222917301907195702940933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46963889735876260937254577 35222917301907195702940933)
            ·
              refine ⟨6604296994107599194301425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35222917301907195702940933 6604296994107599194301425)
              ·
                refine ⟨4953222745580699395726069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604296994107599194301425 4953222745580699395726069)
                ·
                  refine ⟨464364632398190568349319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953222745580699395726069 464364632398190568349319)
                  ·
                    rfl

theorem cell22_4069561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_4069561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069561 prefixEnd_4069561 := by exact prefixLift 4069561
  have htrace : WordTrace (prefixWord ++ tailWord_4069561) baseStart_4069561 baseEnd_4069561 := by
    simpa [prefixWord, tailWord_4069561, baseEnd_4069561] using wordTrace_append hprefix tailTrace_4069561
  have hstable : (prefixWord ++ tailWord_4069561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069561).length < 2 ^ (prefixWord ++ tailWord_4069561).sum := by decide
  have hdescent : baseEnd_4069561 < baseStart_4069561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069591 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 1, 4]
def baseStart_4069591 : Nat := 118140960795 + 4069591 * 2 ^ 59
def prefixEnd_4069591 : Nat := 4983230072969 + 3 ^ 40 * 4069591 * 2
def baseEnd_4069591 : Nat := 1393104166807661626797865

theorem tailTrace_4069591 : CollatzResearch.WordTrace tailWord_4069591 prefixEnd_4069591 1393104166807661626797865 := by
  unfold tailWord_4069591
  simp only [CollatzResearch.WordTrace]
  refine ⟨148430177799574312653680627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98953451866382875102453751 148430177799574312653680627)
  ·
    refine ⟨222645266699361468980520941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148430177799574312653680627 222645266699361468980520941)
    ·
      refine ⟨83491975012260550867695353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222645266699361468980520941 83491975012260550867695353)
      ·
        refine ⟨62618981259195413150771515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83491975012260550867695353 62618981259195413150771515)
        ·
          refine ⟨93928471888793119726157273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62618981259195413150771515 93928471888793119726157273)
          ·
            refine ⟨70446353916594839794617955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93928471888793119726157273 70446353916594839794617955)
            ·
              refine ⟨105669530874892259691926933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70446353916594839794617955 105669530874892259691926933)
              ·
                refine ⟨4953259259760574673059075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105669530874892259691926933 4953259259760574673059075)
                ·
                  refine ⟨7429888889640862009588613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953259259760574673059075 7429888889640862009588613)
                  ·
                    refine ⟨1393104166807661626797865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429888889640862009588613 1393104166807661626797865)
                    ·
                      rfl

theorem cell22_4069591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_4069591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069591 prefixEnd_4069591 := by exact prefixLift 4069591
  have htrace : WordTrace (prefixWord ++ tailWord_4069591) baseStart_4069591 baseEnd_4069591 := by
    simpa [prefixWord, tailWord_4069591, baseEnd_4069591] using wordTrace_append hprefix tailTrace_4069591
  have hstable : (prefixWord ++ tailWord_4069591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069591).length < 2 ^ (prefixWord ++ tailWord_4069591).sum := by decide
  have hdescent : baseEnd_4069591 < baseStart_4069591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069608 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4069608 : Nat := 118140960795 + 4069608 * 2 ^ 59
def prefixEnd_4069608 : Nat := 4983230072969 + 3 ^ 40 * 4069608 * 2
def baseEnd_4069608 : Nat := 1393109986255079249122813

theorem tailTrace_4069608 : CollatzResearch.WordTrace tailWord_4069608 prefixEnd_4069608 1393109986255079249122813 := by
  unfold tailWord_4069608
  simp only [CollatzResearch.WordTrace]
  refine ⟨74215398920256362278524739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98953865227008483038032985 74215398920256362278524739)
  ·
    refine ⟨111323098380384543417787109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74215398920256362278524739 111323098380384543417787109)
    ·
      refine ⟨20873080946322101890835083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111323098380384543417787109 20873080946322101890835083)
      ·
        refine ⟨31309621419483152836252625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873080946322101890835083 31309621419483152836252625)
        ·
          refine ⟨23482216064612364627189469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31309621419483152836252625 23482216064612364627189469)
          ·
            refine ⟨8805831024229636735196051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23482216064612364627189469 8805831024229636735196051)
            ·
              refine ⟨13208746536344455102794077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805831024229636735196051 13208746536344455102794077)
              ·
                refine ⟨4953279951129170663547779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13208746536344455102794077 4953279951129170663547779)
                ·
                  refine ⟨7429919926693755995321669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953279951129170663547779 7429919926693755995321669)
                  ·
                    refine ⟨1393109986255079249122813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7429919926693755995321669 1393109986255079249122813)
                    ·
                      rfl

theorem cell22_4069608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4069608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069608 prefixEnd_4069608 := by exact prefixLift 4069608
  have htrace : WordTrace (prefixWord ++ tailWord_4069608) baseStart_4069608 baseEnd_4069608 := by
    simpa [prefixWord, tailWord_4069608, baseEnd_4069608] using wordTrace_append hprefix tailTrace_4069608
  have hstable : (prefixWord ++ tailWord_4069608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069608).length < 2 ^ (prefixWord ++ tailWord_4069608).sum := by decide
  have hdescent : baseEnd_4069608 < baseStart_4069608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069730 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4069730 : Nat := 118140960795 + 4069730 * 2 ^ 59
def prefixEnd_4069730 : Nat := 4983230072969 + 3 ^ 40 * 4069730 * 2
def baseEnd_4069730 : Nat := 464383916449437199190813

theorem tailTrace_4069730 : CollatzResearch.WordTrace tailWord_4069730 prefixEnd_4069730 464383916449437199190813 := by
  unfold tailWord_4069730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37108811886517684848247661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98956831697380492928660429 37108811886517684848247661)
  ·
    refine ⟨13915804457444131818092873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37108811886517684848247661 13915804457444131818092873)
    ·
      refine ⟨10436853343083098863569655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13915804457444131818092873 10436853343083098863569655)
      ·
        refine ⟨15655280014624648295354483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10436853343083098863569655 15655280014624648295354483)
        ·
          refine ⟨23482920021936972443031725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15655280014624648295354483 23482920021936972443031725)
          ·
            refine ⟨8806095008226364666136897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23482920021936972443031725 8806095008226364666136897)
            ·
              refine ⟨6604571256169773499602673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8806095008226364666136897 6604571256169773499602673)
              ·
                refine ⟨4953428442127330124702005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604571256169773499602673 4953428442127330124702005)
                ·
                  refine ⟨464383916449437199190813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953428442127330124702005 464383916449437199190813)
                  ·
                    rfl

theorem cell22_4069730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4069730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069730 prefixEnd_4069730 := by exact prefixLift 4069730
  have htrace : WordTrace (prefixWord ++ tailWord_4069730) baseStart_4069730 baseEnd_4069730 := by
    simpa [prefixWord, tailWord_4069730, baseEnd_4069730] using wordTrace_append hprefix tailTrace_4069730
  have hstable : (prefixWord ++ tailWord_4069730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069730).length < 2 ^ (prefixWord ++ tailWord_4069730).sum := by decide
  have hdescent : baseEnd_4069730 < baseStart_4069730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069820 : List Nat := [2, 2, 2, 4, 1, 1, 4, 6]
def baseStart_4069820 : Nat := 118140960795 + 4069820 * 2 ^ 59
def prefixEnd_4069820 : Nat := 4983230072969 + 3 ^ 40 * 4069820 * 2
def baseEnd_4069820 : Nat := 154798062020842373646907

theorem tailTrace_4069820 : CollatzResearch.WordTrace tailWord_4069820 prefixEnd_4069820 154798062020842373646907 := by
  unfold tailWord_4069820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74219265057872342381883457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98959020077163123175844609 74219265057872342381883457)
  ·
    refine ⟨55664448793404256786412593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74219265057872342381883457 55664448793404256786412593)
    ·
      refine ⟨41748336595053192589809445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55664448793404256786412593 41748336595053192589809445)
      ·
        refine ⟨7827813111572473610589271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41748336595053192589809445 7827813111572473610589271)
        ·
          refine ⟨11741719667358710415883907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7827813111572473610589271 11741719667358710415883907)
          ·
            refine ⟨17612579501038065623825861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11741719667358710415883907 17612579501038065623825861)
            ·
              refine ⟨3302358656444637304467349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17612579501038065623825861 3302358656444637304467349)
              ·
                refine ⟨154798062020842373646907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3302358656444637304467349 154798062020842373646907)
                ·
                  rfl

theorem cell22_4069820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_4069820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069820 prefixEnd_4069820 := by exact prefixLift 4069820
  have htrace : WordTrace (prefixWord ++ tailWord_4069820) baseStart_4069820 baseEnd_4069820 := by
    simpa [prefixWord, tailWord_4069820, baseEnd_4069820] using wordTrace_append hprefix tailTrace_4069820
  have hstable : (prefixWord ++ tailWord_4069820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069820).length < 2 ^ (prefixWord ++ tailWord_4069820).sum := by decide
  have hdescent : baseEnd_4069820 < baseStart_4069820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069848 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_4069848 : Nat := 118140960795 + 4069848 * 2 ^ 59
def prefixEnd_4069848 : Nat := 4983230072969 + 3 ^ 40 * 4069848 * 2
def baseEnd_4069848 : Nat := 464397381053266207707359

theorem tailTrace_4069848 : CollatzResearch.WordTrace tailWord_4069848 prefixEnd_4069848 464397381053266207707359 := by
  unfold tailWord_4069848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74219775679821622772893099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98959700906428830363857465 74219775679821622772893099)
  ·
    refine ⟨111329663519732434159339649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74219775679821622772893099 111329663519732434159339649)
    ·
      refine ⟨83497247639799325619504737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111329663519732434159339649 83497247639799325619504737)
      ·
        refine ⟨62622935729849494214628553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83497247639799325619504737 62622935729849494214628553)
        ·
          refine ⟨46967201797387120660971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62622935729849494214628553 46967201797387120660971415)
          ·
            refine ⟨70450802696080680991457123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46967201797387120660971415 70450802696080680991457123)
            ·
              refine ⟨105676204044121021487185685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70450802696080680991457123 105676204044121021487185685)
              ·
                refine ⟨4953572064568172882211829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105676204044121021487185685 4953572064568172882211829)
                ·
                  refine ⟨464397381053266207707359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953572064568172882211829 464397381053266207707359)
                  ·
                    rfl

theorem cell22_4069848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_4069848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069848 prefixEnd_4069848 := by exact prefixLift 4069848
  have htrace : WordTrace (prefixWord ++ tailWord_4069848) baseStart_4069848 baseEnd_4069848 := by
    simpa [prefixWord, tailWord_4069848, baseEnd_4069848] using wordTrace_append hprefix tailTrace_4069848
  have hstable : (prefixWord ++ tailWord_4069848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069848).length < 2 ^ (prefixWord ++ tailWord_4069848).sum := by decide
  have hdescent : baseEnd_4069848 < baseStart_4069848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069858 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4069858 : Nat := 118140960795 + 4069858 * 2 ^ 59
def prefixEnd_4069858 : Nat := 4983230072969 + 3 ^ 40 * 4069858 * 2
def baseEnd_4069858 : Nat := 1393195566364161930372047

theorem tailTrace_4069858 : CollatzResearch.WordTrace tailWord_4069858 prefixEnd_4069858 1393195566364161930372047 := by
  unfold tailWord_4069858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109979022401754313412557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98959944059738011502433485 37109979022401754313412557)
  ·
    refine ⟨13916242133400657867529709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37109979022401754313412557 13916242133400657867529709)
    ·
      refine ⟨5218590800025246700323641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13916242133400657867529709 5218590800025246700323641)
      ·
        refine ⟨3913943100018935025242731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5218590800025246700323641 3913943100018935025242731)
        ·
          refine ⟨5870914650028402537864097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913943100018935025242731 5870914650028402537864097)
          ·
            refine ⟨4403185987521301903398073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5870914650028402537864097 4403185987521301903398073)
            ·
              refine ⟨3302389490640976427548555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403185987521301903398073 3302389490640976427548555)
              ·
                refine ⟨4953584235961464641322833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302389490640976427548555 4953584235961464641322833)
                ·
                  refine ⟨3715188176971098480992125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953584235961464641322833 3715188176971098480992125)
                  ·
                    refine ⟨1393195566364161930372047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715188176971098480992125 1393195566364161930372047)
                    ·
                      rfl

theorem cell22_4069858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4069858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069858 prefixEnd_4069858 := by exact prefixLift 4069858
  have htrace : WordTrace (prefixWord ++ tailWord_4069858) baseStart_4069858 baseEnd_4069858 := by
    simpa [prefixWord, tailWord_4069858, baseEnd_4069858] using wordTrace_append hprefix tailTrace_4069858
  have hstable : (prefixWord ++ tailWord_4069858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069858).length < 2 ^ (prefixWord ++ tailWord_4069858).sum := by decide
  have hdescent : baseEnd_4069858 < baseStart_4069858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069863 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4069863 : Nat := 118140960795 + 4069863 * 2 ^ 59
def prefixEnd_4069863 : Nat := 4983230072969 + 3 ^ 40 * 4069863 * 2
def baseEnd_4069863 : Nat := 1393197277966343583997031

theorem tailTrace_4069863 : CollatzResearch.WordTrace tailWord_4069863 prefixEnd_4069863 1393197277966343583997031 := by
  unfold tailWord_4069863
  simp only [CollatzResearch.WordTrace]
  refine ⟨148440098454588903107582243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98960065636392602071721495 148440098454588903107582243)
  ·
    refine ⟨222660147681883354661373365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148440098454588903107582243 222660147681883354661373365)
    ·
      refine ⟨20874388845176564499503753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222660147681883354661373365 20874388845176564499503753)
      ·
        refine ⟨15655791633882423374627815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20874388845176564499503753 15655791633882423374627815)
        ·
          refine ⟨23483687450823635061941723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15655791633882423374627815 23483687450823635061941723)
          ·
            refine ⟨35225531176235452592912585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23483687450823635061941723 35225531176235452592912585)
            ·
              refine ⟨26419148382176589444684439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35225531176235452592912585 26419148382176589444684439)
              ·
                refine ⟨39628722573264884167026659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26419148382176589444684439 39628722573264884167026659)
                ·
                  refine ⟨59443083859897326250539989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39628722573264884167026659 59443083859897326250539989)
                  ·
                    refine ⟨1393197277966343583997031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59443083859897326250539989 1393197277966343583997031)
                    ·
                      rfl

theorem cell22_4069863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4069863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069863 prefixEnd_4069863 := by exact prefixLift 4069863
  have htrace : WordTrace (prefixWord ++ tailWord_4069863) baseStart_4069863 baseEnd_4069863 := by
    simpa [prefixWord, tailWord_4069863, baseEnd_4069863] using wordTrace_append hprefix tailTrace_4069863
  have hstable : (prefixWord ++ tailWord_4069863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069863).length < 2 ^ (prefixWord ++ tailWord_4069863).sum := by decide
  have hdescent : baseEnd_4069863 < baseStart_4069863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069938 : List Nat := [3, 2, 1, 1, 2, 1, 2, 10]
def baseStart_4069938 : Nat := 118140960795 + 4069938 * 2 ^ 59
def prefixEnd_4069938 : Nat := 4983230072969 + 3 ^ 40 * 4069938 * 2
def baseEnd_4069938 : Nat := 154802550222118709819089

theorem tailTrace_4069938 : CollatzResearch.WordTrace tailWord_4069938 prefixEnd_4069938 154802550222118709819089 := by
  unfold tailWord_4069938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37110708482329297729140617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98961889286211460611041645 37110708482329297729140617)
  ·
    refine ⟨27833031361746973296855463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37110708482329297729140617 27833031361746973296855463)
    ·
      refine ⟨41749547042620459945283195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27833031361746973296855463 41749547042620459945283195)
      ·
        refine ⟨62624320563930689917924793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41749547042620459945283195 62624320563930689917924793)
        ·
          refine ⟨46968240422948017438443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62624320563930689917924793 46968240422948017438443595)
          ·
            refine ⟨70452360634422026157665393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46968240422948017438443595 70452360634422026157665393)
            ·
              refine ⟨52839270475816519618249045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70452360634422026157665393 52839270475816519618249045)
              ·
                refine ⟨154802550222118709819089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52839270475816519618249045 154802550222118709819089)
                ·
                  rfl

theorem cell22_4069938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_4069938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069938 prefixEnd_4069938 := by exact prefixLift 4069938
  have htrace : WordTrace (prefixWord ++ tailWord_4069938) baseStart_4069938 baseEnd_4069938 := by
    simpa [prefixWord, tailWord_4069938, baseEnd_4069938] using wordTrace_append hprefix tailTrace_4069938
  have hstable : (prefixWord ++ tailWord_4069938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069938).length < 2 ^ (prefixWord ++ tailWord_4069938).sum := by decide
  have hdescent : baseEnd_4069938 < baseStart_4069938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069942 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4069942 : Nat := 118140960795 + 4069942 * 2 ^ 59
def prefixEnd_4069942 : Nat := 4983230072969 + 3 ^ 40 * 4069942 * 2
def baseEnd_4069942 : Nat := 1393224321280813711271789

theorem tailTrace_4069942 : CollatzResearch.WordTrace tailWord_4069942 prefixEnd_4069942 1393224321280813711271789 := by
  unfold tailWord_4069942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277686238831418724981755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98961986547535133066472053 9277686238831418724981755)
  ·
    refine ⟨13916529358247128087472633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9277686238831418724981755 13916529358247128087472633)
    ·
      refine ⟨10437397018685346065604475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13916529358247128087472633 10437397018685346065604475)
      ·
        refine ⟨15656095528028019098406713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437397018685346065604475 15656095528028019098406713)
        ·
          refine ⟨11742071646021014323805035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15656095528028019098406713 11742071646021014323805035)
          ·
            refine ⟨17613107469031521485707553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742071646021014323805035 17613107469031521485707553)
            ·
              refine ⟨13209830601773641114280665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17613107469031521485707553 13209830601773641114280665)
              ·
                refine ⟨9907372951330230835710499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13209830601773641114280665 9907372951330230835710499)
                ·
                  refine ⟨14861059426995346253565749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9907372951330230835710499 14861059426995346253565749)
                  ·
                    refine ⟨1393224321280813711271789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14861059426995346253565749 1393224321280813711271789)
                    ·
                      rfl

theorem cell22_4069942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4069942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069942 prefixEnd_4069942 := by exact prefixLift 4069942
  have htrace : WordTrace (prefixWord ++ tailWord_4069942) baseStart_4069942 baseEnd_4069942 := by
    simpa [prefixWord, tailWord_4069942, baseEnd_4069942] using wordTrace_append hprefix tailTrace_4069942
  have hstable : (prefixWord ++ tailWord_4069942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069942).length < 2 ^ (prefixWord ++ tailWord_4069942).sum := by decide
  have hdescent : baseEnd_4069942 < baseStart_4069942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069959 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 2, 3]
def baseStart_4069959 : Nat := 118140960795 + 4069959 * 2 ^ 59
def prefixEnd_4069959 : Nat := 4983230072969 + 3 ^ 40 * 4069959 * 2
def baseEnd_4069959 : Nat := 1393230140728231333596737

theorem tailTrace_4069959 : CollatzResearch.WordTrace tailWord_4069959 prefixEnd_4069959 1393230140728231333596737 := by
  unfold tailWord_4069959
  simp only [CollatzResearch.WordTrace]
  refine ⟨148443599862241111503076931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98962399908160741002051287 148443599862241111503076931)
  ·
    refine ⟨222665399793361667254615397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148443599862241111503076931 222665399793361667254615397)
    ·
      refine ⟨41749762461255312610240387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222665399793361667254615397 41749762461255312610240387)
      ·
        refine ⟨62624643691882968915360581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41749762461255312610240387 62624643691882968915360581)
        ·
          refine ⟨11742120692228056671630109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62624643691882968915360581 11742120692228056671630109)
          ·
            refine ⟨4403295259585521251861291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11742120692228056671630109 4403295259585521251861291)
            ·
              refine ⟨6604942889378281877791937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403295259585521251861291 6604942889378281877791937)
              ·
                refine ⟨4953707167033711408343953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6604942889378281877791937 4953707167033711408343953)
                ·
                  refine ⟨3715280375275283556257965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953707167033711408343953 3715280375275283556257965)
                  ·
                    refine ⟨1393230140728231333596737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715280375275283556257965 1393230140728231333596737)
                    ·
                      rfl

theorem cell22_4069959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_4069959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069959 prefixEnd_4069959 := by exact prefixLift 4069959
  have htrace : WordTrace (prefixWord ++ tailWord_4069959) baseStart_4069959 baseEnd_4069959 := by
    simpa [prefixWord, tailWord_4069959, baseEnd_4069959] using wordTrace_append hprefix tailTrace_4069959
  have hstable : (prefixWord ++ tailWord_4069959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069959).length < 2 ^ (prefixWord ++ tailWord_4069959).sum := by decide
  have hdescent : baseEnd_4069959 < baseStart_4069959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069968 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_4069968 : Nat := 118140960795 + 4069968 * 2 ^ 59
def prefixEnd_4069968 : Nat := 4983230072969 + 3 ^ 40 * 4069968 * 2
def baseEnd_4069968 : Nat := 1393233221612158310121709

theorem tailTrace_4069968 : CollatzResearch.WordTrace tailWord_4069968 prefixEnd_4069968 1393233221612158310121709 := by
  unfold tailWord_4069968
  simp only [CollatzResearch.WordTrace]
  refine ⟨74221964059604253020077279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98962618746139004026769705 74221964059604253020077279)
  ·
    refine ⟨111332946089406379530115919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74221964059604253020077279 111332946089406379530115919)
    ·
      refine ⟨166999419134109569295173879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111332946089406379530115919 166999419134109569295173879)
      ·
        refine ⟨250499128701164353942760819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166999419134109569295173879 250499128701164353942760819)
        ·
          refine ⟨375748693051746530914141229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250499128701164353942760819 375748693051746530914141229)
          ·
            refine ⟨140905759894404949092802961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375748693051746530914141229 140905759894404949092802961)
            ·
              refine ⟨105679319920803711819602221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140905759894404949092802961 105679319920803711819602221)
              ·
                refine ⟨39629744970301391932350833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105679319920803711819602221 39629744970301391932350833)
                ·
                  refine ⟨29722308727726043949263125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39629744970301391932350833 29722308727726043949263125)
                  ·
                    refine ⟨1393233221612158310121709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29722308727726043949263125 1393233221612158310121709)
                    ·
                      rfl

theorem cell22_4069968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_4069968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069968 prefixEnd_4069968 := by exact prefixLift 4069968
  have htrace : WordTrace (prefixWord ++ tailWord_4069968) baseStart_4069968 baseEnd_4069968 := by
    simpa [prefixWord, tailWord_4069968, baseEnd_4069968] using wordTrace_append hprefix tailTrace_4069968
  have hstable : (prefixWord ++ tailWord_4069968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069968).length < 2 ^ (prefixWord ++ tailWord_4069968).sum := by decide
  have hdescent : baseEnd_4069968 < baseStart_4069968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4069989 : List Nat := [1, 3, 1, 3, 5, 1, 2, 6]
def baseStart_4069989 : Nat := 118140960795 + 4069989 * 2 ^ 59
def prefixEnd_4069989 : Nat := 4983230072969 + 3 ^ 40 * 4069989 * 2
def baseEnd_4069989 : Nat := 154804490037924583927405

theorem tailTrace_4069989 : CollatzResearch.WordTrace tailWord_4069989 prefixEnd_4069989 154804490037924583927405 := by
  unfold tailWord_4069989
  simp only [CollatzResearch.WordTrace]
  refine ⟨148444694052132426626669021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98963129368088284417779347 148444694052132426626669021)
  ·
    refine ⟨55666760269549659985000883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148444694052132426626669021 55666760269549659985000883)
    ·
      refine ⟨83500140404324489977501325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55666760269549659985000883 83500140404324489977501325)
      ·
        refine ⟨31312552651621683741562997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83500140404324489977501325 31312552651621683741562997)
        ·
          refine ⟨2935551811089532850771531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31312552651621683741562997 2935551811089532850771531)
          ·
            refine ⟨4403327716634299276157297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935551811089532850771531 4403327716634299276157297)
            ·
              refine ⟨3302495787475724457117973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403327716634299276157297 3302495787475724457117973)
              ·
                refine ⟨154804490037924583927405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3302495787475724457117973 154804490037924583927405)
                ·
                  rfl

theorem cell22_4069989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 6].length) (baseStart_4069989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4069989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4069989 prefixEnd_4069989 := by exact prefixLift 4069989
  have htrace : WordTrace (prefixWord ++ tailWord_4069989) baseStart_4069989 baseEnd_4069989 := by
    simpa [prefixWord, tailWord_4069989, baseEnd_4069989] using wordTrace_append hprefix tailTrace_4069989
  have hstable : (prefixWord ++ tailWord_4069989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4069989).length < 2 ^ (prefixWord ++ tailWord_4069989).sum := by decide
  have hdescent : baseEnd_4069989 < baseStart_4069989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4069989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070021 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_4070021 : Nat := 118140960795 + 4070021 * 2 ^ 59
def prefixEnd_4070021 : Nat := 4983230072969 + 3 ^ 40 * 4070021 * 2
def baseEnd_4070021 : Nat := 1393251364595283838546547

theorem tailTrace_4070021 : CollatzResearch.WordTrace tailWord_4070021 prefixEnd_4070021 1393251364595283838546547 := by
  unfold tailWord_4070021
  simp only [CollatzResearch.WordTrace]
  refine ⟨148445861188016496091833917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98963907458677664061222611 148445861188016496091833917)
  ·
    refine ⟨55667197945506186034437719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148445861188016496091833917 55667197945506186034437719)
    ·
      refine ⟨83500796918259279051656579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55667197945506186034437719 83500796918259279051656579)
      ·
        refine ⟨125251195377388918577484869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83500796918259279051656579 125251195377388918577484869)
        ·
          refine ⟨23484599133260422233278413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125251195377388918577484869 23484599133260422233278413)
          ·
            refine ⟨8806724674972658337479405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23484599133260422233278413 8806724674972658337479405)
            ·
              refine ⟨3302521753114746876554777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8806724674972658337479405 3302521753114746876554777)
              ·
                refine ⟨2476891314836060157416083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302521753114746876554777 2476891314836060157416083)
                ·
                  refine ⟨3715336972254090236124125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476891314836060157416083 3715336972254090236124125)
                  ·
                    refine ⟨1393251364595283838546547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715336972254090236124125 1393251364595283838546547)
                    ·
                      rfl

theorem cell22_4070021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_4070021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070021 prefixEnd_4070021 := by exact prefixLift 4070021
  have htrace : WordTrace (prefixWord ++ tailWord_4070021) baseStart_4070021 baseEnd_4070021 := by
    simpa [prefixWord, tailWord_4070021, baseEnd_4070021] using wordTrace_append hprefix tailTrace_4070021
  have hstable : (prefixWord ++ tailWord_4070021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070021).length < 2 ^ (prefixWord ++ tailWord_4070021).sum := by decide
  have hdescent : baseEnd_4070021 < baseStart_4070021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070034 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_4070034 : Nat := 118140960795 + 4070034 * 2 ^ 59
def prefixEnd_4070034 : Nat := 4983230072969 + 3 ^ 40 * 4070034 * 2
def baseEnd_4070034 : Nat := 464418604920318712657169

theorem tailTrace_4070034 : CollatzResearch.WordTrace tailWord_4070034 prefixEnd_4070034 464418604920318712657169 := by
  unfold tailWord_4070034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111583834242349828014289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98964223557979599541371437 37111583834242349828014289)
  ·
    refine ⟨27833687875681762371010717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37111583834242349828014289 27833687875681762371010717)
    ·
      refine ⟨10437632953380660889129019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27833687875681762371010717 10437632953380660889129019)
      ·
        refine ⟨15656449430070991333693529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437632953380660889129019 15656449430070991333693529)
        ·
          refine ⟨11742337072553243500270147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15656449430070991333693529 11742337072553243500270147)
          ·
            refine ⟨17613505608829865250405221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742337072553243500270147 17613505608829865250405221)
            ·
              refine ⟨3302532301655599734450979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17613505608829865250405221 3302532301655599734450979)
              ·
                refine ⟨4953798452483399601676469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302532301655599734450979 4953798452483399601676469)
                ·
                  refine ⟨464418604920318712657169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4953798452483399601676469 464418604920318712657169)
                  ·
                    rfl

theorem cell22_4070034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_4070034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070034 prefixEnd_4070034 := by exact prefixLift 4070034
  have htrace : WordTrace (prefixWord ++ tailWord_4070034) baseStart_4070034 baseEnd_4070034 := by
    simpa [prefixWord, tailWord_4070034, baseEnd_4070034] using wordTrace_append hprefix tailTrace_4070034
  have hstable : (prefixWord ++ tailWord_4070034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070034).length < 2 ^ (prefixWord ++ tailWord_4070034).sum := by decide
  have hdescent : baseEnd_4070034 < baseStart_4070034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070045 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 6]
def baseStart_4070045 : Nat := 118140960795 + 4070045 * 2 ^ 59
def prefixEnd_4070045 : Nat := 4983230072969 + 3 ^ 40 * 4070045 * 2
def baseEnd_4070045 : Nat := 464419860095251925315491

theorem tailTrace_4070045 : CollatzResearch.WordTrace tailWord_4070045 prefixEnd_4070045 464419860095251925315491 := by
  unfold tailWord_4070045
  simp only [CollatzResearch.WordTrace]
  refine ⟨148446736539929548190707589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98964491026619698793805059 148446736539929548190707589)
  ·
    refine ⟨27833763101236790285757673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148446736539929548190707589 27833763101236790285757673)
    ·
      refine ⟨20875322325927592714318255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27833763101236790285757673 20875322325927592714318255)
      ·
        refine ⟨31312983488891389071477383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20875322325927592714318255 31312983488891389071477383)
        ·
          refine ⟨46969475233337083607216075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31312983488891389071477383 46969475233337083607216075)
          ·
            refine ⟨70454212850005625410824113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46969475233337083607216075 70454212850005625410824113)
            ·
              refine ⟨52840659637504219058118085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70454212850005625410824113 52840659637504219058118085)
              ·
                refine ⟨9907623682032041073397141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52840659637504219058118085 9907623682032041073397141)
                ·
                  refine ⟨464419860095251925315491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9907623682032041073397141 464419860095251925315491)
                  ·
                    rfl

theorem cell22_4070045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_4070045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070045 prefixEnd_4070045 := by exact prefixLift 4070045
  have htrace : WordTrace (prefixWord ++ tailWord_4070045) baseStart_4070045 baseEnd_4070045 := by
    simpa [prefixWord, tailWord_4070045, baseEnd_4070045] using wordTrace_append hprefix tailTrace_4070045
  have hstable : (prefixWord ++ tailWord_4070045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070045).length < 2 ^ (prefixWord ++ tailWord_4070045).sum := by decide
  have hdescent : baseEnd_4070045 < baseStart_4070045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070079 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 4]
def baseStart_4070079 : Nat := 118140960795 + 4070079 * 2 ^ 59
def prefixEnd_4070079 : Nat := 4983230072969 + 3 ^ 40 * 4070079 * 2
def baseEnd_4070079 : Nat := 464423739726863673532123

theorem tailTrace_4070079 : CollatzResearch.WordTrace tailWord_4070079 prefixEnd_4070079 464423739726863673532123 := by
  unfold tailWord_4070079
  simp only [CollatzResearch.WordTrace]
  refine ⟨148447976621806371997445291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98965317747870914664963527 148447976621806371997445291)
  ·
    refine ⟨222671964932709557996167937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148447976621806371997445291 222671964932709557996167937)
    ·
      refine ⟨167003973699532168497125953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222671964932709557996167937 167003973699532168497125953)
      ·
        refine ⟨125252980274649126372844465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167003973699532168497125953 125252980274649126372844465)
        ·
          refine ⟨93939735205986844779633349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125252980274649126372844465 93939735205986844779633349)
          ·
            refine ⟨17613700351122533396181253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93939735205986844779633349 17613700351122533396181253)
            ·
              refine ⟨3302568815835475011783985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17613700351122533396181253 3302568815835475011783985)
              ·
                refine ⟨2476926611876606258837989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302568815835475011783985 2476926611876606258837989)
                ·
                  refine ⟨464423739726863673532123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2476926611876606258837989 464423739726863673532123)
                  ·
                    rfl

theorem cell22_4070079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 4].length) (baseStart_4070079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070079 prefixEnd_4070079 := by exact prefixLift 4070079
  have htrace : WordTrace (prefixWord ++ tailWord_4070079) baseStart_4070079 baseEnd_4070079 := by
    simpa [prefixWord, tailWord_4070079, baseEnd_4070079] using wordTrace_append hprefix tailTrace_4070079
  have hstable : (prefixWord ++ tailWord_4070079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070079).length < 2 ^ (prefixWord ++ tailWord_4070079).sum := by decide
  have hdescent : baseEnd_4070079 < baseStart_4070079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070094 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_4070094 : Nat := 118140960795 + 4070094 * 2 ^ 59
def prefixEnd_4070094 : Nat := 4983230072969 + 3 ^ 40 * 4070094 * 2
def baseEnd_4070094 : Nat := 1393276353987135981471323

theorem tailTrace_4070094 : CollatzResearch.WordTrace tailWord_4070094 prefixEnd_4070094 1393276353987135981471323 := by
  unfold tailWord_4070094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18556065464594003694905167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98965682477834686372827557 18556065464594003694905167)
  ·
    refine ⟨27834098196891005542357751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18556065464594003694905167 27834098196891005542357751)
    ·
      refine ⟨41751147295336508313536627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27834098196891005542357751 41751147295336508313536627)
      ·
        refine ⟨62626720943004762470304941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41751147295336508313536627 62626720943004762470304941)
        ·
          refine ⟨23485020353626785926364353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62626720943004762470304941 23485020353626785926364353)
          ·
            refine ⟨17613765265220089444773265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23485020353626785926364353 17613765265220089444773265)
            ·
              refine ⟨13210323948915067083579949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17613765265220089444773265 13210323948915067083579949)
              ·
                refine ⟨4953871480843150156342481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13210323948915067083579949 4953871480843150156342481)
                ·
                  refine ⟨3715403610632362617256861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953871480843150156342481 3715403610632362617256861)
                  ·
                    refine ⟨1393276353987135981471323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715403610632362617256861 1393276353987135981471323)
                    ·
                      rfl

theorem cell22_4070094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_4070094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070094 prefixEnd_4070094 := by exact prefixLift 4070094
  have htrace : WordTrace (prefixWord ++ tailWord_4070094) baseStart_4070094 baseEnd_4070094 := by
    simpa [prefixWord, tailWord_4070094, baseEnd_4070094] using wordTrace_append hprefix tailTrace_4070094
  have hstable : (prefixWord ++ tailWord_4070094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070094).length < 2 ^ (prefixWord ++ tailWord_4070094).sum := by decide
  have hdescent : baseEnd_4070094 < baseStart_4070094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070122 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_4070122 : Nat := 118140960795 + 4070122 * 2 ^ 59
def prefixEnd_4070122 : Nat := 4983230072969 + 3 ^ 40 * 4070122 * 2
def baseEnd_4070122 : Nat := 1393285938959353241771237

theorem tailTrace_4070122 : CollatzResearch.WordTrace tailWord_4070122 prefixEnd_4070122 1393285938959353241771237 := by
  unfold tailWord_4070122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37112386240162647585315155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98966363307100393560840413 37112386240162647585315155)
  ·
    refine ⟨55668579360243971377972733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37112386240162647585315155 55668579360243971377972733)
    ·
      refine ⟨20875717260091489266739775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55668579360243971377972733 20875717260091489266739775)
      ·
        refine ⟨31313575890137233900109663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20875717260091489266739775 31313575890137233900109663)
        ·
          refine ⟨46970363835205850850164495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31313575890137233900109663 46970363835205850850164495)
          ·
            refine ⟨70455545752808776275246743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46970363835205850850164495 70455545752808776275246743)
            ·
              refine ⟨105683318629213164412870115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70455545752808776275246743 105683318629213164412870115)
              ·
                refine ⟨158524977943819746619305173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105683318629213164412870115 158524977943819746619305173)
                ·
                  refine ⟨3715429170558275311389965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 158524977943819746619305173 3715429170558275311389965)
                  ·
                    refine ⟨1393285938959353241771237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715429170558275311389965 1393285938959353241771237)
                    ·
                      rfl

theorem cell22_4070122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_4070122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070122 prefixEnd_4070122 := by exact prefixLift 4070122
  have htrace : WordTrace (prefixWord ++ tailWord_4070122) baseStart_4070122 baseEnd_4070122 := by
    simpa [prefixWord, tailWord_4070122, baseEnd_4070122] using wordTrace_append hprefix tailTrace_4070122
  have hstable : (prefixWord ++ tailWord_4070122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070122).length < 2 ^ (prefixWord ++ tailWord_4070122).sum := by decide
  have hdescent : baseEnd_4070122 < baseStart_4070122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070190 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4070190 : Nat := 118140960795 + 4070190 * 2 ^ 59
def prefixEnd_4070190 : Nat := 4983230072969 + 3 ^ 40 * 4070190 * 2
def baseEnd_4070190 : Nat := 1393309216749023731071029

theorem tailTrace_4070190 : CollatzResearch.WordTrace tailWord_4070190 prefixEnd_4070190 1393309216749023731071029 := by
  unfold tailWord_4070190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18556503140550529744342003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98968016749602825303157349 18556503140550529744342003)
  ·
    refine ⟨27834754710825794616513005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18556503140550529744342003 27834754710825794616513005)
    ·
      refine ⟨10438033016559672981192377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27834754710825794616513005 10438033016559672981192377)
      ·
        refine ⟨7828524762419754735894283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10438033016559672981192377 7828524762419754735894283)
        ·
          refine ⟨11742787143629632103841425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828524762419754735894283 11742787143629632103841425)
          ·
            refine ⟨8807090357722224077881069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11742787143629632103841425 8807090357722224077881069)
            ·
              refine ⟨3302658884145834029205401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8807090357722224077881069 3302658884145834029205401)
              ·
                refine ⟨2476994163109375521904051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302658884145834029205401 2476994163109375521904051)
                ·
                  refine ⟨3715491244664063282856077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476994163109375521904051 3715491244664063282856077)
                  ·
                    refine ⟨1393309216749023731071029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715491244664063282856077 1393309216749023731071029)
                    ·
                      rfl

theorem cell22_4070190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4070190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070190 prefixEnd_4070190 := by exact prefixLift 4070190
  have htrace : WordTrace (prefixWord ++ tailWord_4070190) baseStart_4070190 baseEnd_4070190 := by
    simpa [prefixWord, tailWord_4070190, baseEnd_4070190] using wordTrace_append hprefix tailTrace_4070190
  have hstable : (prefixWord ++ tailWord_4070190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070190).length < 2 ^ (prefixWord ++ tailWord_4070190).sum := by decide
  have hdescent : baseEnd_4070190 < baseStart_4070190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070242 : List Nat := [3, 3, 2, 1, 13]
def baseStart_4070242 : Nat := 118140960795 + 4070242 * 2 ^ 59
def prefixEnd_4070242 : Nat := 4983230072969 + 3 ^ 40 * 4070242 * 2
def baseEnd_4070242 : Nat := 5733856038731328924983

theorem tailTrace_4070242 : CollatzResearch.WordTrace tailWord_4070242 prefixEnd_4070242 5733856038731328924983 := by
  unfold tailWord_4070242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37113480430053962708907245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98969281146810567223752653 37113480430053962708907245)
  ·
    refine ⟨13917555161270236015840217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37113480430053962708907245 13917555161270236015840217)
    ·
      refine ⟨10438166370952677011880163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13917555161270236015840217 10438166370952677011880163)
      ·
        refine ⟨15657249556429015517820245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10438166370952677011880163 15657249556429015517820245)
        ·
          refine ⟨5733856038731328924983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15657249556429015517820245 5733856038731328924983)
          ·
            rfl

theorem cell22_4070242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 13].length) (baseStart_4070242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070242 prefixEnd_4070242 := by exact prefixLift 4070242
  have htrace : WordTrace (prefixWord ++ tailWord_4070242) baseStart_4070242 baseEnd_4070242 := by
    simpa [prefixWord, tailWord_4070242, baseEnd_4070242] using wordTrace_append hprefix tailTrace_4070242
  have hstable : (prefixWord ++ tailWord_4070242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070242).length < 2 ^ (prefixWord ++ tailWord_4070242).sum := by decide
  have hdescent : baseEnd_4070242 < baseStart_4070242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070244 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_4070244 : Nat := 118140960795 + 4070244 * 2 ^ 59
def prefixEnd_4070244 : Nat := 4983230072969 + 3 ^ 40 * 4070244 * 2
def baseEnd_4070244 : Nat := 1393327702052585590220863

theorem tailTrace_4070244 : CollatzResearch.WordTrace tailWord_4070244 prefixEnd_4070244 1393327702052585590220863 := by
  unfold tailWord_4070244
  simp only [CollatzResearch.WordTrace]
  refine ⟨74226997333104302588600893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98969329777472403451467857 74226997333104302588600893)
  ·
    refine ⟨27835123999914113470725335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74226997333104302588600893 27835123999914113470725335)
    ·
      refine ⟨41752685999871170206088003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27835123999914113470725335 41752685999871170206088003)
      ·
        refine ⟨62629028999806755309132005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41752685999871170206088003 62629028999806755309132005)
        ·
          refine ⟨11742942937463766620462251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62629028999806755309132005 11742942937463766620462251)
          ·
            refine ⟨17614414406195649930693377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742942937463766620462251 17614414406195649930693377)
            ·
              refine ⟨13210810804646737448020033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17614414406195649930693377 13210810804646737448020033)
              ·
                refine ⟨9908108103485053086015025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13210810804646737448020033 9908108103485053086015025)
                ·
                  refine ⟨7431081077613789814511269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908108103485053086015025 7431081077613789814511269)
                  ·
                    refine ⟨1393327702052585590220863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431081077613789814511269 1393327702052585590220863)
                    ·
                      rfl

theorem cell22_4070244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_4070244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070244 prefixEnd_4070244 := by exact prefixLift 4070244
  have htrace : WordTrace (prefixWord ++ tailWord_4070244) baseStart_4070244 baseEnd_4070244 := by
    simpa [prefixWord, tailWord_4070244, baseEnd_4070244] using wordTrace_append hprefix tailTrace_4070244
  have hstable : (prefixWord ++ tailWord_4070244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070244).length < 2 ^ (prefixWord ++ tailWord_4070244).sum := by decide
  have hdescent : baseEnd_4070244 < baseStart_4070244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070248 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_4070248 : Nat := 118140960795 + 4070248 * 2 ^ 59
def prefixEnd_4070248 : Nat := 4983230072969 + 3 ^ 40 * 4070248 * 2
def baseEnd_4070248 : Nat := 464443023778110304373617

theorem tailTrace_4070248 : CollatzResearch.WordTrace tailWord_4070248 prefixEnd_4070248 464443023778110304373617 := by
  unfold tailWord_4070248
  simp only [CollatzResearch.WordTrace]
  refine ⟨74227070279097056930173699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98969427038796075906898265 74227070279097056930173699)
  ·
    refine ⟨111340605418645585395260549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74227070279097056930173699 111340605418645585395260549)
    ·
      refine ⟨20876363515996047261611353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111340605418645585395260549 20876363515996047261611353)
      ·
        refine ⟨15657272636997035446208515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20876363515996047261611353 15657272636997035446208515)
        ·
          refine ⟨23485908955495553169312773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15657272636997035446208515 23485908955495553169312773)
          ·
            refine ⟨4403607929155416219246145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23485908955495553169312773 4403607929155416219246145)
            ·
              refine ⟨3302705946866562164434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403607929155416219246145 3302705946866562164434609)
              ·
                refine ⟨2477029460149921623325957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302705946866562164434609 2477029460149921623325957)
                ·
                  refine ⟨464443023778110304373617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477029460149921623325957 464443023778110304373617)
                  ·
                    rfl

theorem cell22_4070248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_4070248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070248 prefixEnd_4070248 := by exact prefixLift 4070248
  have htrace : WordTrace (prefixWord ++ tailWord_4070248) baseStart_4070248 baseEnd_4070248 := by
    simpa [prefixWord, tailWord_4070248, baseEnd_4070248] using wordTrace_append hprefix tailTrace_4070248
  have hstable : (prefixWord ++ tailWord_4070248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070248).length < 2 ^ (prefixWord ++ tailWord_4070248).sum := by decide
  have hdescent : baseEnd_4070248 < baseStart_4070248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070304 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_4070304 : Nat := 118140960795 + 4070304 * 2 ^ 59
def prefixEnd_4070304 : Nat := 4983230072969 + 3 ^ 40 * 4070304 * 2
def baseEnd_4070304 : Nat := 464449413759588477906893

theorem tailTrace_4070304 : CollatzResearch.WordTrace tailWord_4070304 prefixEnd_4070304 464449413759588477906893 := by
  unfold tailWord_4070304
  simp only [CollatzResearch.WordTrace]
  refine ⟨74228091522995617712192983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98970788697327490282923977 74228091522995617712192983)
  ·
    refine ⟨111342137284493426568289475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74228091522995617712192983 111342137284493426568289475)
    ·
      refine ⟨167013205926740139852434213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111342137284493426568289475 167013205926740139852434213)
      ·
        refine ⟨31314976111263776222331415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167013205926740139852434213 31314976111263776222331415)
        ·
          refine ⟨46972464166895664333497123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31314976111263776222331415 46972464166895664333497123)
          ·
            refine ⟨70458696250343496500245685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46972464166895664333497123 70458696250343496500245685)
            ·
              refine ⟨6605502773469702796898033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70458696250343496500245685 6605502773469702796898033)
              ·
                refine ⟨4954127080102277097673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6605502773469702796898033 4954127080102277097673525)
                ·
                  refine ⟨464449413759588477906893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954127080102277097673525 464449413759588477906893)
                  ·
                    rfl

theorem cell22_4070304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_4070304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070304 prefixEnd_4070304 := by exact prefixLift 4070304
  have htrace : WordTrace (prefixWord ++ tailWord_4070304) baseStart_4070304 baseEnd_4070304 := by
    simpa [prefixWord, tailWord_4070304, baseEnd_4070304] using wordTrace_append hprefix tailTrace_4070304
  have hstable : (prefixWord ++ tailWord_4070304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070304).length < 2 ^ (prefixWord ++ tailWord_4070304).sum := by decide
  have hdescent : baseEnd_4070304 < baseStart_4070304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070396 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4070396 : Nat := 118140960795 + 4070396 * 2 ^ 59
def prefixEnd_4070396 : Nat := 4983230072969 + 3 ^ 40 * 4070396 * 2
def baseEnd_4070396 : Nat := 1393379734758907860420397

theorem tailTrace_4070396 : CollatzResearch.WordTrace tailWord_4070396 prefixEnd_4070396 1393379734758907860420397 := by
  unfold tailWord_4070396
  simp only [CollatzResearch.WordTrace]
  refine ⟨74229769280828967568367521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98973025707771956757823361 74229769280828967568367521)
  ·
    refine ⟨55672326960621725676275641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74229769280828967568367521 55672326960621725676275641)
    ·
      refine ⟨41754245220466294257206731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55672326960621725676275641 41754245220466294257206731)
      ·
        refine ⟨62631367830699441385810097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41754245220466294257206731 62631367830699441385810097)
        ·
          refine ⟨46973525873024581039357573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62631367830699441385810097 46973525873024581039357573)
          ·
            refine ⟨8807536101192108944879545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46973525873024581039357573 8807536101192108944879545)
            ·
              refine ⟨6605652075894081708659659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807536101192108944879545 6605652075894081708659659)
              ·
                refine ⟨9908478113841122562989489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6605652075894081708659659 9908478113841122562989489)
                ·
                  refine ⟨7431358585380841922242117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908478113841122562989489 7431358585380841922242117)
                  ·
                    refine ⟨1393379734758907860420397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431358585380841922242117 1393379734758907860420397)
                    ·
                      rfl

theorem cell22_4070396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4070396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070396 prefixEnd_4070396 := by exact prefixLift 4070396
  have htrace : WordTrace (prefixWord ++ tailWord_4070396) baseStart_4070396 baseEnd_4070396 := by
    simpa [prefixWord, tailWord_4070396, baseEnd_4070396] using wordTrace_append hprefix tailTrace_4070396
  have hstable : (prefixWord ++ tailWord_4070396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070396).length < 2 ^ (prefixWord ++ tailWord_4070396).sum := by decide
  have hdescent : baseEnd_4070396 < baseStart_4070396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070398 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4070398 : Nat := 118140960795 + 4070398 * 2 ^ 59
def prefixEnd_4070398 : Nat := 4983230072969 + 3 ^ 40 * 4070398 * 2
def baseEnd_4070398 : Nat := 1393380419399780521870391

theorem tailTrace_4070398 : CollatzResearch.WordTrace tailWord_4070398 prefixEnd_4070398 1393380419399780521870391 := by
  unfold tailWord_4070398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557451438456336184788481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98973074338433792985538565 18557451438456336184788481)
  ·
    refine ⟨13918088578842252138591361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18557451438456336184788481 13918088578842252138591361)
    ·
      refine ⟨10438566434131689103943521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13918088578842252138591361 10438566434131689103943521)
      ·
        refine ⟨7828924825598766827957641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10438566434131689103943521 7828924825598766827957641)
        ·
          refine ⟨5871693619199075120968231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7828924825598766827957641 5871693619199075120968231)
          ·
            refine ⟨8807540428798612681452347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871693619199075120968231 8807540428798612681452347)
            ·
              refine ⟨13211310643197919022178521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807540428798612681452347 13211310643197919022178521)
              ·
                refine ⟨9908482982398439266633891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211310643197919022178521 9908482982398439266633891)
                ·
                  refine ⟨14862724473597658899950837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908482982398439266633891 14862724473597658899950837)
                  ·
                    refine ⟨1393380419399780521870391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14862724473597658899950837 1393380419399780521870391)
                    ·
                      rfl

theorem cell22_4070398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4070398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070398 prefixEnd_4070398 := by exact prefixLift 4070398
  have htrace : WordTrace (prefixWord ++ tailWord_4070398) baseStart_4070398 baseEnd_4070398 := by
    simpa [prefixWord, tailWord_4070398, baseEnd_4070398] using wordTrace_append hprefix tailTrace_4070398
  have hstable : (prefixWord ++ tailWord_4070398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070398).length < 2 ^ (prefixWord ++ tailWord_4070398).sum := by decide
  have hdescent : baseEnd_4070398 < baseStart_4070398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070402 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4070402 : Nat := 118140960795 + 4070402 * 2 ^ 59
def prefixEnd_4070402 : Nat := 4983230072969 + 3 ^ 40 * 4070402 * 2
def baseEnd_4070402 : Nat := 1393381788681525844770379

theorem tailTrace_4070402 : CollatzResearch.WordTrace tailWord_4070402 prefixEnd_4070402 1393381788681525844770379 := by
  unfold tailWord_4070402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37114939349909049540363365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98973171599757465440968973 37114939349909049540363365)
  ·
    refine ⟨6959051128107946788818131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37114939349909049540363365 6959051128107946788818131)
    ·
      refine ⟨10438576692161920183227197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6959051128107946788818131 10438576692161920183227197)
      ·
        refine ⟨3914466259560720068710199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10438576692161920183227197 3914466259560720068710199)
        ·
          refine ⟨5871699389341080103065299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914466259560720068710199 5871699389341080103065299)
          ·
            refine ⟨8807549084011620154597949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871699389341080103065299 8807549084011620154597949)
            ·
              refine ⟨3302830906504357557974231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8807549084011620154597949 3302830906504357557974231)
              ·
                refine ⟨4954246359756536336961347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3302830906504357557974231 4954246359756536336961347)
                ·
                  refine ⟨7431369539634804505442021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954246359756536336961347 7431369539634804505442021)
                  ·
                    refine ⟨1393381788681525844770379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431369539634804505442021 1393381788681525844770379)
                    ·
                      rfl

theorem cell22_4070402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4070402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070402 prefixEnd_4070402 := by exact prefixLift 4070402
  have htrace : WordTrace (prefixWord ++ tailWord_4070402) baseStart_4070402 baseEnd_4070402 := by
    simpa [prefixWord, tailWord_4070402, baseEnd_4070402] using wordTrace_append hprefix tailTrace_4070402
  have hstable : (prefixWord ++ tailWord_4070402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070402).length < 2 ^ (prefixWord ++ tailWord_4070402).sum := by decide
  have hdescent : baseEnd_4070402 < baseStart_4070402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070424 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_4070424 : Nat := 118140960795 + 4070424 * 2 ^ 59
def prefixEnd_4070424 : Nat := 4983230072969 + 3 ^ 40 * 4070424 * 2
def baseEnd_4070424 : Nat := 1393389319731125120720311

theorem tailTrace_4070424 : CollatzResearch.WordTrace tailWord_4070424 prefixEnd_4070424 1393389319731125120720311 := by
  unfold tailWord_4070424
  simp only [CollatzResearch.WordTrace]
  refine ⟨74230279902778247959377163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98973706537037663945836217 74230279902778247959377163)
  ·
    refine ⟨111345419854167371939065745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74230279902778247959377163 111345419854167371939065745)
    ·
      refine ⟨83509064890625528954299309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111345419854167371939065745 83509064890625528954299309)
      ·
        refine ⟨31315899333984573357862241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83509064890625528954299309 31315899333984573357862241)
        ·
          refine ⟨23486924500488430018396681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31315899333984573357862241 23486924500488430018396681)
          ·
            refine ⟨17615193375366322513797511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23486924500488430018396681 17615193375366322513797511)
            ·
              refine ⟨26422790063049483770696267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17615193375366322513797511 26422790063049483770696267)
              ·
                refine ⟨39634185094574225656044401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26422790063049483770696267 39634185094574225656044401)
                ·
                  refine ⟨29725638820930669242033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39634185094574225656044401 29725638820930669242033301)
                  ·
                    refine ⟨1393389319731125120720311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29725638820930669242033301 1393389319731125120720311)
                    ·
                      rfl

theorem cell22_4070424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_4070424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070424 prefixEnd_4070424 := by exact prefixLift 4070424
  have htrace : WordTrace (prefixWord ++ tailWord_4070424) baseStart_4070424 baseEnd_4070424 := by
    simpa [prefixWord, tailWord_4070424, baseEnd_4070424] using wordTrace_append hprefix tailTrace_4070424
  have hstable : (prefixWord ++ tailWord_4070424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070424).length < 2 ^ (prefixWord ++ tailWord_4070424).sum := by decide
  have hdescent : baseEnd_4070424 < baseStart_4070424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070426 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_4070426 : Nat := 118140960795 + 4070426 * 2 ^ 59
def prefixEnd_4070426 : Nat := 4983230072969 + 3 ^ 40 * 4070426 * 2
def baseEnd_4070426 : Nat := 1393390004371997782170305

theorem tailTrace_4070426 : CollatzResearch.WordTrace tailWord_4070426 prefixEnd_4070426 1393390004371997782170305 := by
  unfold tailWord_4070426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37115158187887312565081783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98973755167699500173551421 37115158187887312565081783)
  ·
    refine ⟨55672737281830968847622675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37115158187887312565081783 55672737281830968847622675)
    ·
      refine ⟨83509105922746453271434013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55672737281830968847622675 83509105922746453271434013)
      ·
        refine ⟨31315914721029919976787755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83509105922746453271434013 31315914721029919976787755)
        ·
          refine ⟨46973872081544879965181633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31315914721029919976787755 46973872081544879965181633)
          ·
            refine ⟨35230404061158659973886225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46973872081544879965181633 35230404061158659973886225)
            ·
              refine ⟨26422803045868994980414669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35230404061158659973886225 26422803045868994980414669)
              ·
                refine ⟨9908551142200873117655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26422803045868994980414669 9908551142200873117655501)
                ·
                  refine ⟨3715706678325327419120813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9908551142200873117655501 3715706678325327419120813)
                  ·
                    refine ⟨1393390004371997782170305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715706678325327419120813 1393390004371997782170305)
                    ·
                      rfl

theorem cell22_4070426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_4070426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070426 prefixEnd_4070426 := by exact prefixLift 4070426
  have htrace : WordTrace (prefixWord ++ tailWord_4070426) baseStart_4070426 baseEnd_4070426 := by
    simpa [prefixWord, tailWord_4070426, baseEnd_4070426] using wordTrace_append hprefix tailTrace_4070426
  have hstable : (prefixWord ++ tailWord_4070426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070426).length < 2 ^ (prefixWord ++ tailWord_4070426).sum := by decide
  have hdescent : baseEnd_4070426 < baseStart_4070426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070428 : List Nat := [2, 2, 3, 1, 5, 1, 1, 7]
def baseStart_4070428 : Nat := 118140960795 + 4070428 * 2 ^ 59
def prefixEnd_4070428 : Nat := 4983230072969 + 3 ^ 40 * 4070428 * 2
def baseEnd_4070428 : Nat := 154821187668096715957811

theorem tailTrace_4070428 : CollatzResearch.WordTrace tailWord_4070428 prefixEnd_4070428 154821187668096715957811 := by
  unfold tailWord_4070428
  simp only [CollatzResearch.WordTrace]
  refine ⟨74230352848771002300949969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98973803798361336401266625 74230352848771002300949969)
  ·
    refine ⟨55672764636578251725712477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74230352848771002300949969 55672764636578251725712477)
    ·
      refine ⟨20877286738716844397142179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55672764636578251725712477 20877286738716844397142179)
      ·
        refine ⟨31315930108075266595713269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20877286738716844397142179 31315930108075266595713269)
        ·
          refine ⟨2935868447632056243348119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31315930108075266595713269 2935868447632056243348119)
          ·
            refine ⟨4403802671448084365022179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935868447632056243348119 4403802671448084365022179)
            ·
              refine ⟨6605704007172126547533269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4403802671448084365022179 6605704007172126547533269)
              ·
                refine ⟨154821187668096715957811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6605704007172126547533269 154821187668096715957811)
                ·
                  rfl

theorem cell22_4070428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_4070428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070428 prefixEnd_4070428 := by exact prefixLift 4070428
  have htrace : WordTrace (prefixWord ++ tailWord_4070428) baseStart_4070428 baseEnd_4070428 := by
    simpa [prefixWord, tailWord_4070428, baseEnd_4070428] using wordTrace_append hprefix tailTrace_4070428
  have hstable : (prefixWord ++ tailWord_4070428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070428).length < 2 ^ (prefixWord ++ tailWord_4070428).sum := by decide
  have hdescent : baseEnd_4070428 < baseStart_4070428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070460 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_4070460 : Nat := 118140960795 + 4070460 * 2 ^ 59
def prefixEnd_4070460 : Nat := 4983230072969 + 3 ^ 40 * 4070460 * 2
def baseEnd_4070460 : Nat := 1393401643266833026820201

theorem tailTrace_4070460 : CollatzResearch.WordTrace tailWord_4070460 prefixEnd_4070460 1393401643266833026820201 := by
  unfold tailWord_4070460
  simp only [CollatzResearch.WordTrace]
  refine ⟨74230936416713037033532417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98974581888950716044709889 74230936416713037033532417)
  ·
    refine ⟨55673202312534777775149313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74230936416713037033532417 55673202312534777775149313)
    ·
      refine ⟨41754901734401083331361985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55673202312534777775149313 41754901734401083331361985)
      ·
        refine ⟨31316176300800812498521489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41754901734401083331361985 31316176300800812498521489)
        ·
          refine ⟨23487132225600609373891117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31316176300800812498521489 23487132225600609373891117)
          ·
            refine ⟨8807674584600228515209169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23487132225600609373891117 8807674584600228515209169)
            ·
              refine ⟨6605755938450171386406877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807674584600228515209169 6605755938450171386406877)
              ·
                refine ⟨2477158476918814269902579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6605755938450171386406877 2477158476918814269902579)
                ·
                  refine ⟨3715737715378221404853869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477158476918814269902579 3715737715378221404853869)
                  ·
                    refine ⟨1393401643266833026820201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715737715378221404853869 1393401643266833026820201)
                    ·
                      rfl

theorem cell22_4070460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_4070460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070460 prefixEnd_4070460 := by exact prefixLift 4070460
  have htrace : WordTrace (prefixWord ++ tailWord_4070460) baseStart_4070460 baseEnd_4070460 := by
    simpa [prefixWord, tailWord_4070460, baseEnd_4070460] using wordTrace_append hprefix tailTrace_4070460
  have hstable : (prefixWord ++ tailWord_4070460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070460).length < 2 ^ (prefixWord ++ tailWord_4070460).sum := by decide
  have hdescent : baseEnd_4070460 < baseStart_4070460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070503 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4070503 : Nat := 118140960795 + 4070503 * 2 ^ 59
def prefixEnd_4070503 : Nat := 4983230072969 + 3 ^ 40 * 4070503 * 2
def baseEnd_4070503 : Nat := 1393416363045595247995069

theorem tailTrace_4070503 : CollatzResearch.WordTrace tailWord_4070503 prefixEnd_4070503 1393416363045595247995069 := by
  unfold tailWord_4070503
  simp only [CollatzResearch.WordTrace]
  refine ⟨148463441172270292410880163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98975627448180194940586775 148463441172270292410880163)
  ·
    refine ⟨222695161758405438616320245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148463441172270292410880163 222695161758405438616320245)
    ·
      refine ⟨20877671414850509870280023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222695161758405438616320245 20877671414850509870280023)
      ·
        refine ⟨31316507122275764805420035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20877671414850509870280023 31316507122275764805420035)
        ·
          refine ⟨46974760683413647208130053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31316507122275764805420035 46974760683413647208130053)
          ·
            refine ⟨8807767628140058851524385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46974760683413647208130053 8807767628140058851524385)
            ·
              refine ⟨6605825721105044138643289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807767628140058851524385 6605825721105044138643289)
              ·
                refine ⟨4954369290828783103982467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6605825721105044138643289 4954369290828783103982467)
                ·
                  refine ⟨7431553936243174655973701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954369290828783103982467 7431553936243174655973701)
                  ·
                    refine ⟨1393416363045595247995069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431553936243174655973701 1393416363045595247995069)
                    ·
                      rfl

theorem cell22_4070503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4070503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070503 prefixEnd_4070503 := by exact prefixLift 4070503
  have htrace : WordTrace (prefixWord ++ tailWord_4070503) baseStart_4070503 baseEnd_4070503 := by
    simpa [prefixWord, tailWord_4070503, baseEnd_4070503] using wordTrace_append hprefix tailTrace_4070503
  have hstable : (prefixWord ++ tailWord_4070503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070503).length < 2 ^ (prefixWord ++ tailWord_4070503).sum := by decide
  have hdescent : baseEnd_4070503 < baseStart_4070503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070531 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_4070531 : Nat := 118140960795 + 4070531 * 2 ^ 59
def prefixEnd_4070531 : Nat := 4983230072969 + 3 ^ 40 * 4070531 * 2
def baseEnd_4070531 : Nat := 1393425948017812508294983

theorem tailTrace_4070531 : CollatzResearch.WordTrace tailWord_4070531 prefixEnd_4070531 1393425948017812508294983 := by
  unfold tailWord_4070531
  simp only [CollatzResearch.WordTrace]
  refine ⟨148464462416168853192899447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98976308277445902128599631 148464462416168853192899447)
  ·
    refine ⟨222696693624253279789349171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148464462416168853192899447 222696693624253279789349171)
    ·
      refine ⟨334045040436379919684023757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222696693624253279789349171 334045040436379919684023757)
      ·
        refine ⟨125266890163642469881508909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334045040436379919684023757 125266890163642469881508909)
        ·
          refine ⟨46975083811365926205565841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125266890163642469881508909 46975083811365926205565841)
          ·
            refine ⟨35231312858524444654174381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46975083811365926205565841 35231312858524444654174381)
            ·
              refine ⟨13211742321946666745315393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35231312858524444654174381 13211742321946666745315393)
              ·
                refine ⟨9908806741460000058986545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211742321946666745315393 9908806741460000058986545)
                ·
                  refine ⟨7431605056095000044239909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9908806741460000058986545 7431605056095000044239909)
                  ·
                    refine ⟨1393425948017812508294983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7431605056095000044239909 1393425948017812508294983)
                    ·
                      rfl

theorem cell22_4070531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_4070531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070531 prefixEnd_4070531 := by exact prefixLift 4070531
  have htrace : WordTrace (prefixWord ++ tailWord_4070531) baseStart_4070531 baseEnd_4070531 := by
    simpa [prefixWord, tailWord_4070531, baseEnd_4070531] using wordTrace_append hprefix tailTrace_4070531
  have hstable : (prefixWord ++ tailWord_4070531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070531).length < 2 ^ (prefixWord ++ tailWord_4070531).sum := by decide
  have hdescent : baseEnd_4070531 < baseStart_4070531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070544 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_4070544 : Nat := 118140960795 + 4070544 * 2 ^ 59
def prefixEnd_4070544 : Nat := 4983230072969 + 3 ^ 40 * 4070544 * 2
def baseEnd_4070544 : Nat := 1393430398183484807719943

theorem tailTrace_4070544 : CollatzResearch.WordTrace tailWord_4070544 prefixEnd_4070544 1393430398183484807719943 := by
  unfold tailWord_4070544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74232468282560878206561343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98976624376747837608748457 74232468282560878206561343)
  ·
    refine ⟨111348702423841317309842015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74232468282560878206561343 111348702423841317309842015)
    ·
      refine ⟨167023053635761975964763023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111348702423841317309842015 167023053635761975964763023)
      ·
        refine ⟨250534580453642963947144535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167023053635761975964763023 250534580453642963947144535)
        ·
          refine ⟨375801870680464445920716803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250534580453642963947144535 375801870680464445920716803)
          ·
            refine ⟨563702806020696668881075205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375801870680464445920716803 563702806020696668881075205)
            ·
              refine ⟨105694276128880625415201601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563702806020696668881075205 105694276128880625415201601)
              ·
                refine ⟨79270707096660469061401201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105694276128880625415201601 79270707096660469061401201)
                ·
                  refine ⟨59453030322495351796050901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79270707096660469061401201 59453030322495351796050901)
                  ·
                    refine ⟨1393430398183484807719943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59453030322495351796050901 1393430398183484807719943)
                    ·
                      rfl

theorem cell22_4070544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_4070544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070544 prefixEnd_4070544 := by exact prefixLift 4070544
  have htrace : WordTrace (prefixWord ++ tailWord_4070544) baseStart_4070544 baseEnd_4070544 := by
    simpa [prefixWord, tailWord_4070544, baseEnd_4070544] using wordTrace_append hprefix tailTrace_4070544
  have hstable : (prefixWord ++ tailWord_4070544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070544).length < 2 ^ (prefixWord ++ tailWord_4070544).sum := by decide
  have hdescent : baseEnd_4070544 < baseStart_4070544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070546 : List Nat := [3, 2, 3, 1, 1, 2, 1, 9]
def baseStart_4070546 : Nat := 118140960795 + 4070546 * 2 ^ 59
def prefixEnd_4070546 : Nat := 4983230072969 + 3 ^ 40 * 4070546 * 2
def baseEnd_4070546 : Nat := 154825675869373052129993

theorem tailTrace_4070546 : CollatzResearch.WordTrace tailWord_4070546 prefixEnd_4070546 154825675869373052129993 := by
  unfold tailWord_4070546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37116252377778627688673873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98976673007409673836463661 37116252377778627688673873)
  ·
    refine ⟨27837189283333970766505405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37116252377778627688673873 27837189283333970766505405)
    ·
      refine ⟨10438945981250239037439527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27837189283333970766505405 10438945981250239037439527)
      ·
        refine ⟨15658418971875358556159291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10438945981250239037439527 15658418971875358556159291)
        ·
          refine ⟨23487628457813037834238937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15658418971875358556159291 23487628457813037834238937)
          ·
            refine ⟨17615721343359778375679203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23487628457813037834238937 17615721343359778375679203)
            ·
              refine ⟨26423582015039667563518805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17615721343359778375679203 26423582015039667563518805)
              ·
                refine ⟨154825675869373052129993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26423582015039667563518805 154825675869373052129993)
                ·
                  rfl

theorem cell22_4070546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_4070546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070546 prefixEnd_4070546 := by exact prefixLift 4070546
  have htrace : WordTrace (prefixWord ++ tailWord_4070546) baseStart_4070546 baseEnd_4070546 := by
    simpa [prefixWord, tailWord_4070546, baseEnd_4070546] using wordTrace_append hprefix tailTrace_4070546
  have hstable : (prefixWord ++ tailWord_4070546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070546).length < 2 ^ (prefixWord ++ tailWord_4070546).sum := by decide
  have hdescent : baseEnd_4070546 < baseStart_4070546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070591 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 5]
def baseStart_4070591 : Nat := 118140960795 + 4070591 * 2 ^ 59
def prefixEnd_4070591 : Nat := 4983230072969 + 3 ^ 40 * 4070591 * 2
def baseEnd_4070591 : Nat := 464482162414664117264933

theorem tailTrace_4070591 : CollatzResearch.WordTrace tailWord_4070591 prefixEnd_4070591 464482162414664117264933 := by
  unfold tailWord_4070591
  simp only [CollatzResearch.WordTrace]
  refine ⟨148466650795951483440083627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98977767197300988960055751 148466650795951483440083627)
  ·
    refine ⟨222699976193927225160125441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148466650795951483440083627 222699976193927225160125441)
    ·
      refine ⟨167024982145445418870094081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222699976193927225160125441 167024982145445418870094081)
      ·
        refine ⟨125268736609084064152570561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167024982145445418870094081 125268736609084064152570561)
        ·
          refine ⟨93951552456813048114427921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125268736609084064152570561 93951552456813048114427921)
          ·
            refine ⟨70463664342609786085820941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93951552456813048114427921 70463664342609786085820941)
            ·
              refine ⟨26423874128478669782182853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70463664342609786085820941 26423874128478669782182853)
              ·
                refine ⟨4954476399089750584159285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26423874128478669782182853 4954476399089750584159285)
                ·
                  refine ⟨464482162414664117264933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954476399089750584159285 464482162414664117264933)
                  ·
                    rfl

theorem cell22_4070591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5].length) (baseStart_4070591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070591 prefixEnd_4070591 := by exact prefixLift 4070591
  have htrace : WordTrace (prefixWord ++ tailWord_4070591) baseStart_4070591 baseEnd_4070591 := by
    simpa [prefixWord, tailWord_4070591, baseEnd_4070591] using wordTrace_append hprefix tailTrace_4070591
  have hstable : (prefixWord ++ tailWord_4070591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070591).length < 2 ^ (prefixWord ++ tailWord_4070591).sum := by decide
  have hdescent : baseEnd_4070591 < baseStart_4070591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070593 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4070593 : Nat := 118140960795 + 4070593 * 2 ^ 59
def prefixEnd_4070593 : Nat := 4983230072969 + 3 ^ 40 * 4070593 * 2
def baseEnd_4070593 : Nat := 1393447171884865013244793

theorem tailTrace_4070593 : CollatzResearch.WordTrace tailWord_4070593 prefixEnd_4070593 1393447171884865013244793 := by
  unfold tailWord_4070593
  simp only [CollatzResearch.WordTrace]
  refine ⟨148466723741944237781656433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98977815827962825187770955 148466723741944237781656433)
  ·
    refine ⟨111350042806458178336242325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148466723741944237781656433 111350042806458178336242325)
    ·
      refine ⟨5219533256552727109511359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111350042806458178336242325 5219533256552727109511359)
      ·
        refine ⟨7829299884829090664267039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219533256552727109511359 7829299884829090664267039)
        ·
          refine ⟨11743949827243635996400559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829299884829090664267039 11743949827243635996400559)
          ·
            refine ⟨17615924740865453994600839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11743949827243635996400559 17615924740865453994600839)
            ·
              refine ⟨26423887111298180991901259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17615924740865453994600839 26423887111298180991901259)
              ·
                refine ⟨39635830666947271487851889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26423887111298180991901259 39635830666947271487851889)
                ·
                  refine ⟨29726873000210453615888917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39635830666947271487851889 29726873000210453615888917)
                  ·
                    refine ⟨1393447171884865013244793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29726873000210453615888917 1393447171884865013244793)
                    ·
                      rfl

theorem cell22_4070593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4070593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070593 prefixEnd_4070593 := by exact prefixLift 4070593
  have htrace : WordTrace (prefixWord ++ tailWord_4070593) baseStart_4070593 baseEnd_4070593 := by
    simpa [prefixWord, tailWord_4070593, baseEnd_4070593] using wordTrace_append hprefix tailTrace_4070593
  have hstable : (prefixWord ++ tailWord_4070593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070593).length < 2 ^ (prefixWord ++ tailWord_4070593).sum := by decide
  have hdescent : baseEnd_4070593 < baseStart_4070593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070612 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4070612 : Nat := 118140960795 + 4070612 * 2 ^ 59
def prefixEnd_4070612 : Nat := 4983230072969 + 3 ^ 40 * 4070612 * 2
def baseEnd_4070612 : Nat := 1393453675973155297019735

theorem tailTrace_4070612 : CollatzResearch.WordTrace tailWord_4070612 prefixEnd_4070612 1393453675973155297019735 := by
  unfold tailWord_4070612
  simp only [CollatzResearch.WordTrace]
  refine ⟨74233708364437702013299045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98978277819250269351065393 74233708364437702013299045)
  ·
    refine ⟨13918820318332069127493571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74233708364437702013299045 13918820318332069127493571)
    ·
      refine ⟨20878230477498103691240357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13918820318332069127493571 20878230477498103691240357)
      ·
        refine ⟨3914668214530894442107567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20878230477498103691240357 3914668214530894442107567)
        ·
          refine ⟨5872002321796341663161351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914668214530894442107567 5872002321796341663161351)
          ·
            refine ⟨8808003482694512494742027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872002321796341663161351 8808003482694512494742027)
            ·
              refine ⟨13212005224041768742113041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808003482694512494742027 13212005224041768742113041)
              ·
                refine ⟨9909003918031326556584781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13212005224041768742113041 9909003918031326556584781)
                ·
                  refine ⟨3715876469261747458719293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9909003918031326556584781 3715876469261747458719293)
                  ·
                    refine ⟨1393453675973155297019735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715876469261747458719293 1393453675973155297019735)
                    ·
                      rfl

theorem cell22_4070612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4070612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070612 prefixEnd_4070612 := by exact prefixLift 4070612
  have htrace : WordTrace (prefixWord ++ tailWord_4070612) baseStart_4070612 baseEnd_4070612 := by
    simpa [prefixWord, tailWord_4070612, baseEnd_4070612] using wordTrace_append hprefix tailTrace_4070612
  have hstable : (prefixWord ++ tailWord_4070612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070612).length < 2 ^ (prefixWord ++ tailWord_4070612).sum := by decide
  have hdescent : baseEnd_4070612 < baseStart_4070612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070642 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_4070642 : Nat := 118140960795 + 4070642 * 2 ^ 59
def prefixEnd_4070642 : Nat := 4983230072969 + 3 ^ 40 * 4070642 * 2
def baseEnd_4070642 : Nat := 464487981862081739589881

theorem tailTrace_4070642 : CollatzResearch.WordTrace tailWord_4070642 prefixEnd_4070642 464487981862081739589881 := by
  unfold tailWord_4070642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37117127729691679787547545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98979007279177812766793453 37117127729691679787547545)
  ·
    refine ⟨27837845797268759840660659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37117127729691679787547545 27837845797268759840660659)
    ·
      refine ⟨41756768695903139760990989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27837845797268759840660659 41756768695903139760990989)
      ·
        refine ⟨15658788260963677410371621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41756768695903139760990989 15658788260963677410371621)
        ·
          refine ⟨2936022798930689514444679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15658788260963677410371621 2936022798930689514444679)
          ·
            refine ⟨4404034198396034271667019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936022798930689514444679 4404034198396034271667019)
            ·
              refine ⟨6606051297594051407500529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404034198396034271667019 6606051297594051407500529)
              ·
                refine ⟨4954538473195538555625397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606051297594051407500529 4954538473195538555625397)
                ·
                  refine ⟨464487981862081739589881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4954538473195538555625397 464487981862081739589881)
                  ·
                    rfl

theorem cell22_4070642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_4070642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070642 prefixEnd_4070642 := by exact prefixLift 4070642
  have htrace : WordTrace (prefixWord ++ tailWord_4070642) baseStart_4070642 baseEnd_4070642 := by
    simpa [prefixWord, tailWord_4070642, baseEnd_4070642] using wordTrace_append hprefix tailTrace_4070642
  have hstable : (prefixWord ++ tailWord_4070642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070642).length < 2 ^ (prefixWord ++ tailWord_4070642).sum := by decide
  have hdescent : baseEnd_4070642 < baseStart_4070642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070668 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_4070668 : Nat := 118140960795 + 4070668 * 2 ^ 59
def prefixEnd_4070668 : Nat := 4983230072969 + 3 ^ 40 * 4070668 * 2
def baseEnd_4070668 : Nat := 1393472845917589817619563

theorem tailTrace_4070668 : CollatzResearch.WordTrace tailWord_4070668 prefixEnd_4070668 1393472845917589817619563 := by
  unfold tailWord_4070668
  simp only [CollatzResearch.WordTrace]
  refine ⟨74234729608336262795318329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98979639477781683727091105 74234729608336262795318329)
  ·
    refine ⟨55676047206252197096488747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74234729608336262795318329 55676047206252197096488747)
    ·
      refine ⟨83514070809378295644733121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55676047206252197096488747 83514070809378295644733121)
      ·
        refine ⟨62635553107033721733549841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83514070809378295644733121 62635553107033721733549841)
        ·
          refine ⟨46976664830275291300162381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62635553107033721733549841 46976664830275291300162381)
          ·
            refine ⟨17616249311353234237560893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46976664830275291300162381 17616249311353234237560893)
            ·
              refine ⟨6606093491757462839085335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17616249311353234237560893 6606093491757462839085335)
              ·
                refine ⟨9909140237636194258628003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606093491757462839085335 9909140237636194258628003)
                ·
                  refine ⟨14863710356454291387942005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909140237636194258628003 14863710356454291387942005)
                  ·
                    refine ⟨1393472845917589817619563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14863710356454291387942005 1393472845917589817619563)
                    ·
                      rfl

theorem cell22_4070668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_4070668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070668 prefixEnd_4070668 := by exact prefixLift 4070668
  have htrace : WordTrace (prefixWord ++ tailWord_4070668) baseStart_4070668 baseEnd_4070668 := by
    simpa [prefixWord, tailWord_4070668, baseEnd_4070668] using wordTrace_append hprefix tailTrace_4070668
  have hstable : (prefixWord ++ tailWord_4070668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070668).length < 2 ^ (prefixWord ++ tailWord_4070668).sum := by decide
  have hdescent : baseEnd_4070668 < baseStart_4070668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070685 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4070685 : Nat := 118140960795 + 4070685 * 2 ^ 59
def prefixEnd_4070685 : Nat := 4983230072969 + 3 ^ 40 * 4070685 * 2
def baseEnd_4070685 : Nat := 1393478665365007439944511

theorem tailTrace_4070685 : CollatzResearch.WordTrace tailWord_4070685 prefixEnd_4070685 1393478665365007439944511 := by
  unfold tailWord_4070685
  simp only [CollatzResearch.WordTrace]
  refine ⟨148470079257610937494005509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98980052838407291662670339 148470079257610937494005509)
  ·
    refine ⟨27838139860802050780126033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148470079257610937494005509 27838139860802050780126033)
    ·
      refine ⟨20878604895601538085094525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27838139860802050780126033 20878604895601538085094525)
      ·
        refine ⟨7829476835850576781910447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20878604895601538085094525 7829476835850576781910447)
        ·
          refine ⟨11744215253775865172865671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829476835850576781910447 11744215253775865172865671)
          ·
            refine ⟨17616322880663797759298507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744215253775865172865671 17616322880663797759298507)
            ·
              refine ⟨26424484320995696638947761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17616322880663797759298507 26424484320995696638947761)
              ·
                refine ⟨19818363240746772479210821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26424484320995696638947761 19818363240746772479210821)
                ·
                  refine ⟨3715943107640019839852029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19818363240746772479210821 3715943107640019839852029)
                  ·
                    refine ⟨1393478665365007439944511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715943107640019839852029 1393478665365007439944511)
                    ·
                      rfl

theorem cell22_4070685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4070685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070685 prefixEnd_4070685 := by exact prefixLift 4070685
  have htrace : WordTrace (prefixWord ++ tailWord_4070685) baseStart_4070685 baseEnd_4070685 := by
    simpa [prefixWord, tailWord_4070685, baseEnd_4070685] using wordTrace_append hprefix tailTrace_4070685
  have hstable : (prefixWord ++ tailWord_4070685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070685).length < 2 ^ (prefixWord ++ tailWord_4070685).sum := by decide
  have hdescent : baseEnd_4070685 < baseStart_4070685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070687 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 4]
def baseStart_4070687 : Nat := 118140960795 + 4070687 * 2 ^ 59
def prefixEnd_4070687 : Nat := 4983230072969 + 3 ^ 40 * 4070687 * 2
def baseEnd_4070687 : Nat := 464493116668626700464835

theorem tailTrace_4070687 : CollatzResearch.WordTrace tailWord_4070687 prefixEnd_4070687 464493116668626700464835 := by
  unfold tailWord_4070687
  simp only [CollatzResearch.WordTrace]
  refine ⟨148470152203603691835578315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98980101469069127890385543 148470152203603691835578315)
  ·
    refine ⟨222705228305405537753367473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148470152203603691835578315 222705228305405537753367473)
    ·
      refine ⟨167028921229054153315025605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222705228305405537753367473 167028921229054153315025605)
      ·
        refine ⟨31317922730447653746567301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167028921229054153315025605 31317922730447653746567301)
        ·
          refine ⟨5872110511958935077481369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31317922730447653746567301 5872110511958935077481369)
          ·
            refine ⟨4404082883969201308111027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5872110511958935077481369 4404082883969201308111027)
            ·
              refine ⟨6606124325953801962166541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404082883969201308111027 6606124325953801962166541)
              ·
                refine ⟨2477296622232675735812453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6606124325953801962166541 2477296622232675735812453)
                ·
                  refine ⟨464493116668626700464835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477296622232675735812453 464493116668626700464835)
                  ·
                    rfl

theorem cell22_4070687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 4].length) (baseStart_4070687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070687 prefixEnd_4070687 := by exact prefixLift 4070687
  have htrace : WordTrace (prefixWord ++ tailWord_4070687) baseStart_4070687 baseEnd_4070687 := by
    simpa [prefixWord, tailWord_4070687, baseEnd_4070687] using wordTrace_append hprefix tailTrace_4070687
  have hstable : (prefixWord ++ tailWord_4070687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070687).length < 2 ^ (prefixWord ++ tailWord_4070687).sum := by decide
  have hdescent : baseEnd_4070687 < baseStart_4070687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070698 : List Nat := [3, 1, 4, 2, 1, 1, 10]
def baseStart_4070698 : Nat := 118140960795 + 4070698 * 2 ^ 59
def prefixEnd_4070698 : Nat := 4983230072969 + 3 ^ 40 * 4070698 * 2
def baseEnd_4070698 : Nat := 51610485760395545902573

theorem tailTrace_4070698 : CollatzResearch.WordTrace tailWord_4070698 prefixEnd_4070698 51610485760395545902573 := by
  unfold tailWord_4070698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37117638351640960178557187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98980368937709227142819165 37117638351640960178557187)
  ·
    refine ⟨55676457527461440267835781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37117638351640960178557187 55676457527461440267835781)
    ·
      refine ⟨10439335786399020050219209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55676457527461440267835781 10439335786399020050219209)
      ·
        refine ⟨7829501839799265037664407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10439335786399020050219209 7829501839799265037664407)
        ·
          refine ⟨11744252759698897556496611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829501839799265037664407 11744252759698897556496611)
          ·
            refine ⟨17616379139548346334744917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744252759698897556496611 17616379139548346334744917)
            ·
              refine ⟨51610485760395545902573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17616379139548346334744917 51610485760395545902573)
              ·
                rfl

theorem cell22_4070698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 10].length) (baseStart_4070698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070698 prefixEnd_4070698 := by exact prefixLift 4070698
  have htrace : WordTrace (prefixWord ++ tailWord_4070698) baseStart_4070698 baseEnd_4070698 := by
    simpa [prefixWord, tailWord_4070698, baseEnd_4070698] using wordTrace_append hprefix tailTrace_4070698
  have hstable : (prefixWord ++ tailWord_4070698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070698).length < 2 ^ (prefixWord ++ tailWord_4070698).sum := by decide
  have hdescent : baseEnd_4070698 < baseStart_4070698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070764 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_4070764 : Nat := 118140960795 + 4070764 * 2 ^ 59
def prefixEnd_4070764 : Nat := 4983230072969 + 3 ^ 40 * 4070764 * 2
def baseEnd_4070764 : Nat := 1393505708679477567219269

theorem tailTrace_4070764 : CollatzResearch.WordTrace tailWord_4070764 prefixEnd_4070764 1393505708679477567219269 := by
  unfold tailWord_4070764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74236480312162366993065673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98981973749549822657420897 74236480312162366993065673)
  ·
    refine ⟨55677360234121775244799255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74236480312162366993065673 55677360234121775244799255)
    ·
      refine ⟨83516040351182662867198883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55677360234121775244799255 83516040351182662867198883)
      ·
        refine ⟨125274060526773994300798325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83516040351182662867198883 125274060526773994300798325)
        ·
          refine ⟨11744443174385061965699843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125274060526773994300798325 11744443174385061965699843)
          ·
            refine ⟨17616664761577592948549765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11744443174385061965699843 17616664761577592948549765)
            ·
              refine ⟨3303124642795798677853081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17616664761577592948549765 3303124642795798677853081)
              ·
                refine ⟨2477343482096849008389811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303124642795798677853081 2477343482096849008389811)
                ·
                  refine ⟨3716015223145273512584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477343482096849008389811 3716015223145273512584717)
                  ·
                    refine ⟨1393505708679477567219269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716015223145273512584717 1393505708679477567219269)
                    ·
                      rfl

theorem cell22_4070764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_4070764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070764 prefixEnd_4070764 := by exact prefixLift 4070764
  have htrace : WordTrace (prefixWord ++ tailWord_4070764) baseStart_4070764 baseEnd_4070764 := by
    simpa [prefixWord, tailWord_4070764, baseEnd_4070764] using wordTrace_append hprefix tailTrace_4070764
  have hstable : (prefixWord ++ tailWord_4070764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070764).length < 2 ^ (prefixWord ++ tailWord_4070764).sum := by decide
  have hdescent : baseEnd_4070764 < baseStart_4070764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070788 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_4070788 : Nat := 118140960795 + 4070788 * 2 ^ 59
def prefixEnd_4070788 : Nat := 4983230072969 + 3 ^ 40 * 4070788 * 2
def baseEnd_4070788 : Nat := 464504641456649834873065

theorem tailTrace_4070788 : CollatzResearch.WordTrace tailWord_4070788 prefixEnd_4070788 464504641456649834873065 := by
  unfold tailWord_4070788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74236917988118893042502509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98982557317491857390003345 74236917988118893042502509)
  ·
    refine ⟨27838844245544584890938441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74236917988118893042502509 27838844245544584890938441)
    ·
      refine ⟨20879133184158438668203831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27838844245544584890938441 20879133184158438668203831)
      ·
        refine ⟨31318699776237658002305747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20879133184158438668203831 31318699776237658002305747)
        ·
          refine ⟨46978049664356487003458621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31318699776237658002305747 46978049664356487003458621)
          ·
            refine ⟨17616768624133682626296983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46978049664356487003458621 17616768624133682626296983)
            ·
              refine ⟨26425152936200523939445475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17616768624133682626296983 26425152936200523939445475)
              ·
                refine ⟨39637729404300785909168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26425152936200523939445475 39637729404300785909168213)
                ·
                  refine ⟨464504641456649834873065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39637729404300785909168213 464504641456649834873065)
                  ·
                    rfl

theorem cell22_4070788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_4070788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070788 prefixEnd_4070788 := by exact prefixLift 4070788
  have htrace : WordTrace (prefixWord ++ tailWord_4070788) baseStart_4070788 baseEnd_4070788 := by
    simpa [prefixWord, tailWord_4070788, baseEnd_4070788] using wordTrace_append hprefix tailTrace_4070788
  have hstable : (prefixWord ++ tailWord_4070788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070788).length < 2 ^ (prefixWord ++ tailWord_4070788).sum := by decide
  have hdescent : baseEnd_4070788 < baseStart_4070788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070805 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 4]
def baseStart_4070805 : Nat := 118140960795 + 4070805 * 2 ^ 59
def prefixEnd_4070805 : Nat := 4983230072969 + 3 ^ 40 * 4070805 * 2
def baseEnd_4070805 : Nat := 464506581272455708981381

theorem tailTrace_4070805 : CollatzResearch.WordTrace tailWord_4070805 prefixEnd_4070805 464506581272455708981381 := by
  unfold tailWord_4070805
  simp only [CollatzResearch.WordTrace]
  refine ⟨148474456017176197988373869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98982970678117465325582579 148474456017176197988373869)
  ·
    refine ⟨55677921006441074245640201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148474456017176197988373869 55677921006441074245640201)
    ·
      refine ⟨41758440754830805684230151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55677921006441074245640201 41758440754830805684230151)
      ·
        refine ⟨62637661132246208526345227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41758440754830805684230151 62637661132246208526345227)
        ·
          refine ⟨93956491698369312789517841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62637661132246208526345227 93956491698369312789517841)
          ·
            refine ⟨70467368773776984592138381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93956491698369312789517841 70467368773776984592138381)
            ·
              refine ⟨26425263290166369222051893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70467368773776984592138381 26425263290166369222051893)
              ·
                refine ⟨2477368433453097114567365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26425263290166369222051893 2477368433453097114567365)
                ·
                  refine ⟨464506581272455708981381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477368433453097114567365 464506581272455708981381)
                  ·
                    rfl

theorem cell22_4070805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_4070805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070805 prefixEnd_4070805 := by exact prefixLift 4070805
  have htrace : WordTrace (prefixWord ++ tailWord_4070805) baseStart_4070805 baseEnd_4070805 := by
    simpa [prefixWord, tailWord_4070805, baseEnd_4070805] using wordTrace_append hprefix tailTrace_4070805
  have hstable : (prefixWord ++ tailWord_4070805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070805).length < 2 ^ (prefixWord ++ tailWord_4070805).sum := by decide
  have hdescent : baseEnd_4070805 < baseStart_4070805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070833 : List Nat := [1, 2, 2, 4, 1, 1, 2, 9]
def baseStart_4070833 : Nat := 118140960795 + 4070833 * 2 ^ 59
def prefixEnd_4070833 : Nat := 4983230072969 + 3 ^ 40 * 4070833 * 2
def baseEnd_4070833 : Nat := 154836592087731598582673

theorem tailTrace_4070833 : CollatzResearch.WordTrace tailWord_4070833 prefixEnd_4070833 154836592087731598582673 := by
  unfold tailWord_4070833
  simp only [CollatzResearch.WordTrace]
  refine ⟨148475477261074758770393153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98983651507383172513595435 148475477261074758770393153)
  ·
    refine ⟨111356607945806069077794865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148475477261074758770393153 111356607945806069077794865)
    ·
      refine ⟨83517455959354551808346149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111356607945806069077794865 83517455959354551808346149)
      ·
        refine ⟨15659522992378978464064903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83517455959354551808346149 15659522992378978464064903)
        ·
          refine ⟨23489284488568467696097355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659522992378978464064903 23489284488568467696097355)
          ·
            refine ⟨35233926732852701544146033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23489284488568467696097355 35233926732852701544146033)
            ·
              refine ⟨26425445049639526158109525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35233926732852701544146033 26425445049639526158109525)
              ·
                refine ⟨154836592087731598582673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26425445049639526158109525 154836592087731598582673)
                ·
                  rfl

theorem cell22_4070833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 9].length) (baseStart_4070833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070833 prefixEnd_4070833 := by exact prefixLift 4070833
  have htrace : WordTrace (prefixWord ++ tailWord_4070833) baseStart_4070833 baseEnd_4070833 := by
    simpa [prefixWord, tailWord_4070833, baseEnd_4070833] using wordTrace_append hprefix tailTrace_4070833
  have hstable : (prefixWord ++ tailWord_4070833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070833).length < 2 ^ (prefixWord ++ tailWord_4070833).sum := by decide
  have hdescent : baseEnd_4070833 < baseStart_4070833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070837 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_4070837 : Nat := 118140960795 + 4070837 * 2 ^ 59
def prefixEnd_4070837 : Nat := 4983230072969 + 3 ^ 40 * 4070837 * 2
def baseEnd_4070837 : Nat := 1393530698071329710144045

theorem tailTrace_4070837 : CollatzResearch.WordTrace tailWord_4070837 prefixEnd_4070837 1393530698071329710144045 := by
  unfold tailWord_4070837
  simp only [CollatzResearch.WordTrace]
  refine ⟨148475623153060267453538765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98983748768706844969025843 148475623153060267453538765)
  ·
    refine ⟨55678358682397600295077037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148475623153060267453538765 55678358682397600295077037)
    ·
      refine ⟨20879384505899100110653889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55678358682397600295077037 20879384505899100110653889)
      ·
        refine ⟨15659538379424325082990417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20879384505899100110653889 15659538379424325082990417)
        ·
          refine ⟨11744653784568243812242813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15659538379424325082990417 11744653784568243812242813)
          ·
            refine ⟨4404245169213091429591055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11744653784568243812242813 4404245169213091429591055)
            ·
              refine ⟨6606367753819637144386583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404245169213091429591055 6606367753819637144386583)
              ·
                refine ⟨9909551630729455716579875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606367753819637144386583 9909551630729455716579875)
                ·
                  refine ⟨14864327446094183574869813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9909551630729455716579875 14864327446094183574869813)
                  ·
                    refine ⟨1393530698071329710144045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14864327446094183574869813 1393530698071329710144045)
                    ·
                      rfl

theorem cell22_4070837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_4070837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070837 prefixEnd_4070837 := by exact prefixLift 4070837
  have htrace : WordTrace (prefixWord ++ tailWord_4070837) baseStart_4070837 baseEnd_4070837 := by
    simpa [prefixWord, tailWord_4070837, baseEnd_4070837] using wordTrace_append hprefix tailTrace_4070837
  have hstable : (prefixWord ++ tailWord_4070837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070837).length < 2 ^ (prefixWord ++ tailWord_4070837).sum := by decide
  have hdescent : baseEnd_4070837 < baseStart_4070837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070940 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_4070940 : Nat := 118140960795 + 4070940 * 2 ^ 59
def prefixEnd_4070940 : Nat := 4983230072969 + 3 ^ 40 * 4070940 * 2
def baseEnd_4070940 : Nat := 464521985692090591606243

theorem tailTrace_4070940 : CollatzResearch.WordTrace tailWord_4070940 prefixEnd_4070940 464521985692090591606243 := by
  unfold tailWord_4070940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74239689935843558022269137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98986253247791410696358849 74239689935843558022269137)
  ·
    refine ⟨55679767451882668516701853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74239689935843558022269137 55679767451882668516701853)
    ·
      refine ⟨20879912794456000693763195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55679767451882668516701853 20879912794456000693763195)
      ·
        refine ⟨31319869191684001040644793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20879912794456000693763195 31319869191684001040644793)
        ·
          refine ⟨23489901893763000780483595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31319869191684001040644793 23489901893763000780483595)
          ·
            refine ⟨35234852840644501170725393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23489901893763000780483595 35234852840644501170725393)
            ·
              refine ⟨26426139630483375878044045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35234852840644501170725393 26426139630483375878044045)
              ·
                refine ⟨9909802361431265954266517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26426139630483375878044045 9909802361431265954266517)
                ·
                  refine ⟨464521985692090591606243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9909802361431265954266517 464521985692090591606243)
                  ·
                    rfl

theorem cell22_4070940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_4070940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070940 prefixEnd_4070940 := by exact prefixLift 4070940
  have htrace : WordTrace (prefixWord ++ tailWord_4070940) baseStart_4070940 baseEnd_4070940 := by
    simpa [prefixWord, tailWord_4070940, baseEnd_4070940] using wordTrace_append hprefix tailTrace_4070940
  have hstable : (prefixWord ++ tailWord_4070940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070940).length < 2 ^ (prefixWord ++ tailWord_4070940).sum := by decide
  have hdescent : baseEnd_4070940 < baseStart_4070940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070955 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 8, 3]
def baseStart_4070955 : Nat := 118140960795 + 4070955 * 2 ^ 59
def prefixEnd_4070955 : Nat := 4983230072969 + 3 ^ 40 * 4070955 * 2
def baseEnd_4070955 : Nat := 1393571091882816735693683

theorem tailTrace_4070955 : CollatzResearch.WordTrace tailWord_4070955 prefixEnd_4070955 1393571091882816735693683 := by
  unfold tailWord_4070955
  simp only [CollatzResearch.WordTrace]
  refine ⟨148479926966632773606334319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98986617977755182404222879 148479926966632773606334319)
  ·
    refine ⟨222719890449949160409501479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148479926966632773606334319 222719890449949160409501479)
    ·
      refine ⟨334079835674923740614252219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222719890449949160409501479 334079835674923740614252219)
      ·
        refine ⟨501119753512385610921378329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334079835674923740614252219 501119753512385610921378329)
        ·
          refine ⟨375839815134289208191033747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501119753512385610921378329 375839815134289208191033747)
          ·
            refine ⟨563759722701433812286550621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375839815134289208191033747 563759722701433812286550621)
            ·
              refine ⟨211409896013037679607456483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 563759722701433812286550621 211409896013037679607456483)
              ·
                refine ⟨317114844019556519411184725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211409896013037679607456483 317114844019556519411184725)
                ·
                  refine ⟨3716189578354177961849821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 317114844019556519411184725 3716189578354177961849821)
                  ·
                    refine ⟨1393571091882816735693683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716189578354177961849821 1393571091882816735693683)
                    ·
                      rfl

theorem cell22_4070955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3].length) (baseStart_4070955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070955 prefixEnd_4070955 := by exact prefixLift 4070955
  have htrace : WordTrace (prefixWord ++ tailWord_4070955) baseStart_4070955 baseEnd_4070955 := by
    simpa [prefixWord, tailWord_4070955, baseEnd_4070955] using wordTrace_append hprefix tailTrace_4070955
  have hstable : (prefixWord ++ tailWord_4070955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070955).length < 2 ^ (prefixWord ++ tailWord_4070955).sum := by decide
  have hdescent : baseEnd_4070955 < baseStart_4070955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4070970 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_4070970 : Nat := 118140960795 + 4070970 * 2 ^ 59
def prefixEnd_4070970 : Nat := 4983230072969 + 3 ^ 40 * 4070970 * 2
def baseEnd_4070970 : Nat := 1393576226689361696568637

theorem tailTrace_4070970 : CollatzResearch.WordTrace tailWord_4070970 prefixEnd_4070970 1393576226689361696568637 := by
  unfold tailWord_4070970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37120118515394607792032591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98986982707718954112086909 37120118515394607792032591)
  ·
    refine ⟨55680177773091911688048887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37120118515394607792032591 55680177773091911688048887)
    ·
      refine ⟨83520266659637867532073331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55680177773091911688048887 83520266659637867532073331)
      ·
        refine ⟨125280399989456801298109997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83520266659637867532073331 125280399989456801298109997)
        ·
          refine ⟨46980149996046300486791249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125280399989456801298109997 46980149996046300486791249)
          ·
            refine ⟨35235112497034725365093437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46980149996046300486791249 35235112497034725365093437)
            ·
              refine ⟨13213167186388022011910039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35235112497034725365093437 13213167186388022011910039)
              ·
                refine ⟨19819750779582033017865059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13213167186388022011910039 19819750779582033017865059)
                ·
                  refine ⟨29729626169373049526797589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19819750779582033017865059 29729626169373049526797589)
                  ·
                    refine ⟨1393576226689361696568637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29729626169373049526797589 1393576226689361696568637)
                    ·
                      rfl

theorem cell22_4070970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_4070970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4070970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4070970 prefixEnd_4070970 := by exact prefixLift 4070970
  have htrace : WordTrace (prefixWord ++ tailWord_4070970) baseStart_4070970 baseEnd_4070970 := by
    simpa [prefixWord, tailWord_4070970, baseEnd_4070970] using wordTrace_append hprefix tailTrace_4070970
  have hstable : (prefixWord ++ tailWord_4070970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4070970).length < 2 ^ (prefixWord ++ tailWord_4070970).sum := by decide
  have hdescent : baseEnd_4070970 < baseStart_4070970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4070970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071015 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4071015 : Nat := 118140960795 + 4071015 * 2 ^ 59
def prefixEnd_4071015 : Nat := 4983230072969 + 3 ^ 40 * 4071015 * 2
def baseEnd_4071015 : Nat := 1393591631108996579193499

theorem tailTrace_4071015 : CollatzResearch.WordTrace tailWord_4071015 prefixEnd_4071015 1393591631108996579193499 := by
  unfold tailWord_4071015
  simp only [CollatzResearch.WordTrace]
  refine ⟨148482115346415403853518499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98988076897610269235678999 148482115346415403853518499)
  ·
    refine ⟨222723173019623105780277749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148482115346415403853518499 222723173019623105780277749)
    ·
      refine ⟨20880297470589666166901039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222723173019623105780277749 20880297470589666166901039)
      ·
        refine ⟨31320446205884499250351559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20880297470589666166901039 31320446205884499250351559)
        ·
          refine ⟨46980669308826748875527339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31320446205884499250351559 46980669308826748875527339)
          ·
            refine ⟨70471003963240123313291009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46980669308826748875527339 70471003963240123313291009)
            ·
              refine ⟨52853252972430092484968257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70471003963240123313291009 52853252972430092484968257)
              ·
                refine ⟨39639939729322569363726193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52853252972430092484968257 39639939729322569363726193)
                ·
                  refine ⟨29729954796991927022794645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39639939729322569363726193 29729954796991927022794645)
                  ·
                    refine ⟨1393591631108996579193499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29729954796991927022794645 1393591631108996579193499)
                    ·
                      rfl

theorem cell22_4071015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4071015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071015 prefixEnd_4071015 := by exact prefixLift 4071015
  have htrace : WordTrace (prefixWord ++ tailWord_4071015) baseStart_4071015 baseEnd_4071015 := by
    simpa [prefixWord, tailWord_4071015, baseEnd_4071015] using wordTrace_append hprefix tailTrace_4071015
  have hstable : (prefixWord ++ tailWord_4071015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071015).length < 2 ^ (prefixWord ++ tailWord_4071015).sum := by decide
  have hdescent : baseEnd_4071015 < baseStart_4071015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071017 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_4071017 : Nat := 118140960795 + 4071017 * 2 ^ 59
def prefixEnd_4071017 : Nat := 4983230072969 + 3 ^ 40 * 4071017 * 2
def baseEnd_4071017 : Nat := 1393592315749869240643493

theorem tailTrace_4071017 : CollatzResearch.WordTrace tailWord_4071017 prefixEnd_4071017 1393592315749869240643493 := by
  unfold tailWord_4071017
  simp only [CollatzResearch.WordTrace]
  refine ⟨148482188292408158195091305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98988125528272105463394203 148482188292408158195091305)
  ·
    refine ⟨111361641219306118646318479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148482188292408158195091305 111361641219306118646318479)
    ·
      refine ⟨167042461828959177969477719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111361641219306118646318479 167042461828959177969477719)
      ·
        refine ⟨250563692743438766954216579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167042461828959177969477719 250563692743438766954216579)
        ·
          refine ⟨375845539115158150431324869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250563692743438766954216579 375845539115158150431324869)
          ·
            refine ⟨70471038584092153205873413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375845539115158150431324869 70471038584092153205873413)
            ·
              refine ⟨13213319734517278726101265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70471038584092153205873413 13213319734517278726101265)
              ·
                refine ⟨9909989800887959044575949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13213319734517278726101265 9909989800887959044575949)
                ·
                  refine ⟨3716246175332984641715981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9909989800887959044575949 3716246175332984641715981)
                  ·
                    refine ⟨1393592315749869240643493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716246175332984641715981 1393592315749869240643493)
                    ·
                      rfl

theorem cell22_4071017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_4071017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071017 prefixEnd_4071017 := by exact prefixLift 4071017
  have htrace : WordTrace (prefixWord ++ tailWord_4071017) baseStart_4071017 baseEnd_4071017 := by
    simpa [prefixWord, tailWord_4071017, baseEnd_4071017] using wordTrace_append hprefix tailTrace_4071017
  have hstable : (prefixWord ++ tailWord_4071017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071017).length < 2 ^ (prefixWord ++ tailWord_4071017).sum := by decide
  have hdescent : baseEnd_4071017 < baseStart_4071017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071034 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_4071034 : Nat := 118140960795 + 4071034 * 2 ^ 59
def prefixEnd_4071034 : Nat := 4983230072969 + 3 ^ 40 * 4071034 * 2
def baseEnd_4071034 : Nat := 1393598135197286862968441

theorem tailTrace_4071034 : CollatzResearch.WordTrace tailWord_4071034 prefixEnd_4071034 1393598135197286862968441 := by
  unfold tailWord_4071034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37120702083336642524615039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98988538888897713398973437 37120702083336642524615039)
  ·
    refine ⟨55681053125004963786922559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37120702083336642524615039 55681053125004963786922559)
    ·
      refine ⟨83521579687507445680383839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55681053125004963786922559 83521579687507445680383839)
      ·
        refine ⟨125282369531261168520575759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83521579687507445680383839 125282369531261168520575759)
        ·
          refine ⟨187923554296891752780863639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125282369531261168520575759 187923554296891752780863639)
          ·
            refine ⟨281885331445337629171295459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187923554296891752780863639 281885331445337629171295459)
            ·
              refine ⟨422827997168006443756943189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281885331445337629171295459 422827997168006443756943189)
              ·
                refine ⟨2477507795906287756388339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 422827997168006443756943189 2477507795906287756388339)
                ·
                  refine ⟨3716261693859431634582509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477507795906287756388339 3716261693859431634582509)
                  ·
                    refine ⟨1393598135197286862968441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716261693859431634582509 1393598135197286862968441)
                    ·
                      rfl

theorem cell22_4071034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_4071034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071034 prefixEnd_4071034 := by exact prefixLift 4071034
  have htrace : WordTrace (prefixWord ++ tailWord_4071034) baseStart_4071034 baseEnd_4071034 := by
    simpa [prefixWord, tailWord_4071034, baseEnd_4071034] using wordTrace_append hprefix tailTrace_4071034
  have hstable : (prefixWord ++ tailWord_4071034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071034).length < 2 ^ (prefixWord ++ tailWord_4071034).sum := by decide
  have hdescent : baseEnd_4071034 < baseStart_4071034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071051 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 1, 3]
def baseStart_4071051 : Nat := 118140960795 + 4071051 * 2 ^ 59
def prefixEnd_4071051 : Nat := 4983230072969 + 3 ^ 40 * 4071051 * 2
def baseEnd_4071051 : Nat := 1393603954644704485293389

theorem tailTrace_4071051 : CollatzResearch.WordTrace tailWord_4071051 prefixEnd_4071051 1393603954644704485293389 := by
  unfold tailWord_4071051
  simp only [CollatzResearch.WordTrace]
  refine ⟨148483428374284982001829007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98988952249523321334552671 148483428374284982001829007)
  ·
    refine ⟨222725142561427473002743511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148483428374284982001829007 222725142561427473002743511)
    ·
      refine ⟨334087713842141209504115267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222725142561427473002743511 334087713842141209504115267)
      ·
        refine ⟨501131570763211814256172901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334087713842141209504115267 501131570763211814256172901)
        ·
          refine ⟨93962169518102215173032419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501131570763211814256172901 93962169518102215173032419)
          ·
            refine ⟨140943254277153322759548629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93962169518102215173032419 140943254277153322759548629)
            ·
              refine ⟨3303357522120781002176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140943254277153322759548629 3303357522120781002176921)
              ·
                refine ⟨2477518141590585751632691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303357522120781002176921 2477518141590585751632691)
                ·
                  refine ⟨3716277212385878627449037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477518141590585751632691 3716277212385878627449037)
                  ·
                    refine ⟨1393603954644704485293389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716277212385878627449037 1393603954644704485293389)
                    ·
                      rfl

theorem cell22_4071051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 3].length) (baseStart_4071051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071051 prefixEnd_4071051 := by exact prefixLift 4071051
  have htrace : WordTrace (prefixWord ++ tailWord_4071051) baseStart_4071051 baseEnd_4071051 := by
    simpa [prefixWord, tailWord_4071051, baseEnd_4071051] using wordTrace_append hprefix tailTrace_4071051
  have hstable : (prefixWord ++ tailWord_4071051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071051).length < 2 ^ (prefixWord ++ tailWord_4071051).sum := by decide
  have hdescent : baseEnd_4071051 < baseStart_4071051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071064 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_4071064 : Nat := 118140960795 + 4071064 * 2 ^ 59
def prefixEnd_4071064 : Nat := 4983230072969 + 3 ^ 40 * 4071064 * 2
def baseEnd_4071064 : Nat := 464536134936792261572783

theorem tailTrace_4071064 : CollatzResearch.WordTrace tailWord_4071064 prefixEnd_4071064 464536134936792261572783 := by
  unfold tailWord_4071064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74241951261618942611026123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98989268348825256814701497 74241951261618942611026123)
  ·
    refine ⟨111362926892428413916539185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74241951261618942611026123 111362926892428413916539185)
    ·
      refine ⟨83522195169321310437404389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111362926892428413916539185 83522195169321310437404389)
      ·
        refine ⟨15660411594247745707013323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83522195169321310437404389 15660411594247745707013323)
        ·
          refine ⟨23490617391371618560519985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660411594247745707013323 23490617391371618560519985)
          ·
            refine ⟨17617963043528713920389989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23490617391371618560519985 17617963043528713920389989)
            ·
              refine ⟨3303368070661633860073123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17617963043528713920389989 3303368070661633860073123)
              ·
                refine ⟨4955052105992450790109685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303368070661633860073123 4955052105992450790109685)
                ·
                  refine ⟨464536134936792261572783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4955052105992450790109685 464536134936792261572783)
                  ·
                    rfl

theorem cell22_4071064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_4071064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071064 prefixEnd_4071064 := by exact prefixLift 4071064
  have htrace : WordTrace (prefixWord ++ tailWord_4071064) baseStart_4071064 baseEnd_4071064 := by
    simpa [prefixWord, tailWord_4071064, baseEnd_4071064] using wordTrace_append hprefix tailTrace_4071064
  have hstable : (prefixWord ++ tailWord_4071064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071064).length < 2 ^ (prefixWord ++ tailWord_4071064).sum := by decide
  have hdescent : baseEnd_4071064 < baseStart_4071064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071075 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 8]
def baseStart_4071075 : Nat := 118140960795 + 4071075 * 2 ^ 59
def prefixEnd_4071075 : Nat := 4983230072969 + 3 ^ 40 * 4071075 * 2
def baseEnd_4071075 : Nat := 464537390111725474231105

theorem tailTrace_4071075 : CollatzResearch.WordTrace tailWord_4071075 prefixEnd_4071075 464537390111725474231105 := by
  unfold tailWord_4071075
  simp only [CollatzResearch.WordTrace]
  refine ⟨148484303726198034100702679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98989535817465356067135119 148484303726198034100702679)
  ·
    refine ⟨222726455589297051151054019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148484303726198034100702679 222726455589297051151054019)
    ·
      refine ⟨334089683383945576726581029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222726455589297051151054019 334089683383945576726581029)
      ·
        refine ⟨62641815634489795636233943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334089683383945576726581029 62641815634489795636233943)
        ·
          refine ⟨93962723451734693454350915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62641815634489795636233943 93962723451734693454350915)
          ·
            refine ⟨140944085177602040181526373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93962723451734693454350915 140944085177602040181526373)
            ·
              refine ⟨26427015970800382534036195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140944085177602040181526373 26427015970800382534036195)
              ·
                refine ⟨39640523956200573801054293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26427015970800382534036195 39640523956200573801054293)
                ·
                  refine ⟨464537390111725474231105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39640523956200573801054293 464537390111725474231105)
                  ·
                    rfl

theorem cell22_4071075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_4071075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071075 prefixEnd_4071075 := by exact prefixLift 4071075
  have htrace : WordTrace (prefixWord ++ tailWord_4071075) baseStart_4071075 baseEnd_4071075 := by
    simpa [prefixWord, tailWord_4071075, baseEnd_4071075] using wordTrace_append hprefix tailTrace_4071075
  have hstable : (prefixWord ++ tailWord_4071075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071075).length < 2 ^ (prefixWord ++ tailWord_4071075).sum := by decide
  have hdescent : baseEnd_4071075 < baseStart_4071075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071120 : List Nat := [2, 1, 1, 1, 1, 2, 1, 13]
def baseStart_4071120 : Nat := 118140960795 + 4071120 * 2 ^ 59
def prefixEnd_4071120 : Nat := 4983230072969 + 3 ^ 40 * 4071120 * 2
def baseEnd_4071120 : Nat := 154847508306090145035353

theorem tailTrace_4071120 : CollatzResearch.WordTrace tailWord_4071120 prefixEnd_4071120 154847508306090145035353 := by
  unfold tailWord_4071120
  simp only [CollatzResearch.WordTrace]
  refine ⟨74242972505517503393045407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98990630007356671190727209 74242972505517503393045407)
  ·
    refine ⟨111364458758276255089568111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74242972505517503393045407 111364458758276255089568111)
    ·
      refine ⟨167046688137414382634352167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111364458758276255089568111 167046688137414382634352167)
      ·
        refine ⟨250570032206121573951528251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167046688137414382634352167 250570032206121573951528251)
        ·
          refine ⟨375855048309182360927292377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250570032206121573951528251 375855048309182360927292377)
          ·
            refine ⟨281891286231886770695469283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375855048309182360927292377 281891286231886770695469283)
            ·
              refine ⟨422836929347830156043203925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281891286231886770695469283 422836929347830156043203925)
              ·
                refine ⟨154847508306090145035353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 422836929347830156043203925 154847508306090145035353)
                ·
                  rfl

theorem cell22_4071120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_4071120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071120 prefixEnd_4071120 := by exact prefixLift 4071120
  have htrace : WordTrace (prefixWord ++ tailWord_4071120) baseStart_4071120 baseEnd_4071120 := by
    simpa [prefixWord, tailWord_4071120, baseEnd_4071120] using wordTrace_append hprefix tailTrace_4071120
  have hstable : (prefixWord ++ tailWord_4071120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071120).length < 2 ^ (prefixWord ++ tailWord_4071120).sum := by decide
  have hdescent : baseEnd_4071120 < baseStart_4071120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071124 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4071124 : Nat := 118140960795 + 4071124 * 2 ^ 59
def prefixEnd_4071124 : Nat := 4983230072969 + 3 ^ 40 * 4071124 * 2
def baseEnd_4071124 : Nat := 1393628944036556628218165

theorem tailTrace_4071124 : CollatzResearch.WordTrace tailWord_4071124 prefixEnd_4071124 1393628944036556628218165 := by
  unfold tailWord_4071124
  simp only [CollatzResearch.WordTrace]
  refine ⟨74243045451510257734618213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98990727268680343646157617 74243045451510257734618213)
  ·
    refine ⟨13920571022158173325240915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74243045451510257734618213 13920571022158173325240915)
    ·
      refine ⟨20880856533237259987861373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920571022158173325240915 20880856533237259987861373)
      ·
        refine ⟨7830321199963972495448015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20880856533237259987861373 7830321199963972495448015)
        ·
          refine ⟨11745481799945958743172023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830321199963972495448015 11745481799945958743172023)
          ·
            refine ⟨17618222699918938114758035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745481799945958743172023 17618222699918938114758035)
            ·
              refine ⟨26427334049878407172137053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17618222699918938114758035 26427334049878407172137053)
              ·
                refine ⟨9910250268704402689551395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26427334049878407172137053 9910250268704402689551395)
                ·
                  refine ⟨14865375403056604034327093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910250268704402689551395 14865375403056604034327093)
                  ·
                    refine ⟨1393628944036556628218165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14865375403056604034327093 1393628944036556628218165)
                    ·
                      rfl

theorem cell22_4071124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4071124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071124 prefixEnd_4071124 := by exact prefixLift 4071124
  have htrace : WordTrace (prefixWord ++ tailWord_4071124) baseStart_4071124 baseEnd_4071124 := by
    simpa [prefixWord, tailWord_4071124, baseEnd_4071124] using wordTrace_append hprefix tailTrace_4071124
  have hstable : (prefixWord ++ tailWord_4071124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071124).length < 2 ^ (prefixWord ++ tailWord_4071124).sum := by decide
  have hdescent : baseEnd_4071124 < baseStart_4071124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071139 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 6]
def baseStart_4071139 : Nat := 118140960795 + 4071139 * 2 ^ 59
def prefixEnd_4071139 : Nat := 4983230072969 + 3 ^ 40 * 4071139 * 2
def baseEnd_4071139 : Nat := 1393634078843101589093119

theorem tailTrace_4071139 : CollatzResearch.WordTrace tailWord_4071139 prefixEnd_4071139 1393634078843101589093119 := by
  unfold tailWord_4071139
  simp only [CollatzResearch.WordTrace]
  refine ⟨148486637997966173031032471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98991091998644115354021647 148486637997966173031032471)
  ·
    refine ⟨222729956996949259546548707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148486637997966173031032471 222729956996949259546548707)
    ·
      refine ⟨334094935495423889319823061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222729956996949259546548707 334094935495423889319823061)
      ·
        refine ⟨7830350050673997405933353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 334094935495423889319823061 7830350050673997405933353)
        ·
          refine ⟨5872762538005498054450015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830350050673997405933353 5872762538005498054450015)
          ·
            refine ⟨8809143807008247081675023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872762538005498054450015 8809143807008247081675023)
            ·
              refine ⟨13213715710512370622512535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809143807008247081675023 13213715710512370622512535)
              ·
                refine ⟨19820573565768555933768803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13213715710512370622512535 19820573565768555933768803)
                ·
                  refine ⟨29730860348652833900653205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19820573565768555933768803 29730860348652833900653205)
                  ·
                    refine ⟨1393634078843101589093119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29730860348652833900653205 1393634078843101589093119)
                    ·
                      rfl

theorem cell22_4071139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_4071139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071139 prefixEnd_4071139 := by exact prefixLift 4071139
  have htrace : WordTrace (prefixWord ++ tailWord_4071139) baseStart_4071139 baseEnd_4071139 := by
    simpa [prefixWord, tailWord_4071139, baseEnd_4071139] using wordTrace_append hprefix tailTrace_4071139
  have hstable : (prefixWord ++ tailWord_4071139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071139).length < 2 ^ (prefixWord ++ tailWord_4071139).sum := by decide
  have hdescent : baseEnd_4071139 < baseStart_4071139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071143 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 4]
def baseStart_4071143 : Nat := 118140960795 + 4071143 * 2 ^ 59
def prefixEnd_4071143 : Nat := 4983230072969 + 3 ^ 40 * 4071143 * 2
def baseEnd_4071143 : Nat := 464545149374948970664369

theorem tailTrace_4071143 : CollatzResearch.WordTrace tailWord_4071143 prefixEnd_4071143 464545149374948970664369 := by
  unfold tailWord_4071143
  simp only [CollatzResearch.WordTrace]
  refine ⟨148486783889951681714178083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98991189259967787809452055 148486783889951681714178083)
  ·
    refine ⟨222730175834927522571267125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148486783889951681714178083 222730175834927522571267125)
    ·
      refine ⟨20880953984524455241056293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222730175834927522571267125 20880953984524455241056293)
      ·
        refine ⟨3915178872098335357698055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20880953984524455241056293 3915178872098335357698055)
        ·
          refine ⟨5872768308147503036547083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915178872098335357698055 5872768308147503036547083)
          ·
            refine ⟨8809152462221254554820625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872768308147503036547083 8809152462221254554820625)
            ·
              refine ⟨6606864346665940916115469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8809152462221254554820625 6606864346665940916115469)
              ·
                refine ⟨2477574129999727843543301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6606864346665940916115469 2477574129999727843543301)
                ·
                  refine ⟨464545149374948970664369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477574129999727843543301 464545149374948970664369)
                  ·
                    rfl

theorem cell22_4071143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 4].length) (baseStart_4071143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071143 prefixEnd_4071143 := by exact prefixLift 4071143
  have htrace : WordTrace (prefixWord ++ tailWord_4071143) baseStart_4071143 baseEnd_4071143 := by
    simpa [prefixWord, tailWord_4071143, baseEnd_4071143] using wordTrace_append hprefix tailTrace_4071143
  have hstable : (prefixWord ++ tailWord_4071143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071143).length < 2 ^ (prefixWord ++ tailWord_4071143).sum := by decide
  have hdescent : baseEnd_4071143 < baseStart_4071143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071158 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_4071158 : Nat := 118140960795 + 4071158 * 2 ^ 59
def prefixEnd_4071158 : Nat := 4983230072969 + 3 ^ 40 * 4071158 * 2
def baseEnd_4071158 : Nat := 1393640582931391872868061

theorem tailTrace_4071158 : CollatzResearch.WordTrace tailWord_4071158 prefixEnd_4071158 1393640582931391872868061 := by
  unfold tailWord_4071158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280458186556083704748383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98991553989931559517316085 9280458186556083704748383)
  ·
    refine ⟨13920687279834125557122575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9280458186556083704748383 13920687279834125557122575)
    ·
      refine ⟨20881030919751188335683863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920687279834125557122575 20881030919751188335683863)
      ·
        refine ⟨31321546379626782503525795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20881030919751188335683863 31321546379626782503525795)
        ·
          refine ⟨46982319569440173755288693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31321546379626782503525795 46982319569440173755288693)
          ·
            refine ⟨4404592459635016289558315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46982319569440173755288693 4404592459635016289558315)
            ·
              refine ⟨6606888689452524434337473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404592459635016289558315 6606888689452524434337473)
              ·
                refine ⟨4955166517089393325753105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606888689452524434337473 4955166517089393325753105)
                ·
                  refine ⟨3716374887817044994314829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955166517089393325753105 3716374887817044994314829)
                  ·
                    refine ⟨1393640582931391872868061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716374887817044994314829 1393640582931391872868061)
                    ·
                      rfl

theorem cell22_4071158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_4071158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071158 prefixEnd_4071158 := by exact prefixLift 4071158
  have htrace : WordTrace (prefixWord ++ tailWord_4071158) baseStart_4071158 baseEnd_4071158 := by
    simpa [prefixWord, tailWord_4071158, baseEnd_4071158] using wordTrace_append hprefix tailTrace_4071158
  have hstable : (prefixWord ++ tailWord_4071158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071158).length < 2 ^ (prefixWord ++ tailWord_4071158).sum := by decide
  have hdescent : baseEnd_4071158 < baseStart_4071158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071169 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_4071169 : Nat := 118140960795 + 4071169 * 2 ^ 59
def prefixEnd_4071169 : Nat := 4983230072969 + 3 ^ 40 * 4071169 * 2
def baseEnd_4071169 : Nat := 1393644348456191510843027

theorem tailTrace_4071169 : CollatzResearch.WordTrace tailWord_4071169 prefixEnd_4071169 1393644348456191510843027 := by
  unfold tailWord_4071169
  simp only [CollatzResearch.WordTrace]
  refine ⟨148487732187857488154624561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98991821458571658769749707 148487732187857488154624561)
  ·
    refine ⟨111365799140893116115968421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148487732187857488154624561 111365799140893116115968421)
    ·
      refine ⟨20881087338917459271744079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111365799140893116115968421 20881087338917459271744079)
      ·
        refine ⟨31321631008376188907616119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20881087338917459271744079 31321631008376188907616119)
        ·
          refine ⟨46982446512564283361424179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31321631008376188907616119 46982446512564283361424179)
          ·
            refine ⟨70473669768846425042136269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46982446512564283361424179 70473669768846425042136269)
            ·
              refine ⟨26427626163317409390801101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70473669768846425042136269 26427626163317409390801101)
              ·
                refine ⟨9910359811244028521550413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26427626163317409390801101 9910359811244028521550413)
                ·
                  refine ⟨3716384929216510695581405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9910359811244028521550413 3716384929216510695581405)
                  ·
                    refine ⟨1393644348456191510843027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716384929216510695581405 1393644348456191510843027)
                    ·
                      rfl

theorem cell22_4071169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_4071169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071169 prefixEnd_4071169 := by exact prefixLift 4071169
  have htrace : WordTrace (prefixWord ++ tailWord_4071169) baseStart_4071169 baseEnd_4071169 := by
    simpa [prefixWord, tailWord_4071169, baseEnd_4071169] using wordTrace_append hprefix tailTrace_4071169
  have hstable : (prefixWord ++ tailWord_4071169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071169).length < 2 ^ (prefixWord ++ tailWord_4071169).sum := by decide
  have hdescent : baseEnd_4071169 < baseStart_4071169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071188 : List Nat := [2, 4, 4, 1, 1, 1, 1, 8]
def baseStart_4071188 : Nat := 118140960795 + 4071188 * 2 ^ 59
def prefixEnd_4071188 : Nat := 4983230072969 + 3 ^ 40 * 4071188 * 2
def baseEnd_4071188 : Nat := 154850094727164643846441

theorem tailTrace_4071188 : CollatzResearch.WordTrace tailWord_4071188 prefixEnd_4071188 154850094727164643846441 := by
  unfold tailWord_4071188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74244212587394327199783109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98992283449859102933044145 74244212587394327199783109)
  ·
    refine ⟨13920789860136436349959333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74244212587394327199783109 13920789860136436349959333)
    ·
      refine ⟨2610148098775581815617375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13920789860136436349959333 2610148098775581815617375)
      ·
        refine ⟨3915222148163372723426063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610148098775581815617375 3915222148163372723426063)
        ·
          refine ⟨5872833222245059085139095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915222148163372723426063 5872833222245059085139095)
          ·
            refine ⟨8809249833367588627708643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872833222245059085139095 8809249833367588627708643)
            ·
              refine ⟨13213874750051382941562965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809249833367588627708643 13213874750051382941562965)
              ·
                refine ⟨154850094727164643846441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13213874750051382941562965 154850094727164643846441)
                ·
                  rfl

theorem cell22_4071188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_4071188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071188 prefixEnd_4071188 := by exact prefixLift 4071188
  have htrace : WordTrace (prefixWord ++ tailWord_4071188) baseStart_4071188 baseEnd_4071188 := by
    simpa [prefixWord, tailWord_4071188, baseEnd_4071188] using wordTrace_append hprefix tailTrace_4071188
  have hstable : (prefixWord ++ tailWord_4071188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071188).length < 2 ^ (prefixWord ++ tailWord_4071188).sum := by decide
  have hdescent : baseEnd_4071188 < baseStart_4071188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071276 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_4071276 : Nat := 118140960795 + 4071276 * 2 ^ 59
def prefixEnd_4071276 : Nat := 4983230072969 + 3 ^ 40 * 4071276 * 2
def baseEnd_4071276 : Nat := 1393680976742878898417699

theorem tailTrace_4071276 : CollatzResearch.WordTrace tailWord_4071276 prefixEnd_4071276 1393680976742878898417699 := by
  unfold tailWord_4071276
  simp only [CollatzResearch.WordTrace]
  refine ⟨74245817399234922714384841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98994423198979896952513121 74245817399234922714384841)
  ·
    refine ⟨55684363049426192035788631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74245817399234922714384841 55684363049426192035788631)
    ·
      refine ⟨83526544574139288053682947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55684363049426192035788631 83526544574139288053682947)
      ·
        refine ⟨125289816861208932080524421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83526544574139288053682947 125289816861208932080524421)
        ·
          refine ⟨23491840661476674765098329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125289816861208932080524421 23491840661476674765098329)
          ·
            refine ⟨17618880496107506073823747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23491840661476674765098329 17618880496107506073823747)
            ·
              refine ⟨26428320744161259110735621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17618880496107506073823747 26428320744161259110735621)
              ·
                refine ⟨4955310139530236083262929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26428320744161259110735621 4955310139530236083262929)
                ·
                  refine ⟨3716482604647677062447197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955310139530236083262929 3716482604647677062447197)
                  ·
                    refine ⟨1393680976742878898417699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716482604647677062447197 1393680976742878898417699)
                    ·
                      rfl

theorem cell22_4071276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_4071276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071276 prefixEnd_4071276 := by exact prefixLift 4071276
  have htrace : WordTrace (prefixWord ++ tailWord_4071276) baseStart_4071276 baseEnd_4071276 := by
    simpa [prefixWord, tailWord_4071276, baseEnd_4071276] using wordTrace_append hprefix tailTrace_4071276
  have hstable : (prefixWord ++ tailWord_4071276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071276).length < 2 ^ (prefixWord ++ tailWord_4071276).sum := by decide
  have hdescent : baseEnd_4071276 < baseStart_4071276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071278 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_4071278 : Nat := 118140960795 + 4071278 * 2 ^ 59
def prefixEnd_4071278 : Nat := 4983230072969 + 3 ^ 40 * 4071278 * 2
def baseEnd_4071278 : Nat := 464560553794583853289231

theorem tailTrace_4071278 : CollatzResearch.WordTrace tailWord_4071278 prefixEnd_4071278 464560553794583853289231 := by
  unfold tailWord_4071278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561463468057824971292811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98994471829641733180228325 18561463468057824971292811)
  ·
    refine ⟨27842195202086737456939217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18561463468057824971292811 27842195202086737456939217)
    ·
      refine ⟨20881646401565053092704413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27842195202086737456939217 20881646401565053092704413)
      ·
        refine ⟨7830617400586894909764155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20881646401565053092704413 7830617400586894909764155)
        ·
          refine ⟨11745926100880342364646233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830617400586894909764155 11745926100880342364646233)
          ·
            refine ⟨8809444575660256773484675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11745926100880342364646233 8809444575660256773484675)
            ·
              refine ⟨13214166863490385160227013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809444575660256773484675 13214166863490385160227013)
              ·
                refine ⟨2477656286904447217542565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13214166863490385160227013 2477656286904447217542565)
                ·
                  refine ⟨464560553794583853289231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477656286904447217542565 464560553794583853289231)
                  ·
                    rfl

theorem cell22_4071278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_4071278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071278 prefixEnd_4071278 := by exact prefixLift 4071278
  have htrace : WordTrace (prefixWord ++ tailWord_4071278) baseStart_4071278 baseEnd_4071278 := by
    simpa [prefixWord, tailWord_4071278, baseEnd_4071278] using wordTrace_append hprefix tailTrace_4071278
  have hstable : (prefixWord ++ tailWord_4071278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071278).length < 2 ^ (prefixWord ++ tailWord_4071278).sum := by decide
  have hdescent : baseEnd_4071278 < baseStart_4071278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071287 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_4071287 : Nat := 118140960795 + 4071287 * 2 ^ 59
def prefixEnd_4071287 : Nat := 4983230072969 + 3 ^ 40 * 4071287 * 2
def baseEnd_4071287 : Nat := 1393684742267678536392665

theorem tailTrace_4071287 : CollatzResearch.WordTrace tailWord_4071287 prefixEnd_4071287 1393684742267678536392665 := by
  unfold tailWord_4071287
  simp only [CollatzResearch.WordTrace]
  refine ⟨148492036001429994307420115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98994690667619996204946743 148492036001429994307420115)
  ·
    refine ⟨222738054002144991461130173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148492036001429994307420115 222738054002144991461130173)
    ·
      refine ⟨83526770250804371797923815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222738054002144991461130173 83526770250804371797923815)
      ·
        refine ⟨125290155376206557696885723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83526770250804371797923815 125290155376206557696885723)
        ·
          refine ⟨187935233064309836545328585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125290155376206557696885723 187935233064309836545328585)
          ·
            refine ⟨140951424798232377408996439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187935233064309836545328585 140951424798232377408996439)
            ·
              refine ⟨211427137197348566113494659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140951424798232377408996439 211427137197348566113494659)
              ·
                refine ⟨317140705796022849170241989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211427137197348566113494659 317140705796022849170241989)
                ·
                  refine ⟨59463882336754284219420373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317140705796022849170241989 59463882336754284219420373)
                  ·
                    refine ⟨1393684742267678536392665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59463882336754284219420373 1393684742267678536392665)
                    ·
                      rfl

theorem cell22_4071287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_4071287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071287 prefixEnd_4071287 := by exact prefixLift 4071287
  have htrace : WordTrace (prefixWord ++ tailWord_4071287) baseStart_4071287 baseEnd_4071287 := by
    simpa [prefixWord, tailWord_4071287, baseEnd_4071287] using wordTrace_append hprefix tailTrace_4071287
  have hstable : (prefixWord ++ tailWord_4071287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071287).length < 2 ^ (prefixWord ++ tailWord_4071287).sum := by decide
  have hdescent : baseEnd_4071287 < baseStart_4071287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071445 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_4071445 : Nat := 118140960795 + 4071445 * 2 ^ 59
def prefixEnd_4071445 : Nat := 4983230072969 + 3 ^ 40 * 4071445 * 2
def baseEnd_4071445 : Nat := 1393738828896618790942181

theorem tailTrace_4071445 : CollatzResearch.WordTrace tailWord_4071445 prefixEnd_4071445 1393738828896618790942181 := by
  unfold tailWord_4071445
  simp only [CollatzResearch.WordTrace]
  refine ⟨148497798734857587291671789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98998532489905058194447859 148497798734857587291671789)
  ·
    refine ⟨55686674525571595234376921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148497798734857587291671789 55686674525571595234376921)
    ·
      refine ⟨41765005894178696425782691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55686674525571595234376921 41765005894178696425782691)
      ·
        refine ⟨62647508841268044638674037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41765005894178696425782691 62647508841268044638674037)
        ·
          refine ⟨5873203953868879184875691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62647508841268044638674037 5873203953868879184875691)
          ·
            refine ⟨8809805930803318777313537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873203953868879184875691 8809805930803318777313537)
            ·
              refine ⟨6607354448102489082985153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8809805930803318777313537 6607354448102489082985153)
              ·
                refine ⟨4955515836076866812238865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607354448102489082985153 4955515836076866812238865)
                ·
                  refine ⟨3716636877057650109179149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955515836076866812238865 3716636877057650109179149)
                  ·
                    refine ⟨1393738828896618790942181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716636877057650109179149 1393738828896618790942181)
                    ·
                      rfl

theorem cell22_4071445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_4071445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071445 prefixEnd_4071445 := by exact prefixLift 4071445
  have htrace : WordTrace (prefixWord ++ tailWord_4071445) baseStart_4071445 baseEnd_4071445 := by
    simpa [prefixWord, tailWord_4071445, baseEnd_4071445] using wordTrace_append hprefix tailTrace_4071445
  have hstable : (prefixWord ++ tailWord_4071445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071445).length < 2 ^ (prefixWord ++ tailWord_4071445).sum := by decide
  have hdescent : baseEnd_4071445 < baseStart_4071445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071447 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 4]
def baseStart_4071447 : Nat := 118140960795 + 4071447 * 2 ^ 59
def prefixEnd_4071447 : Nat := 4983230072969 + 3 ^ 40 * 4071447 * 2
def baseEnd_4071447 : Nat := 464579837845830484130725

theorem tailTrace_4071447 : CollatzResearch.WordTrace tailWord_4071447 prefixEnd_4071447 464579837845830484130725 := by
  unfold tailWord_4071447
  simp only [CollatzResearch.WordTrace]
  refine ⟨148497871680850341633244595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98998581120566894422163063 148497871680850341633244595)
  ·
    refine ⟨222746807521275512449866893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148497871680850341633244595 222746807521275512449866893)
    ·
      refine ⟨83530052820478317168700085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222746807521275512449866893 83530052820478317168700085)
      ·
        refine ⟨7830942451919842234565633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83530052820478317168700085 7830942451919842234565633)
        ·
          refine ⟨5873206838939881675924225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830942451919842234565633 5873206838939881675924225)
          ·
            refine ⟨4404905129204911256943169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873206838939881675924225 4404905129204911256943169)
            ·
              refine ⟨3303678846903683442707377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404905129204911256943169 3303678846903683442707377)
              ·
                refine ⟨2477759135177762582030533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303678846903683442707377 2477759135177762582030533)
                ·
                  refine ⟨464579837845830484130725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477759135177762582030533 464579837845830484130725)
                  ·
                    rfl

theorem cell22_4071447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 4].length) (baseStart_4071447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071447 prefixEnd_4071447 := by exact prefixLift 4071447
  have htrace : WordTrace (prefixWord ++ tailWord_4071447) baseStart_4071447 baseEnd_4071447 := by
    simpa [prefixWord, tailWord_4071447, baseEnd_4071447] using wordTrace_append hprefix tailTrace_4071447
  have hstable : (prefixWord ++ tailWord_4071447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071447).length < 2 ^ (prefixWord ++ tailWord_4071447).sum := by decide
  have hdescent : baseEnd_4071447 < baseStart_4071447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071473 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_4071473 : Nat := 118140960795 + 4071473 * 2 ^ 59
def prefixEnd_4071473 : Nat := 4983230072969 + 3 ^ 40 * 4071473 * 2
def baseEnd_4071473 : Nat := 1393748413868836051242095

theorem tailTrace_4071473 : CollatzResearch.WordTrace tailWord_4071473 prefixEnd_4071473 1393748413868836051242095 := by
  unfold tailWord_4071473
  simp only [CollatzResearch.WordTrace]
  refine ⟨148498819978756148073691073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98999213319170765382460715 148498819978756148073691073)
  ·
    refine ⟨111374114984067111055268305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148498819978756148073691073 111374114984067111055268305)
    ·
      refine ⟨83530586238050333291451229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111374114984067111055268305 83530586238050333291451229)
      ·
        refine ⟨31323969839268874984294211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83530586238050333291451229 31323969839268874984294211)
        ·
          refine ⟨46985954758903312476441317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31323969839268874984294211 46985954758903312476441317)
          ·
            refine ⟨8809866517294371089332747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46985954758903312476441317 8809866517294371089332747)
            ·
              refine ⟨13214799775941556633999121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8809866517294371089332747 13214799775941556633999121)
              ·
                refine ⟨9911099831956167475499341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13214799775941556633999121 9911099831956167475499341)
                ·
                  refine ⟨3716662436983562803312253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9911099831956167475499341 3716662436983562803312253)
                  ·
                    refine ⟨1393748413868836051242095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716662436983562803312253 1393748413868836051242095)
                    ·
                      rfl

theorem cell22_4071473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_4071473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071473 prefixEnd_4071473 := by exact prefixLift 4071473
  have htrace : WordTrace (prefixWord ++ tailWord_4071473) baseStart_4071473 baseEnd_4071473 := by
    simpa [prefixWord, tailWord_4071473, baseEnd_4071473] using wordTrace_append hprefix tailTrace_4071473
  have hstable : (prefixWord ++ tailWord_4071473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071473).length < 2 ^ (prefixWord ++ tailWord_4071473).sum := by decide
  have hdescent : baseEnd_4071473 < baseStart_4071473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071580 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_4071580 : Nat := 118140960795 + 4071580 * 2 ^ 59
def prefixEnd_4071580 : Nat := 4983230072969 + 3 ^ 40 * 4071580 * 2
def baseEnd_4071580 : Nat := 1393785042155523438816767

theorem tailTrace_4071580 : CollatzResearch.WordTrace tailWord_4071580 prefixEnd_4071580 1393785042155523438816767 := by
  unfold tailWord_4071580
  simp only [CollatzResearch.WordTrace]
  refine ⟨74251361294684252673918097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99001815059579003565224129 74251361294684252673918097)
  ·
    refine ⟨55688520971013189505438573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74251361294684252673918097 55688520971013189505438573)
    ·
      refine ⟨20883195364129946064539465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55688520971013189505438573 20883195364129946064539465)
      ·
        refine ⟨15662396523097459548404599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20883195364129946064539465 15662396523097459548404599)
        ·
          refine ⟨23493594784646189322606899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15662396523097459548404599 23493594784646189322606899)
          ·
            refine ⟨35240392176969283983910349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23493594784646189322606899 35240392176969283983910349)
            ·
              refine ⟨13215147066363481493966381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35240392176969283983910349 13215147066363481493966381)
              ·
                refine ⟨4955680149886305560237393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13215147066363481493966381 4955680149886305560237393)
                ·
                  refine ⟨3716760112414729170178045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955680149886305560237393 3716760112414729170178045)
                  ·
                    refine ⟨1393785042155523438816767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716760112414729170178045 1393785042155523438816767)
                    ·
                      rfl

theorem cell22_4071580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_4071580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071580 prefixEnd_4071580 := by exact prefixLift 4071580
  have htrace : WordTrace (prefixWord ++ tailWord_4071580) baseStart_4071580 baseEnd_4071580 := by
    simpa [prefixWord, tailWord_4071580, baseEnd_4071580] using wordTrace_append hprefix tailTrace_4071580
  have hstable : (prefixWord ++ tailWord_4071580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071580).length < 2 ^ (prefixWord ++ tailWord_4071580).sum := by decide
  have hdescent : baseEnd_4071580 < baseStart_4071580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071621 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 7]
def baseStart_4071621 : Nat := 118140960795 + 4071621 * 2 ^ 59
def prefixEnd_4071621 : Nat := 4983230072969 + 3 ^ 40 * 4071621 * 2
def baseEnd_4071621 : Nat := 464599692431137666180547

theorem tailTrace_4071621 : CollatzResearch.WordTrace tailWord_4071621 prefixEnd_4071621 464599692431137666180547 := by
  unfold tailWord_4071621
  simp only [CollatzResearch.WordTrace]
  refine ⟨148504217982219969350078717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99002811988146646233385811 148504217982219969350078717)
  ·
    refine ⟨55689081743332488506279519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148504217982219969350078717 55689081743332488506279519)
    ·
      refine ⟨83533622614998732759419279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55689081743332488506279519 83533622614998732759419279)
      ·
        refine ⟨125300433922498099139128919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83533622614998732759419279 125300433922498099139128919)
        ·
          refine ⟨187950650883747148708693379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125300433922498099139128919 187950650883747148708693379)
          ·
            refine ⟨281925976325620723063040069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187950650883747148708693379 281925976325620723063040069)
            ·
              refine ⟨52861120561053885574320013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281925976325620723063040069 52861120561053885574320013)
              ·
                refine ⟨19822920210395207090370005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52861120561053885574320013 19822920210395207090370005)
                ·
                  refine ⟨464599692431137666180547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19822920210395207090370005 464599692431137666180547)
                  ·
                    rfl

theorem cell22_4071621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_4071621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071621 prefixEnd_4071621 := by exact prefixLift 4071621
  have htrace : WordTrace (prefixWord ++ tailWord_4071621) baseStart_4071621 baseEnd_4071621 := by
    simpa [prefixWord, tailWord_4071621, baseEnd_4071621] using wordTrace_append hprefix tailTrace_4071621
  have hstable : (prefixWord ++ tailWord_4071621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071621).length < 2 ^ (prefixWord ++ tailWord_4071621).sum := by decide
  have hdescent : baseEnd_4071621 < baseStart_4071621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071683 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 6]
def baseStart_4071683 : Nat := 118140960795 + 4071683 * 2 ^ 59
def prefixEnd_4071683 : Nat := 4983230072969 + 3 ^ 40 * 4071683 * 2
def baseEnd_4071683 : Nat := 464606767053488501163817

theorem tailTrace_4071683 : CollatzResearch.WordTrace tailWord_4071683 prefixEnd_4071683 464606767053488501163817 := by
  unfold tailWord_4071683
  simp only [CollatzResearch.WordTrace]
  refine ⟨148506479307995353938835703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99004319538663569292557135 148506479307995353938835703)
  ·
    refine ⟨222759718961993030908253555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148506479307995353938835703 222759718961993030908253555)
    ·
      refine ⟨334139578442989546362380333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222759718961993030908253555 334139578442989546362380333)
      ·
        refine ⟨125302341916121079885892625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334139578442989546362380333 125302341916121079885892625)
        ·
          refine ⟨93976756437090809914419469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125302341916121079885892625 93976756437090809914419469)
          ·
            refine ⟨35241283663909053717907301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93976756437090809914419469 35241283663909053717907301)
            ·
              refine ⟨6607740686982947572107619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35241283663909053717907301 6607740686982947572107619)
              ·
                refine ⟨9911611030474421358161429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607740686982947572107619 9911611030474421358161429)
                ·
                  refine ⟨464606767053488501163817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9911611030474421358161429 464606767053488501163817)
                  ·
                    rfl

theorem cell22_4071683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 6].length) (baseStart_4071683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071683 prefixEnd_4071683 := by exact prefixLift 4071683
  have htrace : WordTrace (prefixWord ++ tailWord_4071683) baseStart_4071683 baseEnd_4071683 := by
    simpa [prefixWord, tailWord_4071683, baseEnd_4071683] using wordTrace_append hprefix tailTrace_4071683
  have hstable : (prefixWord ++ tailWord_4071683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071683).length < 2 ^ (prefixWord ++ tailWord_4071683).sum := by decide
  have hdescent : baseEnd_4071683 < baseStart_4071683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071713 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_4071713 : Nat := 118140960795 + 4071713 * 2 ^ 59
def prefixEnd_4071713 : Nat := 4983230072969 + 3 ^ 40 * 4071713 * 2
def baseEnd_4071713 : Nat := 1393830570773555425241359

theorem tailTrace_4071713 : CollatzResearch.WordTrace tailWord_4071713 prefixEnd_4071713 1393830570773555425241359 := by
  unfold tailWord_4071713
  simp only [CollatzResearch.WordTrace]
  refine ⟨148507573497886669062427793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99005048998591112708285195 148507573497886669062427793)
  ·
    refine ⟨111380680123415001796820845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148507573497886669062427793 111380680123415001796820845)
    ·
      refine ⟨41767755046280625673807817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111380680123415001796820845 41767755046280625673807817)
      ·
        refine ⟨31325816284710469255355863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41767755046280625673807817 31325816284710469255355863)
        ·
          refine ⟨46988724427065703883033795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31325816284710469255355863 46988724427065703883033795)
          ·
            refine ⟨70483086640598555824550693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46988724427065703883033795 70483086640598555824550693)
            ·
              refine ⟨13215578745112229217103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70483086640598555824550693 13215578745112229217103255)
              ·
                refine ⟨19823368117668343825654883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215578745112229217103255 19823368117668343825654883)
                ·
                  refine ⟨29735052176502515738482325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19823368117668343825654883 29735052176502515738482325)
                  ·
                    refine ⟨1393830570773555425241359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29735052176502515738482325 1393830570773555425241359)
                    ·
                      rfl

theorem cell22_4071713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_4071713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071713 prefixEnd_4071713 := by exact prefixLift 4071713
  have htrace : WordTrace (prefixWord ++ tailWord_4071713) baseStart_4071713 baseEnd_4071713 := by
    simpa [prefixWord, tailWord_4071713, baseEnd_4071713] using wordTrace_append hprefix tailTrace_4071713
  have hstable : (prefixWord ++ tailWord_4071713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071713).length < 2 ^ (prefixWord ++ tailWord_4071713).sum := by decide
  have hdescent : baseEnd_4071713 < baseStart_4071713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071732 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_4071732 : Nat := 118140960795 + 4071732 * 2 ^ 59
def prefixEnd_4071732 : Nat := 4983230072969 + 3 ^ 40 * 4071732 * 2
def baseEnd_4071732 : Nat := 1393837074861845709016301

theorem tailTrace_4071732 : CollatzResearch.WordTrace tailWord_4071732 prefixEnd_4071732 1393837074861845709016301 := by
  unfold tailWord_4071732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74254133242408917653684725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99005510989878556871579633 74254133242408917653684725)
  ·
    refine ⟨6961324991475836030032943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74254133242408917653684725 6961324991475836030032943)
    ·
      refine ⟨10441987487213754045049415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961324991475836030032943 10441987487213754045049415)
      ·
        refine ⟨15662981230820631067574123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10441987487213754045049415 15662981230820631067574123)
        ·
          refine ⟨23494471846230946601361185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15662981230820631067574123 23494471846230946601361185)
          ·
            refine ⟨17620853884673209951020889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23494471846230946601361185 17620853884673209951020889)
            ·
              refine ⟨13215640413504907463265667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620853884673209951020889 13215640413504907463265667)
              ·
                refine ⟨19823460620257361194898501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215640413504907463265667 19823460620257361194898501)
                ·
                  refine ⟨3716898866298255224043469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19823460620257361194898501 3716898866298255224043469)
                  ·
                    refine ⟨1393837074861845709016301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716898866298255224043469 1393837074861845709016301)
                    ·
                      rfl

theorem cell22_4071732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_4071732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071732 prefixEnd_4071732 := by exact prefixLift 4071732
  have htrace : WordTrace (prefixWord ++ tailWord_4071732) baseStart_4071732 baseEnd_4071732 := by
    simpa [prefixWord, tailWord_4071732, baseEnd_4071732] using wordTrace_append hprefix tailTrace_4071732
  have hstable : (prefixWord ++ tailWord_4071732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071732).length < 2 ^ (prefixWord ++ tailWord_4071732).sum := by decide
  have hdescent : baseEnd_4071732 < baseStart_4071732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071758 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_4071758 : Nat := 118140960795 + 4071758 * 2 ^ 59
def prefixEnd_4071758 : Nat := 4983230072969 + 3 ^ 40 * 4071758 * 2
def baseEnd_4071758 : Nat := 1393845975193190307866221

theorem tailTrace_4071758 : CollatzResearch.WordTrace tailWord_4071758 prefixEnd_4071758 1393845975193190307866221 := by
  unfold tailWord_4071758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18563651847840455218476991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99006143188482427831877285 18563651847840455218476991)
  ·
    refine ⟨27845477771760682827715487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18563651847840455218476991 27845477771760682827715487)
    ·
      refine ⟨41768216657641024241573231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27845477771760682827715487 41768216657641024241573231)
      ·
        refine ⟨62652324986461536362359847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41768216657641024241573231 62652324986461536362359847)
        ·
          refine ⟨93978487479692304543539771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62652324986461536362359847 93978487479692304543539771)
          ·
            refine ⟨140967731219538456815309657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93978487479692304543539771 140967731219538456815309657)
            ·
              refine ⟨105725798414653842611482243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140967731219538456815309657 105725798414653842611482243)
              ·
                refine ⟨158588697621980763917223365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105725798414653842611482243 158588697621980763917223365)
                ·
                  refine ⟨29735380804121393234479381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158588697621980763917223365 29735380804121393234479381)
                  ·
                    refine ⟨1393845975193190307866221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29735380804121393234479381 1393845975193190307866221)
                    ·
                      rfl

theorem cell22_4071758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_4071758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071758 prefixEnd_4071758 := by exact prefixLift 4071758
  have htrace : WordTrace (prefixWord ++ tailWord_4071758) baseStart_4071758 baseEnd_4071758 := by
    simpa [prefixWord, tailWord_4071758, baseEnd_4071758] using wordTrace_append hprefix tailTrace_4071758
  have hstable : (prefixWord ++ tailWord_4071758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071758).length < 2 ^ (prefixWord ++ tailWord_4071758).sum := by decide
  have hdescent : baseEnd_4071758 < baseStart_4071758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071794 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_4071794 : Nat := 118140960795 + 4071794 * 2 ^ 59
def prefixEnd_4071794 : Nat := 4983230072969 + 3 ^ 40 * 4071794 * 2
def baseEnd_4071794 : Nat := 1393858298728898213966111

theorem tailTrace_4071794 : CollatzResearch.WordTrace tailWord_4071794 prefixEnd_4071794 1393858298728898213966111 := by
  unfold tailWord_4071794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37127631952648304974031609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99007018540395479930750957 37127631952648304974031609)
  ·
    refine ⟨27845723964486228730523707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37127631952648304974031609 27845723964486228730523707)
    ·
      refine ⟨41768585946729343095785561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27845723964486228730523707 41768585946729343095785561)
      ·
        refine ⟨31326439460047007321839171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41768585946729343095785561 31326439460047007321839171)
        ·
          refine ⟨46989659190070510982758757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31326439460047007321839171 46989659190070510982758757)
          ·
            refine ⟨8810561098138220809267267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46989659190070510982758757 8810561098138220809267267)
            ·
              refine ⟨13215841647207331213900901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810561098138220809267267 13215841647207331213900901)
              ·
                refine ⟨2477970308851374602606419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13215841647207331213900901 2477970308851374602606419)
                ·
                  refine ⟨3716955463277061903909629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477970308851374602606419 3716955463277061903909629)
                  ·
                    refine ⟨1393858298728898213966111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716955463277061903909629 1393858298728898213966111)
                    ·
                      rfl

theorem cell22_4071794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_4071794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071794 prefixEnd_4071794 := by exact prefixLift 4071794
  have htrace : WordTrace (prefixWord ++ tailWord_4071794) baseStart_4071794 baseEnd_4071794 := by
    simpa [prefixWord, tailWord_4071794, baseEnd_4071794] using wordTrace_append hprefix tailTrace_4071794
  have hstable : (prefixWord ++ tailWord_4071794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071794).length < 2 ^ (prefixWord ++ tailWord_4071794).sum := by decide
  have hdescent : baseEnd_4071794 < baseStart_4071794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071805 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_4071805 : Nat := 118140960795 + 4071805 * 2 ^ 59
def prefixEnd_4071805 : Nat := 4983230072969 + 3 ^ 40 * 4071805 * 2
def baseEnd_4071805 : Nat := 1393862064253697851941077

theorem tailTrace_4071805 : CollatzResearch.WordTrace tailWord_4071805 prefixEnd_4071805 1393862064253697851941077 := by
  unfold tailWord_4071805
  simp only [CollatzResearch.WordTrace]
  refine ⟨148510929013553368774776869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99007286009035579183184579 148510929013553368774776869)
  ·
    refine ⟨27845799190041256645270663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148510929013553368774776869 27845799190041256645270663)
    ·
      refine ⟨41768698785061884967905995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27845799190041256645270663 41768698785061884967905995)
      ·
        refine ⟨62653048177592827451858993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41768698785061884967905995 62653048177592827451858993)
        ·
          refine ⟨46989786133194620588894245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62653048177592827451858993 46989786133194620588894245)
          ·
            refine ⟨8810584899973991360417671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46989786133194620588894245 8810584899973991360417671)
            ·
              refine ⟨13215877349960987040626507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810584899973991360417671 13215877349960987040626507)
              ·
                refine ⟨19823816024941480560939761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215877349960987040626507 19823816024941480560939761)
                ·
                  refine ⟨14867862018706110420704821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19823816024941480560939761 14867862018706110420704821)
                  ·
                    refine ⟨1393862064253697851941077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14867862018706110420704821 1393862064253697851941077)
                    ·
                      rfl

theorem cell22_4071805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_4071805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071805 prefixEnd_4071805 := by exact prefixLift 4071805
  have htrace : WordTrace (prefixWord ++ tailWord_4071805) baseStart_4071805 baseEnd_4071805 := by
    simpa [prefixWord, tailWord_4071805, baseEnd_4071805] using wordTrace_append hprefix tailTrace_4071805
  have hstable : (prefixWord ++ tailWord_4071805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071805).length < 2 ^ (prefixWord ++ tailWord_4071805).sum := by decide
  have hdescent : baseEnd_4071805 < baseStart_4071805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071820 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_4071820 : Nat := 118140960795 + 4071820 * 2 ^ 59
def prefixEnd_4071820 : Nat := 4983230072969 + 3 ^ 40 * 4071820 * 2
def baseEnd_4071820 : Nat := 1393867199060242812816031

theorem tailTrace_4071820 : CollatzResearch.WordTrace tailWord_4071820 prefixEnd_4071820 1393867199060242812816031 := by
  unfold tailWord_4071820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74255738054249513168286457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99007650738999350891048609 74255738054249513168286457)
  ·
    refine ⟨55691803540687134876214843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74255738054249513168286457 55691803540687134876214843)
    ·
      refine ⟨83537705311030702314322265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55691803540687134876214843 83537705311030702314322265)
      ·
        refine ⟨62653278983273026735741699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83537705311030702314322265 62653278983273026735741699)
        ·
          refine ⟨93979918474909540103612549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62653278983273026735741699 93979918474909540103612549)
          ·
            refine ⟨17621234714045538769427353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93979918474909540103612549 17621234714045538769427353)
            ·
              refine ⟨13215926035534154077070515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17621234714045538769427353 13215926035534154077070515)
              ·
                refine ⟨19823889053301231115605773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215926035534154077070515 19823889053301231115605773)
                ·
                  refine ⟨7433958394987961668352165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19823889053301231115605773 7433958394987961668352165)
                  ·
                    refine ⟨1393867199060242812816031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7433958394987961668352165 1393867199060242812816031)
                    ·
                      rfl

theorem cell22_4071820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_4071820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071820 prefixEnd_4071820 := by exact prefixLift 4071820
  have htrace : WordTrace (prefixWord ++ tailWord_4071820) baseStart_4071820 baseEnd_4071820 := by
    simpa [prefixWord, tailWord_4071820, baseEnd_4071820] using wordTrace_append hprefix tailTrace_4071820
  have hstable : (prefixWord ++ tailWord_4071820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071820).length < 2 ^ (prefixWord ++ tailWord_4071820).sum := by decide
  have hdescent : baseEnd_4071820 < baseStart_4071820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071841 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 5]
def baseStart_4071841 : Nat := 118140960795 + 4071841 * 2 ^ 59
def prefixEnd_4071841 : Nat := 4983230072969 + 3 ^ 40 * 4071841 * 2
def baseEnd_4071841 : Nat := 464624795929801919346989

theorem tailTrace_4071841 : CollatzResearch.WordTrace tailWord_4071841 prefixEnd_4071841 464624795929801919346989 := by
  unfold tailWord_4071841
  simp only [CollatzResearch.WordTrace]
  refine ⟨148512242041422946923087377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99008161360948631282058251 148512242041422946923087377)
  ·
    refine ⟨111384181531067210192315533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148512242041422946923087377 111384181531067210192315533)
    ·
      refine ⟨41769068074150203822118325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111384181531067210192315533 41769068074150203822118325)
      ·
        refine ⟨3915850131951581608323593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41769068074150203822118325 3915850131951581608323593)
        ·
          refine ⟨2936887598963686206242695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915850131951581608323593 2936887598963686206242695)
          ·
            refine ⟨4405331398445529309364043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936887598963686206242695 4405331398445529309364043)
            ·
              refine ⟨6607997097668293964046065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405331398445529309364043 6607997097668293964046065)
              ·
                refine ⟨4955997823251220473034549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607997097668293964046065 4955997823251220473034549)
                ·
                  refine ⟨464624795929801919346989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4955997823251220473034549 464624795929801919346989)
                  ·
                    rfl

theorem cell22_4071841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_4071841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071841 prefixEnd_4071841 := by exact prefixLift 4071841
  have htrace : WordTrace (prefixWord ++ tailWord_4071841) baseStart_4071841 baseEnd_4071841 := by
    simpa [prefixWord, tailWord_4071841, baseEnd_4071841] using wordTrace_append hprefix tailTrace_4071841
  have hstable : (prefixWord ++ tailWord_4071841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071841).length < 2 ^ (prefixWord ++ tailWord_4071841).sum := by decide
  have hdescent : baseEnd_4071841 < baseStart_4071841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071865 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_4071865 : Nat := 118140960795 + 4071865 * 2 ^ 59
def prefixEnd_4071865 : Nat := 4983230072969 + 3 ^ 40 * 4071865 * 2
def baseEnd_4071865 : Nat := 1393882603479877695440893

theorem tailTrace_4071865 : CollatzResearch.WordTrace tailWord_4071865 prefixEnd_4071865 1393882603479877695440893 := by
  unfold tailWord_4071865
  simp only [CollatzResearch.WordTrace]
  refine ⟨148513117393335999021961049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99008744928890666014640699 148513117393335999021961049)
  ·
    refine ⟨111384838045001999266470787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148513117393335999021961049 111384838045001999266470787)
    ·
      refine ⟨167077257067502998899706181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111384838045001999266470787 167077257067502998899706181)
      ·
        refine ⟨31326985700156812293694909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167077257067502998899706181 31326985700156812293694909)
        ·
          refine ⟨11747619637558804610135591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31326985700156812293694909 11747619637558804610135591)
          ·
            refine ⟨17621429456338206915203387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11747619637558804610135591 17621429456338206915203387)
            ·
              refine ⟨26432144184507310372805081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17621429456338206915203387 26432144184507310372805081)
              ·
                refine ⟨19824108138380482779603811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26432144184507310372805081 19824108138380482779603811)
                ·
                  refine ⟨29736162207570724169405717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19824108138380482779603811 29736162207570724169405717)
                  ·
                    refine ⟨1393882603479877695440893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29736162207570724169405717 1393882603479877695440893)
                    ·
                      rfl

theorem cell22_4071865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_4071865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071865 prefixEnd_4071865 := by exact prefixLift 4071865
  have htrace : WordTrace (prefixWord ++ tailWord_4071865) baseStart_4071865 baseEnd_4071865 := by
    simpa [prefixWord, tailWord_4071865, baseEnd_4071865] using wordTrace_append hprefix tailTrace_4071865
  have hstable : (prefixWord ++ tailWord_4071865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071865).length < 2 ^ (prefixWord ++ tailWord_4071865).sum := by decide
  have hdescent : baseEnd_4071865 < baseStart_4071865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071880 : List Nat := [2, 1, 3, 1, 3, 3, 1, 8]
def baseStart_4071880 : Nat := 118140960795 + 4071880 * 2 ^ 59
def prefixEnd_4071880 : Nat := 4983230072969 + 3 ^ 40 * 4071880 * 2
def baseEnd_4071880 : Nat := 154876415365158072923983

theorem tailTrace_4071880 : CollatzResearch.WordTrace tailWord_4071880 prefixEnd_4071880 154876415365158072923983 := by
  unfold tailWord_4071880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74256832244140828291878547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99009109658854437722504729 74256832244140828291878547)
  ·
    refine ⟨111385248366211242437817821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74256832244140828291878547 111385248366211242437817821)
    ·
      refine ⟨41769468137329215914181683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111385248366211242437817821 41769468137329215914181683)
      ·
        refine ⟨62654202205993823871272525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41769468137329215914181683 62654202205993823871272525)
        ·
          refine ⟨23495325827247683951727197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62654202205993823871272525 23495325827247683951727197)
          ·
            refine ⟨8810747185217881481897699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23495325827247683951727197 8810747185217881481897699)
            ·
              refine ⟨13216120777826822222846549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810747185217881481897699 13216120777826822222846549)
              ·
                refine ⟨154876415365158072923983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13216120777826822222846549 154876415365158072923983)
                ·
                  rfl

theorem cell22_4071880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_4071880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4071880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4071880 prefixEnd_4071880 := by exact prefixLift 4071880
  have htrace : WordTrace (prefixWord ++ tailWord_4071880) baseStart_4071880 baseEnd_4071880 := by
    simpa [prefixWord, tailWord_4071880, baseEnd_4071880] using wordTrace_append hprefix tailTrace_4071880
  have hstable : (prefixWord ++ tailWord_4071880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071880).length < 2 ^ (prefixWord ++ tailWord_4071880).sum := by decide
  have hdescent : baseEnd_4071880 < baseStart_4071880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072036 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_4072036 : Nat := 118140960795 + 4072036 * 2 ^ 59
def prefixEnd_4072036 : Nat := 4983230072969 + 3 ^ 40 * 4072036 * 2
def baseEnd_4072036 : Nat := 1393941140274490249415369

theorem tailTrace_4072036 : CollatzResearch.WordTrace tailWord_4072036 prefixEnd_4072036 1393941140274490249415369 := by
  unfold tailWord_4072036
  simp only [CollatzResearch.WordTrace]
  refine ⟨74259677137858247613217981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99012902850477663484290641 74259677137858247613217981)
  ·
    refine ⟨27847378926696842854956743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74259677137858247613217981 27847378926696842854956743)
    ·
      refine ⟨41771068390045264282435115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27847378926696842854956743 41771068390045264282435115)
      ·
        refine ⟨62656602585067896423652673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41771068390045264282435115 62656602585067896423652673)
        ·
          refine ⟨46992451938800922317739505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62656602585067896423652673 46992451938800922317739505)
          ·
            refine ⟨35244338954100691738304629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46992451938800922317739505 35244338954100691738304629)
            ·
              refine ⟨3304156776946939850466059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35244338954100691738304629 3304156776946939850466059)
              ·
                refine ⟨4956235165420409775699089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304156776946939850466059 4956235165420409775699089)
                ·
                  refine ⟨3717176374065307331774317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956235165420409775699089 3717176374065307331774317)
                  ·
                    refine ⟨1393941140274490249415369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717176374065307331774317 1393941140274490249415369)
                    ·
                      rfl

theorem cell22_4072036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_4072036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072036 prefixEnd_4072036 := by exact prefixLift 4072036
  have htrace : WordTrace (prefixWord ++ tailWord_4072036) baseStart_4072036 baseEnd_4072036 := by
    simpa [prefixWord, tailWord_4072036, baseEnd_4072036] using wordTrace_append hprefix tailTrace_4072036
  have hstable : (prefixWord ++ tailWord_4072036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072036).length < 2 ^ (prefixWord ++ tailWord_4072036).sum := by decide
  have hdescent : baseEnd_4072036 < baseStart_4072036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072154 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_4072154 : Nat := 118140960795 + 4072154 * 2 ^ 59
def prefixEnd_4072154 : Nat := 4983230072969 + 3 ^ 40 * 4072154 * 2
def baseEnd_4072154 : Nat := 1393981534085977274965007

theorem tailTrace_4072154 : CollatzResearch.WordTrace tailWord_4072154 prefixEnd_4072154 1393981534085977274965007 := by
  unfold tailWord_4072154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37130914522322250344807879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99015772059526000919487677 37130914522322250344807879)
  ·
    refine ⟨55696371783483375517211819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37130914522322250344807879 55696371783483375517211819)
    ·
      refine ⟨83544557675225063275817729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55696371783483375517211819 83544557675225063275817729)
      ·
        refine ⟨62658418256418797456863297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83544557675225063275817729 62658418256418797456863297)
        ·
          refine ⟨46993813692314098092647473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62658418256418797456863297 46993813692314098092647473)
          ·
            refine ⟨35245360269235573569485605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46993813692314098092647473 35245360269235573569485605)
            ·
              refine ⟨6608505050481670044278551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35245360269235573569485605 6608505050481670044278551)
              ·
                refine ⟨9912757575722505066417827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608505050481670044278551 9912757575722505066417827)
                ·
                  refine ⟨14869136363583757599626741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912757575722505066417827 14869136363583757599626741)
                  ·
                    refine ⟨1393981534085977274965007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14869136363583757599626741 1393981534085977274965007)
                    ·
                      rfl

theorem cell22_4072154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_4072154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072154 prefixEnd_4072154 := by exact prefixLift 4072154
  have htrace : WordTrace (prefixWord ++ tailWord_4072154) baseStart_4072154 baseEnd_4072154 := by
    simpa [prefixWord, tailWord_4072154, baseEnd_4072154] using wordTrace_append hprefix tailTrace_4072154
  have hstable : (prefixWord ++ tailWord_4072154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072154).length < 2 ^ (prefixWord ++ tailWord_4072154).sum := by decide
  have hdescent : baseEnd_4072154 < baseStart_4072154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072156 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_4072156 : Nat := 118140960795 + 4072156 * 2 ^ 59
def prefixEnd_4072156 : Nat := 4983230072969 + 3 ^ 40 * 4072156 * 2
def baseEnd_4072156 : Nat := 464660739575616645471667

theorem tailTrace_4072156 : CollatzResearch.WordTrace tailWord_4072156 prefixEnd_4072156 464660739575616645471667 := by
  unfold tailWord_4072156
  simp only [CollatzResearch.WordTrace]
  refine ⟨74261865517640877860402161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99015820690187837147202881 74261865517640877860402161)
  ·
    refine ⟨55696399138230658395301621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74261865517640877860402161 55696399138230658395301621)
    ·
      refine ⟨5221537419209124224559527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55696399138230658395301621 5221537419209124224559527)
      ·
        refine ⟨7832306128813686336839291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221537419209124224559527 7832306128813686336839291)
        ·
          refine ⟨11748459193220529505258937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832306128813686336839291 11748459193220529505258937)
          ·
            refine ⟨8811344394915397128944203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11748459193220529505258937 8811344394915397128944203)
            ·
              refine ⟨13217016592373095693416305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811344394915397128944203 13217016592373095693416305)
              ·
                refine ⟨9912762444279821770062229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13217016592373095693416305 9912762444279821770062229)
                ·
                  refine ⟨464660739575616645471667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9912762444279821770062229 464660739575616645471667)
                  ·
                    rfl

theorem cell22_4072156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_4072156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072156 prefixEnd_4072156 := by exact prefixLift 4072156
  have htrace : WordTrace (prefixWord ++ tailWord_4072156) baseStart_4072156 baseEnd_4072156 := by
    simpa [prefixWord, tailWord_4072156, baseEnd_4072156] using wordTrace_append hprefix tailTrace_4072156
  have hstable : (prefixWord ++ tailWord_4072156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072156).length < 2 ^ (prefixWord ++ tailWord_4072156).sum := by decide
  have hdescent : baseEnd_4072156 < baseStart_4072156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072169 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_4072169 : Nat := 118140960795 + 4072169 * 2 ^ 59
def prefixEnd_4072169 : Nat := 4983230072969 + 3 ^ 40 * 4072169 * 2
def baseEnd_4072169 : Nat := 1393986668892522235839961

theorem tailTrace_4072169 : CollatzResearch.WordTrace tailWord_4072169 prefixEnd_4072169 1393986668892522235839961 := by
  unfold tailWord_4072169
  simp only [CollatzResearch.WordTrace]
  refine ⟨148524205184234658941027561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99016136789489772627351707 148524205184234658941027561)
  ·
    refine ⟨111393153888175994205770671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148524205184234658941027561 111393153888175994205770671)
    ·
      refine ⟨167089730832263991308656007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111393153888175994205770671 167089730832263991308656007)
      ·
        refine ⟨250634596248395986962984011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167089730832263991308656007 250634596248395986962984011)
        ·
          refine ⟨375951894372593980444476017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250634596248395986962984011 375951894372593980444476017)
          ·
            refine ⟨281963920779445485333357013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375951894372593980444476017 281963920779445485333357013)
            ·
              refine ⟨6608529393268253562500555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281963920779445485333357013 6608529393268253562500555)
              ·
                refine ⟨9912794089902380343750833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608529393268253562500555 9912794089902380343750833)
                ·
                  refine ⟨7434595567426785257813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9912794089902380343750833 7434595567426785257813125)
                  ·
                    refine ⟨1393986668892522235839961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7434595567426785257813125 1393986668892522235839961)
                    ·
                      rfl

theorem cell22_4072169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_4072169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072169 prefixEnd_4072169 := by exact prefixLift 4072169
  have htrace : WordTrace (prefixWord ++ tailWord_4072169) baseStart_4072169 baseEnd_4072169 := by
    simpa [prefixWord, tailWord_4072169, baseEnd_4072169] using wordTrace_append hprefix tailTrace_4072169
  have hstable : (prefixWord ++ tailWord_4072169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072169).length < 2 ^ (prefixWord ++ tailWord_4072169).sum := by decide
  have hdescent : baseEnd_4072169 < baseStart_4072169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072188 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_4072188 : Nat := 118140960795 + 4072188 * 2 ^ 59
def prefixEnd_4072188 : Nat := 4983230072969 + 3 ^ 40 * 4072188 * 2
def baseEnd_4072188 : Nat := 1393993172980812519614903

theorem tailTrace_4072188 : CollatzResearch.WordTrace tailWord_4072188 prefixEnd_4072188 1393993172980812519614903 := by
  unfold tailWord_4072188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74262449085582912592984609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99016598780777216790646145 74262449085582912592984609)
  ·
    refine ⟨55696836814187184444738457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74262449085582912592984609 55696836814187184444738457)
    ·
      refine ⟨41772627610640388333553843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55696836814187184444738457 41772627610640388333553843)
      ·
        refine ⟨62658941415960582500330765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41772627610640388333553843 62658941415960582500330765)
        ·
          refine ⟨23497103030985218437624037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62658941415960582500330765 23497103030985218437624037)
          ·
            refine ⟨4405706818309728457054507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23497103030985218437624037 4405706818309728457054507)
            ·
              refine ⟨6608560227464592685581761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405706818309728457054507 6608560227464592685581761)
              ·
                refine ⟨4956420170598444514186321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6608560227464592685581761 4956420170598444514186321)
                ·
                  refine ⟨3717315127948833385639741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956420170598444514186321 3717315127948833385639741)
                  ·
                    refine ⟨1393993172980812519614903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717315127948833385639741 1393993172980812519614903)
                    ·
                      rfl

theorem cell22_4072188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_4072188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072188 prefixEnd_4072188 := by exact prefixLift 4072188
  have htrace : WordTrace (prefixWord ++ tailWord_4072188) baseStart_4072188 baseEnd_4072188 := by
    simpa [prefixWord, tailWord_4072188, baseEnd_4072188] using wordTrace_append hprefix tailTrace_4072188
  have hstable : (prefixWord ++ tailWord_4072188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072188).length < 2 ^ (prefixWord ++ tailWord_4072188).sum := by decide
  have hdescent : baseEnd_4072188 < baseStart_4072188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072197 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_4072197 : Nat := 118140960795 + 4072197 * 2 ^ 59
def prefixEnd_4072197 : Nat := 4983230072969 + 3 ^ 40 * 4072197 * 2
def baseEnd_4072197 : Nat := 1393996253864739496139875

theorem tailTrace_4072197 : CollatzResearch.WordTrace tailWord_4072197 prefixEnd_4072197 1393996253864739496139875 := by
  unfold tailWord_4072197
  simp only [CollatzResearch.WordTrace]
  refine ⟨148525226428133219723046845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99016817618755479815364563 148525226428133219723046845)
  ·
    refine ⟨55696959910549957396142567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148525226428133219723046845 55696959910549957396142567)
    ·
      refine ⟨83545439865824936094213851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55696959910549957396142567 83545439865824936094213851)
      ·
        refine ⟨125318159798737404141320777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83545439865824936094213851 125318159798737404141320777)
        ·
          refine ⟨93988619849053053105990583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125318159798737404141320777 93988619849053053105990583)
          ·
            refine ⟨140982929773579579658985875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93988619849053053105990583 140982929773579579658985875)
            ·
              refine ⟨211474394660369369488478813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140982929773579579658985875 211474394660369369488478813)
              ·
                refine ⟨79302897997638513558179555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211474394660369369488478813 79302897997638513558179555)
                ·
                  refine ⟨118954346996457770337269333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79302897997638513558179555 118954346996457770337269333)
                  ·
                    refine ⟨1393996253864739496139875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118954346996457770337269333 1393996253864739496139875)
                    ·
                      rfl

theorem cell22_4072197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_4072197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072197 prefixEnd_4072197 := by exact prefixLift 4072197
  have htrace : WordTrace (prefixWord ++ tailWord_4072197) baseStart_4072197 baseEnd_4072197 := by
    simpa [prefixWord, tailWord_4072197, baseEnd_4072197] using wordTrace_append hprefix tailTrace_4072197
  have hstable : (prefixWord ++ tailWord_4072197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072197).length < 2 ^ (prefixWord ++ tailWord_4072197).sum := by decide
  have hdescent : baseEnd_4072197 < baseStart_4072197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072250 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_4072250 : Nat := 118140960795 + 4072250 * 2 ^ 59
def prefixEnd_4072250 : Nat := 4983230072969 + 3 ^ 40 * 4072250 * 2
def baseEnd_4072250 : Nat := 1394014396847865024564713

theorem tailTrace_4072250 : CollatzResearch.WordTrace tailWord_4072250 prefixEnd_4072250 1394014396847865024564713 := by
  unfold tailWord_4072250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37131789874235302443681551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99018106331294139849817469 37131789874235302443681551)
  ·
    refine ⟨55697684811352953665522327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37131789874235302443681551 55697684811352953665522327)
    ·
      refine ⟨83546527217029430498283491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55697684811352953665522327 83546527217029430498283491)
      ·
        refine ⟨125319790825544145747425237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83546527217029430498283491 125319790825544145747425237)
        ·
          refine ⟨2937182597473690915955279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125319790825544145747425237 2937182597473690915955279)
          ·
            refine ⟨4405773896210536373932919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937182597473690915955279 4405773896210536373932919)
            ·
              refine ⟨6608660844315804560899379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405773896210536373932919 6608660844315804560899379)
              ·
                refine ⟨9912991266473706841349069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608660844315804560899379 9912991266473706841349069)
                ·
                  refine ⟨3717371724927640065505901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9912991266473706841349069 3717371724927640065505901)
                  ·
                    refine ⟨1394014396847865024564713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717371724927640065505901 1394014396847865024564713)
                    ·
                      rfl

theorem cell22_4072250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_4072250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072250 prefixEnd_4072250 := by exact prefixLift 4072250
  have htrace : WordTrace (prefixWord ++ tailWord_4072250) baseStart_4072250 baseEnd_4072250 := by
    simpa [prefixWord, tailWord_4072250, baseEnd_4072250] using wordTrace_append hprefix tailTrace_4072250
  have hstable : (prefixWord ++ tailWord_4072250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072250).length < 2 ^ (prefixWord ++ tailWord_4072250).sum := by decide
  have hdescent : baseEnd_4072250 < baseStart_4072250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072259 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_4072259 : Nat := 118140960795 + 4072259 * 2 ^ 59
def prefixEnd_4072259 : Nat := 4983230072969 + 3 ^ 40 * 4072259 * 2
def baseEnd_4072259 : Nat := 1394017477731792001089685

theorem tailTrace_4072259 : CollatzResearch.WordTrace tailWord_4072259 prefixEnd_4072259 1394017477731792001089685 := by
  unfold tailWord_4072259
  simp only [CollatzResearch.WordTrace]
  refine ⟨148527487753908604311803831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99018325169272402874535887 148527487753908604311803831)
  ·
    refine ⟨222791231630862906467705747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148527487753908604311803831 222791231630862906467705747)
    ·
      refine ⟨334186847446294359701558621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222791231630862906467705747 334186847446294359701558621)
      ·
        refine ⟨125320067792360384888084483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334186847446294359701558621 125320067792360384888084483)
        ·
          refine ⟨187980101688540577332126725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125320067792360384888084483 187980101688540577332126725)
          ·
            refine ⟨35246269066601358249773761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187980101688540577332126725 35246269066601358249773761)
            ·
              refine ⟨26434701799951018687330321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35246269066601358249773761 26434701799951018687330321)
              ·
                refine ⟨19826026349963264015497741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26434701799951018687330321 19826026349963264015497741)
                ·
                  refine ⟨7434759881236224005811653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19826026349963264015497741 7434759881236224005811653)
                  ·
                    refine ⟨1394017477731792001089685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7434759881236224005811653 1394017477731792001089685)
                    ·
                      rfl

theorem cell22_4072259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_4072259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072259 prefixEnd_4072259 := by exact prefixLift 4072259
  have htrace : WordTrace (prefixWord ++ tailWord_4072259) baseStart_4072259 baseEnd_4072259 := by
    simpa [prefixWord, tailWord_4072259, baseEnd_4072259] using wordTrace_append hprefix tailTrace_4072259
  have hstable : (prefixWord ++ tailWord_4072259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072259).length < 2 ^ (prefixWord ++ tailWord_4072259).sum := by decide
  have hdescent : baseEnd_4072259 < baseStart_4072259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072274 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_4072274 : Nat := 118140960795 + 4072274 * 2 ^ 59
def prefixEnd_4072274 : Nat := 4983230072969 + 3 ^ 40 * 4072274 * 2
def baseEnd_4072274 : Nat := 464674204179445653988213

theorem tailTrace_4072274 : CollatzResearch.WordTrace tailWord_4072274 prefixEnd_4072274 464674204179445653988213 := by
  unfold tailWord_4072274
  simp only [CollatzResearch.WordTrace]
  refine ⟨37132008712213565468399969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99018689899236174582399917 37132008712213565468399969)
  ·
    refine ⟨27849006534160174101299977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37132008712213565468399969 27849006534160174101299977)
    ·
      refine ⟨20886754900620130575974983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27849006534160174101299977 20886754900620130575974983)
      ·
        refine ⟨31330132350930195863962475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20886754900620130575974983 31330132350930195863962475)
        ·
          refine ⟨46995198526395293795943713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31330132350930195863962475 46995198526395293795943713)
          ·
            refine ⟨35246398894796470346957785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46995198526395293795943713 35246398894796470346957785)
            ·
              refine ⟨26434799171097352760218339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35246398894796470346957785 26434799171097352760218339)
              ·
                refine ⟨39652198756646029140327509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26434799171097352760218339 39652198756646029140327509)
                ·
                  refine ⟨464674204179445653988213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39652198756646029140327509 464674204179445653988213)
                  ·
                    rfl

theorem cell22_4072274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_4072274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072274 prefixEnd_4072274 := by exact prefixLift 4072274
  have htrace : WordTrace (prefixWord ++ tailWord_4072274) baseStart_4072274 baseEnd_4072274 := by
    simpa [prefixWord, tailWord_4072274, baseEnd_4072274] using wordTrace_append hprefix tailTrace_4072274
  have hstable : (prefixWord ++ tailWord_4072274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072274).length < 2 ^ (prefixWord ++ tailWord_4072274).sum := by decide
  have hdescent : baseEnd_4072274 < baseStart_4072274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072306 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_4072306 : Nat := 118140960795 + 4072306 * 2 ^ 59
def prefixEnd_4072306 : Nat := 4983230072969 + 3 ^ 40 * 4072306 * 2
def baseEnd_4072306 : Nat := 1394033566792299545164541

theorem tailTrace_4072306 : CollatzResearch.WordTrace tailWord_4072306 prefixEnd_4072306 1394033566792299545164541 := by
  unfold tailWord_4072306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37132300496184582834691193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99019467989825554225843181 37132300496184582834691193)
  ·
    refine ⟨27849225372138437126018395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37132300496184582834691193 27849225372138437126018395)
    ·
      refine ⟨41773838058207655689027593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27849225372138437126018395 41773838058207655689027593)
      ·
        refine ⟨31330378543655741766770695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41773838058207655689027593 31330378543655741766770695)
        ·
          refine ⟨46995567815483612650156043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31330378543655741766770695 46995567815483612650156043)
          ·
            refine ⟨70493351723225418975234065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46995567815483612650156043 70493351723225418975234065)
            ·
              refine ⟨52870013792419064231425549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70493351723225418975234065 52870013792419064231425549)
              ·
                refine ⟨19826255172157149086784581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52870013792419064231425549 19826255172157149086784581)
                ·
                  refine ⟨3717422844779465453772109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19826255172157149086784581 3717422844779465453772109)
                  ·
                    refine ⟨1394033566792299545164541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717422844779465453772109 1394033566792299545164541)
                    ·
                      rfl

theorem cell22_4072306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_4072306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072306 prefixEnd_4072306 := by exact prefixLift 4072306
  have htrace : WordTrace (prefixWord ++ tailWord_4072306) baseStart_4072306 baseEnd_4072306 := by
    simpa [prefixWord, tailWord_4072306, baseEnd_4072306] using wordTrace_append hprefix tailTrace_4072306
  have hstable : (prefixWord ++ tailWord_4072306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072306).length < 2 ^ (prefixWord ++ tailWord_4072306).sum := by decide
  have hdescent : baseEnd_4072306 < baseStart_4072306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072319 : List Nat := [1, 1, 2, 2, 1, 1, 7, 7]
def baseStart_4072319 : Nat := 118140960795 + 4072319 * 2 ^ 59
def prefixEnd_4072319 : Nat := 4983230072969 + 3 ^ 40 * 4072319 * 2
def baseEnd_4072319 : Nat := 154893112995330204954389

theorem tailTrace_4072319 : CollatzResearch.WordTrace tailWord_4072319 prefixEnd_4072319 154893112995330204954389 := by
  unfold tailWord_4072319
  simp only [CollatzResearch.WordTrace]
  refine ⟨148529676133691234558988011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99019784089127489705992007 148529676133691234558988011)
  ·
    refine ⟨222794514200536851838482017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148529676133691234558988011 222794514200536851838482017)
    ·
      refine ⟨167095885650402638878861513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222794514200536851838482017 167095885650402638878861513)
      ·
        refine ⟨125321914237801979159146135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167095885650402638878861513 125321914237801979159146135)
        ·
          refine ⟨187982871356702968738719203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125321914237801979159146135 187982871356702968738719203)
          ·
            refine ⟨281974307035054453108078805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187982871356702968738719203 281974307035054453108078805)
            ·
              refine ⟨6608772821134088744720597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281974307035054453108078805 6608772821134088744720597)
              ·
                refine ⟨154893112995330204954389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6608772821134088744720597 154893112995330204954389)
                ·
                  rfl

theorem cell22_4072319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 7].length) (baseStart_4072319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072319 prefixEnd_4072319 := by exact prefixLift 4072319
  have htrace : WordTrace (prefixWord ++ tailWord_4072319) baseStart_4072319 baseEnd_4072319 := by
    simpa [prefixWord, tailWord_4072319, baseEnd_4072319] using wordTrace_append hprefix tailTrace_4072319
  have hstable : (prefixWord ++ tailWord_4072319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072319).length < 2 ^ (prefixWord ++ tailWord_4072319).sum := by decide
  have hdescent : baseEnd_4072319 < baseStart_4072319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072338 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4072338 : Nat := 118140960795 + 4072338 * 2 ^ 59
def prefixEnd_4072338 : Nat := 4983230072969 + 3 ^ 40 * 4072338 * 2
def baseEnd_4072338 : Nat := 1394044521046262128364443

theorem tailTrace_4072338 : CollatzResearch.WordTrace tailWord_4072338 prefixEnd_4072338 1394044521046262128364443 := by
  unfold tailWord_4072338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37132592280155600200982417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99020246080414933869286445 37132592280155600200982417)
  ·
    refine ⟨27849444210116700150736813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37132592280155600200982417 27849444210116700150736813)
    ·
      refine ⟨10443541578793762556526305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27849444210116700150736813 10443541578793762556526305)
      ·
        refine ⟨7832656184095321917394729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10443541578793762556526305 7832656184095321917394729)
        ·
          refine ⟨5874492138071491438046047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7832656184095321917394729 5874492138071491438046047)
          ·
            refine ⟨8811738207107237157069071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874492138071491438046047 8811738207107237157069071)
            ·
              refine ⟨13217607310660855735603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811738207107237157069071 13217607310660855735603607)
              ·
                refine ⟨19826410965991283603405411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13217607310660855735603607 19826410965991283603405411)
                ·
                  refine ⟨29739616448986925405108117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19826410965991283603405411 29739616448986925405108117)
                  ·
                    refine ⟨1394044521046262128364443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29739616448986925405108117 1394044521046262128364443)
                    ·
                      rfl

theorem cell22_4072338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4072338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072338 prefixEnd_4072338 := by exact prefixLift 4072338
  have htrace : WordTrace (prefixWord ++ tailWord_4072338) baseStart_4072338 baseEnd_4072338 := by
    simpa [prefixWord, tailWord_4072338, baseEnd_4072338] using wordTrace_append hprefix tailTrace_4072338
  have hstable : (prefixWord ++ tailWord_4072338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072338).length < 2 ^ (prefixWord ++ tailWord_4072338).sum := by decide
  have hdescent : baseEnd_4072338 < baseStart_4072338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072342 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4072342 : Nat := 118140960795 + 4072342 * 2 ^ 59
def prefixEnd_4072342 : Nat := 4983230072969 + 3 ^ 40 * 4072342 * 2
def baseEnd_4072342 : Nat := 464681963442669150421477

theorem tailTrace_4072342 : CollatzResearch.WordTrace tailWord_4072342 prefixEnd_4072342 464681963442669150421477 := by
  unfold tailWord_4072342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283157188287994342942205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99020343341738606324716853 9283157188287994342942205)
  ·
    refine ⟨3481183945607997878603327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9283157188287994342942205 3481183945607997878603327)
    ·
      refine ⟨5221775918411996817904991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3481183945607997878603327 5221775918411996817904991)
      ·
        refine ⟨7832663877617995226857487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221775918411996817904991 7832663877617995226857487)
        ·
          refine ⟨11748995816426992840286231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832663877617995226857487 11748995816426992840286231)
          ·
            refine ⟨17623493724640489260429347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11748995816426992840286231 17623493724640489260429347)
            ·
              refine ⟨26435240586960733890644021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623493724640489260429347 26435240586960733890644021)
              ·
                refine ⟨2478303805027568802247877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26435240586960733890644021 2478303805027568802247877)
                ·
                  refine ⟨464681963442669150421477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2478303805027568802247877 464681963442669150421477)
                  ·
                    rfl

theorem cell22_4072342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4072342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072342 prefixEnd_4072342 := by exact prefixLift 4072342
  have htrace : WordTrace (prefixWord ++ tailWord_4072342) baseStart_4072342 baseEnd_4072342 := by
    simpa [prefixWord, tailWord_4072342, baseEnd_4072342] using wordTrace_append hprefix tailTrace_4072342
  have hstable : (prefixWord ++ tailWord_4072342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072342).length < 2 ^ (prefixWord ++ tailWord_4072342).sum := by decide
  have hdescent : baseEnd_4072342 < baseStart_4072342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072364 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_4072364 : Nat := 118140960795 + 4072364 * 2 ^ 59
def prefixEnd_4072364 : Nat := 4983230072969 + 3 ^ 40 * 4072364 * 2
def baseEnd_4072364 : Nat := 464684473792535575738121

theorem tailTrace_4072364 : CollatzResearch.WordTrace tailWord_4072364 prefixEnd_4072364 464684473792535575738121 := by
  unfold tailWord_4072364
  simp only [CollatzResearch.WordTrace]
  refine ⟨74265658709264103622188073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99020878279018804829584097 74265658709264103622188073)
  ·
    refine ⟨55699244031948077716641055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74265658709264103622188073 55699244031948077716641055)
    ·
      refine ⟨83548866047922116574961583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55699244031948077716641055 83548866047922116574961583)
      ·
        refine ⟨125323299071883174862442375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83548866047922116574961583 125323299071883174862442375)
        ·
          refine ⟨187984948607824762293663563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125323299071883174862442375 187984948607824762293663563)
          ·
            refine ⟨281977422911737143440495345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187984948607824762293663563 281977422911737143440495345)
            ·
              refine ⟨211483067183802857580371509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281977422911737143440495345 211483067183802857580371509)
              ·
                refine ⟨19826537548481517898159829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211483067183802857580371509 19826537548481517898159829)
                ·
                  refine ⟨464684473792535575738121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19826537548481517898159829 464684473792535575738121)
                  ·
                    rfl

theorem cell22_4072364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_4072364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072364 prefixEnd_4072364 := by exact prefixLift 4072364
  have htrace : WordTrace (prefixWord ++ tailWord_4072364) baseStart_4072364 baseEnd_4072364 := by
    simpa [prefixWord, tailWord_4072364, baseEnd_4072364] using wordTrace_append hprefix tailTrace_4072364
  have hstable : (prefixWord ++ tailWord_4072364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072364).length < 2 ^ (prefixWord ++ tailWord_4072364).sum := by decide
  have hdescent : baseEnd_4072364 < baseStart_4072364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072374 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4072374 : Nat := 118140960795 + 4072374 * 2 ^ 59
def prefixEnd_4072374 : Nat := 4983230072969 + 3 ^ 40 * 4072374 * 2
def baseEnd_4072374 : Nat := 1394056844581970034464333

theorem tailTrace_4072374 : CollatzResearch.WordTrace tailWord_4072374 prefixEnd_4072374 1394056844581970034464333 := by
  unfold tailWord_4072374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283230134280748684515011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99021121432327985968160117 9283230134280748684515011)
  ·
    refine ⟨13924845201421123026772517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9283230134280748684515011 13924845201421123026772517)
    ·
      refine ⟨2610908475266460567519847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13924845201421123026772517 2610908475266460567519847)
      ·
        refine ⟨3916362712899690851279771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610908475266460567519847 3916362712899690851279771)
        ·
          refine ⟨5874544069349536276919657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916362712899690851279771 5874544069349536276919657)
          ·
            refine ⟨4405908052012152207689743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5874544069349536276919657 4405908052012152207689743)
            ·
              refine ⟨6608862078018228311534615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405908052012152207689743 6608862078018228311534615)
              ·
                refine ⟨9913293117027342467301923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608862078018228311534615 9913293117027342467301923)
                ·
                  refine ⟨14869939675541013700952885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913293117027342467301923 14869939675541013700952885)
                  ·
                    refine ⟨1394056844581970034464333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14869939675541013700952885 1394056844581970034464333)
                    ·
                      rfl

theorem cell22_4072374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4072374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072374 prefixEnd_4072374 := by exact prefixLift 4072374
  have htrace : WordTrace (prefixWord ++ tailWord_4072374) baseStart_4072374 baseEnd_4072374 := by
    simpa [prefixWord, tailWord_4072374, baseEnd_4072374] using wordTrace_append hprefix tailTrace_4072374
  have hstable : (prefixWord ++ tailWord_4072374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072374).length < 2 ^ (prefixWord ++ tailWord_4072374).sum := by decide
  have hdescent : baseEnd_4072374 < baseStart_4072374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072379 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_4072379 : Nat := 118140960795 + 4072379 * 2 ^ 59
def prefixEnd_4072379 : Nat := 4983230072969 + 3 ^ 40 * 4072379 * 2
def baseEnd_4072379 : Nat := 1394058556184151688089317

theorem tailTrace_4072379 : CollatzResearch.WordTrace tailWord_4072379 prefixEnd_4072379 1394058556184151688089317 := by
  unfold tailWord_4072379
  simp only [CollatzResearch.WordTrace]
  refine ⟨148531864513473864806172191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99021243008982576537448127 148531864513473864806172191)
  ·
    refine ⟨222797796770210797209258287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148531864513473864806172191 222797796770210797209258287)
    ·
      refine ⟨334196695155316195813887431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222797796770210797209258287 334196695155316195813887431)
      ·
        refine ⟨501295042732974293720831147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334196695155316195813887431 501295042732974293720831147)
        ·
          refine ⟨751942564099461440581246721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501295042732974293720831147 751942564099461440581246721)
          ·
            refine ⟨563956923074596080435935041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751942564099461440581246721 563956923074596080435935041)
            ·
              refine ⟨422967692305947060326951281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563956923074596080435935041 422967692305947060326951281)
              ·
                refine ⟨317225769229460295245213461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422967692305947060326951281 317225769229460295245213461)
                ·
                  refine ⟨14869957932630951339619381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317225769229460295245213461 14869957932630951339619381)
                  ·
                    refine ⟨1394058556184151688089317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14869957932630951339619381 1394058556184151688089317)
                    ·
                      rfl

theorem cell22_4072379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_4072379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072379 prefixEnd_4072379 := by exact prefixLift 4072379
  have htrace : WordTrace (prefixWord ++ tailWord_4072379) baseStart_4072379 baseEnd_4072379 := by
    simpa [prefixWord, tailWord_4072379, baseEnd_4072379] using wordTrace_append hprefix tailTrace_4072379
  have hstable : (prefixWord ++ tailWord_4072379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072379).length < 2 ^ (prefixWord ++ tailWord_4072379).sum := by decide
  have hdescent : baseEnd_4072379 < baseStart_4072379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072402 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_4072402 : Nat := 118140960795 + 4072402 * 2 ^ 59
def prefixEnd_4072402 : Nat := 4983230072969 + 3 ^ 40 * 4072402 * 2
def baseEnd_4072402 : Nat := 1394066429554187294764247

theorem tailTrace_4072402 : CollatzResearch.WordTrace tailWord_4072402 prefixEnd_4072402 1394066429554187294764247 := by
  unfold tailWord_4072402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37133175848097634933564865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99021802261593693156172973 37133175848097634933564865)
  ·
    refine ⟨27849881886073226200173649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37133175848097634933564865 27849881886073226200173649)
    ·
      refine ⟨20887411414554919650130237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27849881886073226200173649 20887411414554919650130237)
      ·
        refine ⟨7832779280458094868798839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20887411414554919650130237 7832779280458094868798839)
        ·
          refine ⟨11749168920687142303198259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832779280458094868798839 11749168920687142303198259)
          ·
            refine ⟨17623753381030713454797389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749168920687142303198259 17623753381030713454797389)
            ·
              refine ⟨6608907517886517545549021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17623753381030713454797389 6608907517886517545549021)
              ·
                refine ⟨2478340319207444079580883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608907517886517545549021 2478340319207444079580883)
                ·
                  refine ⟨3717510478811166119371325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478340319207444079580883 3717510478811166119371325)
                  ·
                    refine ⟨1394066429554187294764247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717510478811166119371325 1394066429554187294764247)
                    ·
                      rfl

theorem cell22_4072402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_4072402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072402 prefixEnd_4072402 := by exact prefixLift 4072402
  have htrace : WordTrace (prefixWord ++ tailWord_4072402) baseStart_4072402 baseEnd_4072402 := by
    simpa [prefixWord, tailWord_4072402, baseEnd_4072402] using wordTrace_append hprefix tailTrace_4072402
  have hstable : (prefixWord ++ tailWord_4072402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072402).length < 2 ^ (prefixWord ++ tailWord_4072402).sum := by decide
  have hdescent : baseEnd_4072402 < baseStart_4072402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072441 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_4072441 : Nat := 118140960795 + 4072441 * 2 ^ 59
def prefixEnd_4072441 : Nat := 4983230072969 + 3 ^ 40 * 4072441 * 2
def baseEnd_4072441 : Nat := 1394079780051204193039127

theorem tailTrace_4072441 : CollatzResearch.WordTrace tailWord_4072441 prefixEnd_4072441 1394079780051204193039127 := by
  unfold tailWord_4072441
  simp only [CollatzResearch.WordTrace]
  refine ⟨148534125839249249394929177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99022750559499499596619451 148534125839249249394929177)
  ·
    refine ⟨111400594379436937046196883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148534125839249249394929177 111400594379436937046196883)
    ·
      refine ⟨167100891569155405569295325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111400594379436937046196883 167100891569155405569295325)
      ·
        refine ⟨62662834338433277088485747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167100891569155405569295325 62662834338433277088485747)
        ·
          refine ⟨93994251507649915632728621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62662834338433277088485747 93994251507649915632728621)
          ·
            refine ⟨35247844315368718362273233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93994251507649915632728621 35247844315368718362273233)
            ·
              refine ⟨26435883236526538771704925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35247844315368718362273233 26435883236526538771704925)
              ·
                refine ⟨9913456213697452039389347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26435883236526538771704925 9913456213697452039389347)
                ·
                  refine ⟨14870184320546178059084021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913456213697452039389347 14870184320546178059084021)
                  ·
                    refine ⟨1394079780051204193039127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14870184320546178059084021 1394079780051204193039127)
                    ·
                      rfl

theorem cell22_4072441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_4072441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072441 prefixEnd_4072441 := by exact prefixLift 4072441
  have htrace : WordTrace (prefixWord ++ tailWord_4072441) baseStart_4072441 baseEnd_4072441 := by
    simpa [prefixWord, tailWord_4072441, baseEnd_4072441] using wordTrace_append hprefix tailTrace_4072441
  have hstable : (prefixWord ++ tailWord_4072441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072441).length < 2 ^ (prefixWord ++ tailWord_4072441).sum := by decide
  have hdescent : baseEnd_4072441 < baseStart_4072441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072458 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_4072458 : Nat := 118140960795 + 4072458 * 2 ^ 59
def prefixEnd_4072458 : Nat := 4983230072969 + 3 ^ 40 * 4072458 * 2
def baseEnd_4072458 : Nat := 1394085599498621815364075

theorem tailTrace_4072458 : CollatzResearch.WordTrace tailWord_4072458 prefixEnd_4072458 1394085599498621815364075 := by
  unfold tailWord_4072458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37133686470046915324574507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99023163920125107532198685 37133686470046915324574507)
  ·
    refine ⟨55700529705070372986861761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37133686470046915324574507 55700529705070372986861761)
    ·
      refine ⟨41775397278802779740146321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55700529705070372986861761 41775397278802779740146321)
      ·
        refine ⟨31331547959102084805109741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41775397278802779740146321 31331547959102084805109741)
        ·
          refine ⟨11749330484663281801916153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31331547959102084805109741 11749330484663281801916153)
          ·
            refine ⟨8811997863497461351437115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749330484663281801916153 8811997863497461351437115)
            ·
              refine ⟨13217996795246192027155673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8811997863497461351437115 13217996795246192027155673)
              ·
                refine ⟨9913497596434644020366755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13217996795246192027155673 9913497596434644020366755)
                ·
                  refine ⟨14870246394651966030550133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913497596434644020366755 14870246394651966030550133)
                  ·
                    refine ⟨1394085599498621815364075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14870246394651966030550133 1394085599498621815364075)
                    ·
                      rfl

theorem cell22_4072458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_4072458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072458 prefixEnd_4072458 := by exact prefixLift 4072458
  have htrace : WordTrace (prefixWord ++ tailWord_4072458) baseStart_4072458 baseEnd_4072458 := by
    simpa [prefixWord, tailWord_4072458, baseEnd_4072458] using wordTrace_append hprefix tailTrace_4072458
  have hstable : (prefixWord ++ tailWord_4072458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072458).length < 2 ^ (prefixWord ++ tailWord_4072458).sum := by decide
  have hdescent : baseEnd_4072458 < baseStart_4072458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072471 : List Nat := [1, 1, 3, 5, 1, 11]
def baseStart_4072471 : Nat := 118140960795 + 4072471 * 2 ^ 59
def prefixEnd_4072471 : Nat := 4983230072969 + 3 ^ 40 * 4072471 * 2
def baseEnd_4072471 : Nat := 17210988267460421170235

theorem tailTrace_4072471 : CollatzResearch.WordTrace tailWord_4072471 prefixEnd_4072471 17210988267460421170235 := by
  unfold tailWord_4072471
  simp only [CollatzResearch.WordTrace]
  refine ⟨148535220029140564518521267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99023480019427043012347511 148535220029140564518521267)
  ·
    refine ⟨222802830043710846777781901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148535220029140564518521267 222802830043710846777781901)
    ·
      refine ⟨83551061266391567541668213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222802830043710846777781901 83551061266391567541668213)
      ·
        refine ⟨7832911993724209457031395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83551061266391567541668213 7832911993724209457031395)
        ·
          refine ⟨11749367990586314185547093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832911993724209457031395 11749367990586314185547093)
          ·
            refine ⟨17210988267460421170235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11749367990586314185547093 17210988267460421170235)
            ·
              rfl

theorem cell22_4072471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 11].length) (baseStart_4072471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072471 prefixEnd_4072471 := by exact prefixLift 4072471
  have htrace : WordTrace (prefixWord ++ tailWord_4072471) baseStart_4072471 baseEnd_4072471 := by
    simpa [prefixWord, tailWord_4072471, baseEnd_4072471] using wordTrace_append hprefix tailTrace_4072471
  have hstable : (prefixWord ++ tailWord_4072471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072471).length < 2 ^ (prefixWord ++ tailWord_4072471).sum := by decide
  have hdescent : baseEnd_4072471 < baseStart_4072471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072501 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4072501 : Nat := 118140960795 + 4072501 * 2 ^ 59
def prefixEnd_4072501 : Nat := 4983230072969 + 3 ^ 40 * 4072501 * 2
def baseEnd_4072501 : Nat := 1394100319277384036538943

theorem tailTrace_4072501 : CollatzResearch.WordTrace tailWord_4072501 prefixEnd_4072501 1394100319277384036538943 := by
  unfold tailWord_4072501
  simp only [CollatzResearch.WordTrace]
  refine ⟨148536314219031879642113357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99024209479354586428075571 148536314219031879642113357)
  ·
    refine ⟨55701117832136954865792509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148536314219031879642113357 55701117832136954865792509)
    ·
      refine ⟨20887919187051358074672191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55701117832136954865792509 20887919187051358074672191)
      ·
        refine ⟨31331878780577037112008287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20887919187051358074672191 31331878780577037112008287)
        ·
          refine ⟨46997818170865555668012431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31331878780577037112008287 46997818170865555668012431)
          ·
            refine ⟨70496727256298333502018647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46997818170865555668012431 70496727256298333502018647)
            ·
              refine ⟨105745090884447500253027971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70496727256298333502018647 105745090884447500253027971)
              ·
                refine ⟨158617636326671250379541957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105745090884447500253027971 158617636326671250379541957)
                ·
                  refine ⟨29740806811250859446164117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158617636326671250379541957 29740806811250859446164117)
                  ·
                    refine ⟨1394100319277384036538943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29740806811250859446164117 1394100319277384036538943)
                    ·
                      rfl

theorem cell22_4072501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4072501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072501 prefixEnd_4072501 := by exact prefixLift 4072501
  have htrace : WordTrace (prefixWord ++ tailWord_4072501) baseStart_4072501 baseEnd_4072501 := by
    simpa [prefixWord, tailWord_4072501, baseEnd_4072501] using wordTrace_append hprefix tailTrace_4072501
  have hstable : (prefixWord ++ tailWord_4072501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072501).length < 2 ^ (prefixWord ++ tailWord_4072501).sum := by decide
  have hdescent : baseEnd_4072501 < baseStart_4072501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072531 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_4072531 : Nat := 118140960795 + 4072531 * 2 ^ 59
def prefixEnd_4072531 : Nat := 4983230072969 + 3 ^ 40 * 4072531 * 2
def baseEnd_4072531 : Nat := 1394110588890473958288851

theorem tailTrace_4072531 : CollatzResearch.WordTrace tailWord_4072531 prefixEnd_4072531 1394110588890473958288851 := by
  unfold tailWord_4072531
  simp only [CollatzResearch.WordTrace]
  refine ⟨148537408408923194765705447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99024938939282129843803631 148537408408923194765705447)
  ·
    refine ⟨222806112613384792148558171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148537408408923194765705447 222806112613384792148558171)
    ·
      refine ⟨334209168920077188222837257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222806112613384792148558171 334209168920077188222837257)
      ·
        refine ⟨250656876690057891167127943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334209168920077188222837257 250656876690057891167127943)
        ·
          refine ⟨375985315035086836750691915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250656876690057891167127943 375985315035086836750691915)
          ·
            refine ⟨563977972552630255126037873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375985315035086836750691915 563977972552630255126037873)
            ·
              refine ⟨422983479414472691344528405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563977972552630255126037873 422983479414472691344528405)
              ·
                refine ⟨19827350597553407406774769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 422983479414472691344528405 19827350597553407406774769)
                ·
                  refine ⟨14870512948165055555081077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19827350597553407406774769 14870512948165055555081077)
                  ·
                    refine ⟨1394110588890473958288851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14870512948165055555081077 1394110588890473958288851)
                    ·
                      rfl

theorem cell22_4072531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_4072531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072531 prefixEnd_4072531 := by exact prefixLift 4072531
  have htrace : WordTrace (prefixWord ++ tailWord_4072531) baseStart_4072531 baseEnd_4072531 := by
    simpa [prefixWord, tailWord_4072531, baseEnd_4072531] using wordTrace_append hprefix tailTrace_4072531
  have hstable : (prefixWord ++ tailWord_4072531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072531).length < 2 ^ (prefixWord ++ tailWord_4072531).sum := by decide
  have hdescent : baseEnd_4072531 < baseStart_4072531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072561 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 8]
def baseStart_4072561 : Nat := 118140960795 + 4072561 * 2 ^ 59
def prefixEnd_4072561 : Nat := 4983230072969 + 3 ^ 40 * 4072561 * 2
def baseEnd_4072561 : Nat := 464706952834521293346253

theorem tailTrace_4072561 : CollatzResearch.WordTrace tailWord_4072561 prefixEnd_4072561 464706952834521293346253 := by
  unfold tailWord_4072561
  simp only [CollatzResearch.WordTrace]
  refine ⟨148538502598814509889297537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99025668399209673259531691 148538502598814509889297537)
  ·
    refine ⟨111403876949110882416973153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148538502598814509889297537 111403876949110882416973153)
    ·
      refine ⟨83552907711833161812729865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111403876949110882416973153 83552907711833161812729865)
      ·
        refine ⟨62664680783874871359547399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83552907711833161812729865 62664680783874871359547399)
        ·
          refine ⟨93997021175812307039321099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62664680783874871359547399 93997021175812307039321099)
          ·
            refine ⟨140995531763718460558981649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93997021175812307039321099 140995531763718460558981649)
            ·
              refine ⟨105746648822788845419236237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140995531763718460558981649 105746648822788845419236237)
              ·
                refine ⟨39654993308545817032213589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105746648822788845419236237 39654993308545817032213589)
                ·
                  refine ⟨464706952834521293346253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39654993308545817032213589 464706952834521293346253)
                  ·
                    rfl

theorem cell22_4072561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_4072561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072561 prefixEnd_4072561 := by exact prefixLift 4072561
  have htrace : WordTrace (prefixWord ++ tailWord_4072561) baseStart_4072561 baseEnd_4072561 := by
    simpa [prefixWord, tailWord_4072561, baseEnd_4072561] using wordTrace_append hprefix tailTrace_4072561
  have hstable : (prefixWord ++ tailWord_4072561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072561).length < 2 ^ (prefixWord ++ tailWord_4072561).sum := by decide
  have hdescent : baseEnd_4072561 < baseStart_4072561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072580 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_4072580 : Nat := 118140960795 + 4072580 * 2 ^ 59
def prefixEnd_4072580 : Nat := 4983230072969 + 3 ^ 40 * 4072580 * 2
def baseEnd_4072580 : Nat := 1394127362591854163813701

theorem tailTrace_4072580 : CollatzResearch.WordTrace tailWord_4072580 prefixEnd_4072580 1394127362591854163813701 := by
  unfold tailWord_4072580
  simp only [CollatzResearch.WordTrace]
  refine ⟨74269597792872838067119597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99026130390497117422826129 74269597792872838067119597)
  ·
    refine ⟨27851099172327314275169849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74269597792872838067119597 27851099172327314275169849)
    ·
      refine ⟨20888324379245485706377387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27851099172327314275169849 20888324379245485706377387)
      ·
        refine ⟨31332486568868228559566081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20888324379245485706377387 31332486568868228559566081)
        ·
          refine ⟨23499364926651171419674561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31332486568868228559566081 23499364926651171419674561)
          ·
            refine ⟨17624523694988378564755921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23499364926651171419674561 17624523694988378564755921)
            ·
              refine ⟨13218392771241283923566941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17624523694988378564755921 13218392771241283923566941)
              ·
                refine ⟨4956897289215481471337603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13218392771241283923566941 4956897289215481471337603)
                ·
                  refine ⟨7435345933823222207006405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956897289215481471337603 7435345933823222207006405)
                  ·
                    refine ⟨1394127362591854163813701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435345933823222207006405 1394127362591854163813701)
                    ·
                      rfl

theorem cell22_4072580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_4072580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072580 prefixEnd_4072580 := by exact prefixLift 4072580
  have htrace : WordTrace (prefixWord ++ tailWord_4072580) baseStart_4072580 baseEnd_4072580 := by
    simpa [prefixWord, tailWord_4072580, baseEnd_4072580] using wordTrace_append hprefix tailTrace_4072580
  have hstable : (prefixWord ++ tailWord_4072580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072580).length < 2 ^ (prefixWord ++ tailWord_4072580).sum := by decide
  have hdescent : baseEnd_4072580 < baseStart_4072580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072608 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_4072608 : Nat := 118140960795 + 4072608 * 2 ^ 59
def prefixEnd_4072608 : Nat := 4983230072969 + 3 ^ 40 * 4072608 * 2
def baseEnd_4072608 : Nat := 1394136947564071424113615

theorem tailTrace_4072608 : CollatzResearch.WordTrace tailWord_4072608 prefixEnd_4072608 1394136947564071424113615 := by
  unfold tailWord_4072608
  simp only [CollatzResearch.WordTrace]
  refine ⟨74270108414822118458129239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99026811219762824610838985 74270108414822118458129239)
  ·
    refine ⟨111405162622233177687193859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74270108414822118458129239 111405162622233177687193859)
    ·
      refine ⟨167107743933349766530790789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111405162622233177687193859 167107743933349766530790789)
      ·
        refine ⟨31332701987503081224523273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167107743933349766530790789 31332701987503081224523273)
        ·
          refine ⟨23499526490627310918392455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31332701987503081224523273 23499526490627310918392455)
          ·
            refine ⟨35249289735940966377588683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23499526490627310918392455 35249289735940966377588683)
            ·
              refine ⟨52873934603911449566383025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35249289735940966377588683 52873934603911449566383025)
              ·
                refine ⟨39655450952933587174787269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52873934603911449566383025 39655450952933587174787269)
                ·
                  refine ⟨7435397053675047595272613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39655450952933587174787269 7435397053675047595272613)
                  ·
                    refine ⟨1394136947564071424113615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435397053675047595272613 1394136947564071424113615)
                    ·
                      rfl

theorem cell22_4072608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_4072608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072608 prefixEnd_4072608 := by exact prefixLift 4072608
  have htrace : WordTrace (prefixWord ++ tailWord_4072608) baseStart_4072608 baseEnd_4072608 := by
    simpa [prefixWord, tailWord_4072608, baseEnd_4072608] using wordTrace_append hprefix tailTrace_4072608
  have hstable : (prefixWord ++ tailWord_4072608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072608).length < 2 ^ (prefixWord ++ tailWord_4072608).sum := by decide
  have hdescent : baseEnd_4072608 < baseStart_4072608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072625 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_4072625 : Nat := 118140960795 + 4072625 * 2 ^ 59
def prefixEnd_4072625 : Nat := 4983230072969 + 3 ^ 40 * 4072625 * 2
def baseEnd_4072625 : Nat := 1394142767011489046438563

theorem tailTrace_4072625 : CollatzResearch.WordTrace tailWord_4072625 prefixEnd_4072625 1394142767011489046438563 := by
  unfold tailWord_4072625
  simp only [CollatzResearch.WordTrace]
  refine ⟨148540836870582648819627329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99027224580388432546418219 148540836870582648819627329)
  ·
    refine ⟨111405627652936986614720497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148540836870582648819627329 111405627652936986614720497)
    ·
      refine ⟨83554220739702739961040373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111405627652936986614720497 83554220739702739961040373)
      ·
        refine ⟨7833208194347131871347535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83554220739702739961040373 7833208194347131871347535)
        ·
          refine ⟨11749812291520697807021303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833208194347131871347535 11749812291520697807021303)
          ·
            refine ⟨17624718437281046710531955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749812291520697807021303 17624718437281046710531955)
            ·
              refine ⟨26437077655921570065797933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17624718437281046710531955 26437077655921570065797933)
              ·
                refine ⟨9913904120970588774674225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26437077655921570065797933 9913904120970588774674225)
                ·
                  refine ⟨7435428090727941581005669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9913904120970588774674225 7435428090727941581005669)
                  ·
                    refine ⟨1394142767011489046438563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435428090727941581005669 1394142767011489046438563)
                    ·
                      rfl

theorem cell22_4072625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_4072625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072625 prefixEnd_4072625 := by exact prefixLift 4072625
  have htrace : WordTrace (prefixWord ++ tailWord_4072625) baseStart_4072625 baseEnd_4072625 := by
    simpa [prefixWord, tailWord_4072625, baseEnd_4072625] using wordTrace_append hprefix tailTrace_4072625
  have hstable : (prefixWord ++ tailWord_4072625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072625).length < 2 ^ (prefixWord ++ tailWord_4072625).sum := by decide
  have hdescent : baseEnd_4072625 < baseStart_4072625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072644 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4072644 : Nat := 118140960795 + 4072644 * 2 ^ 59
def prefixEnd_4072644 : Nat := 4983230072969 + 3 ^ 40 * 4072644 * 2
def baseEnd_4072644 : Nat := 1394149271099779330213505

theorem tailTrace_4072644 : CollatzResearch.WordTrace tailWord_4072644 prefixEnd_4072644 1394149271099779330213505 := by
  unfold tailWord_4072644
  simp only [CollatzResearch.WordTrace]
  refine ⟨74270764928756907532284493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99027686571675876709712657 74270764928756907532284493)
  ·
    refine ⟨27851536848283840324606685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74270764928756907532284493 27851536848283840324606685)
    ·
      refine ⟨10444326318106440121727507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27851536848283840324606685 10444326318106440121727507)
      ·
        refine ⟨15666489477159660182591261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10444326318106440121727507 15666489477159660182591261)
        ·
          refine ⟨5874933553934872568471723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15666489477159660182591261 5874933553934872568471723)
          ·
            refine ⟨8812400330902308852707585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874933553934872568471723 8812400330902308852707585)
            ·
              refine ⟨6609300248176731639530689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812400330902308852707585 6609300248176731639530689)
              ·
                refine ⟨4956975186132548729648017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609300248176731639530689 4956975186132548729648017)
                ·
                  refine ⟨3717731389599411547236013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956975186132548729648017 3717731389599411547236013)
                  ·
                    refine ⟨1394149271099779330213505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717731389599411547236013 1394149271099779330213505)
                    ·
                      rfl

theorem cell22_4072644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4072644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072644 prefixEnd_4072644 := by exact prefixLift 4072644
  have htrace : WordTrace (prefixWord ++ tailWord_4072644) baseStart_4072644 baseEnd_4072644 := by
    simpa [prefixWord, tailWord_4072644, baseEnd_4072644] using wordTrace_append hprefix tailTrace_4072644
  have hstable : (prefixWord ++ tailWord_4072644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072644).length < 2 ^ (prefixWord ++ tailWord_4072644).sum := by decide
  have hdescent : baseEnd_4072644 < baseStart_4072644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072702 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4072702 : Nat := 118140960795 + 4072702 * 2 ^ 59
def prefixEnd_4072702 : Nat := 4983230072969 + 3 ^ 40 * 4072702 * 2
def baseEnd_4072702 : Nat := 464723041895028837421109

theorem tailTrace_4072702 : CollatzResearch.WordTrace tailWord_4072702 prefixEnd_4072702 464723041895028837421109 := by
  unfold tailWord_4072702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567955661412961371272545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99029096860869127313453573 18567955661412961371272545)
  ·
    refine ⟨13925966746059721028454409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18567955661412961371272545 13925966746059721028454409)
    ·
      refine ⟨10444475059544790771340807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13925966746059721028454409 10444475059544790771340807)
      ·
        refine ⟨15666712589317186157011211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10444475059544790771340807 15666712589317186157011211)
        ·
          refine ⟨23500068883975779235516817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15666712589317186157011211 23500068883975779235516817)
          ·
            refine ⟨17625051662981834426637613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23500068883975779235516817 17625051662981834426637613)
            ·
              refine ⟨6609394373618187909989105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17625051662981834426637613 6609394373618187909989105)
              ·
                refine ⟨4957045780213640932491829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609394373618187909989105 4957045780213640932491829)
                ·
                  refine ⟨464723041895028837421109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957045780213640932491829 464723041895028837421109)
                  ·
                    rfl

theorem cell22_4072702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4072702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072702 prefixEnd_4072702 := by exact prefixLift 4072702
  have htrace : WordTrace (prefixWord ++ tailWord_4072702) baseStart_4072702 baseEnd_4072702 := by
    simpa [prefixWord, tailWord_4072702, baseEnd_4072702] using wordTrace_append hprefix tailTrace_4072702
  have hstable : (prefixWord ++ tailWord_4072702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072702).length < 2 ^ (prefixWord ++ tailWord_4072702).sum := by decide
  have hdescent : baseEnd_4072702 < baseStart_4072702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072730 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_4072730 : Nat := 118140960795 + 4072730 * 2 ^ 59
def prefixEnd_4072730 : Nat := 4983230072969 + 3 ^ 40 * 4072730 * 2
def baseEnd_4072730 : Nat := 464726236885767924187747

theorem tailTrace_4072730 : CollatzResearch.WordTrace tailWord_4072730 prefixEnd_4072730 464726236885767924187747 := by
  unfold tailWord_4072730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37136166633800562938049911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99029777690134834501466429 37136166633800562938049911)
  ·
    refine ⟨55704249950700844407074867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37136166633800562938049911 55704249950700844407074867)
    ·
      refine ⟨83556374926051266610612301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55704249950700844407074867 83556374926051266610612301)
      ·
        refine ⟨31333640597269224978979613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83556374926051266610612301 31333640597269224978979613)
        ·
          refine ⟨11750115223975959367117355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31333640597269224978979613 11750115223975959367117355)
          ·
            refine ⟨17625172835963939050676033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750115223975959367117355 17625172835963939050676033)
            ·
              refine ⟨13218879626972954288007025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17625172835963939050676033 13218879626972954288007025)
              ·
                refine ⟨9914159720229715716005269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13218879626972954288007025 9914159720229715716005269)
                ·
                  refine ⟨464726236885767924187747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9914159720229715716005269 464726236885767924187747)
                  ·
                    rfl

theorem cell22_4072730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_4072730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072730 prefixEnd_4072730 := by exact prefixLift 4072730
  have htrace : WordTrace (prefixWord ++ tailWord_4072730) baseStart_4072730 baseEnd_4072730 := by
    simpa [prefixWord, tailWord_4072730, baseEnd_4072730] using wordTrace_append hprefix tailTrace_4072730
  have hstable : (prefixWord ++ tailWord_4072730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072730).length < 2 ^ (prefixWord ++ tailWord_4072730).sum := by decide
  have hdescent : baseEnd_4072730 < baseStart_4072730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072749 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4072749 : Nat := 118140960795 + 4072749 * 2 ^ 59
def prefixEnd_4072749 : Nat := 4983230072969 + 3 ^ 40 * 4072749 * 2
def baseEnd_4072749 : Nat := 1394185214745594056338183

theorem tailTrace_4072749 : CollatzResearch.WordTrace tailWord_4072749 prefixEnd_4072749 1394185214745594056338183 := by
  unfold tailWord_4072749
  simp only [CollatzResearch.WordTrace]
  refine ⟨148545359522133417997141301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99030239681422278664760867 148545359522133417997141301)
  ·
    refine ⟨13926127455200007937231997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148545359522133417997141301 13926127455200007937231997)
    ·
      refine ⟨5222297795700002976461999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13926127455200007937231997 5222297795700002976461999)
      ·
        refine ⟨7833446693550004464692999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222297795700002976461999 7833446693550004464692999)
        ·
          refine ⟨11750170040325006697039499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833446693550004464692999 11750170040325006697039499)
          ·
            refine ⟨17625255060487510045559249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750170040325006697039499 17625255060487510045559249)
            ·
              refine ⟨13218941295365632534169437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17625255060487510045559249 13218941295365632534169437)
              ·
                refine ⟨4957102985762112200313539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13218941295365632534169437 4957102985762112200313539)
                ·
                  refine ⟨7435654478643168300470309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957102985762112200313539 7435654478643168300470309)
                  ·
                    refine ⟨1394185214745594056338183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435654478643168300470309 1394185214745594056338183)
                    ·
                      rfl

theorem cell22_4072749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4072749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072749 prefixEnd_4072749 := by exact prefixLift 4072749
  have htrace : WordTrace (prefixWord ++ tailWord_4072749) baseStart_4072749 baseEnd_4072749 := by
    simpa [prefixWord, tailWord_4072749, baseEnd_4072749] using wordTrace_append hprefix tailTrace_4072749
  have hstable : (prefixWord ++ tailWord_4072749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072749).length < 2 ^ (prefixWord ++ tailWord_4072749).sum := by decide
  have hdescent : baseEnd_4072749 < baseStart_4072749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072762 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_4072762 : Nat := 118140960795 + 4072762 * 2 ^ 59
def prefixEnd_4072762 : Nat := 4983230072969 + 3 ^ 40 * 4072762 * 2
def baseEnd_4072762 : Nat := 1394189664911266355763143

theorem tailTrace_4072762 : CollatzResearch.WordTrace tailWord_4072762 prefixEnd_4072762 1394189664911266355763143 := by
  unfold tailWord_4072762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37136458417771580304341135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99030555780724214144909693 37136458417771580304341135)
  ·
    refine ⟨55704687626657370456511703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37136458417771580304341135 55704687626657370456511703)
    ·
      refine ⟨83557031439986055684767555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55704687626657370456511703 83557031439986055684767555)
      ·
        refine ⟨125335547159979083527151333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83557031439986055684767555 125335547159979083527151333)
        ·
          refine ⟨23500415092496078161340875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125335547159979083527151333 23500415092496078161340875)
          ·
            refine ⟨35250622638744117242011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23500415092496078161340875 35250622638744117242011313)
            ·
              refine ⟨26437966979058087931508485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35250622638744117242011313 26437966979058087931508485)
              ·
                refine ⟨4957118808573391487157841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26437966979058087931508485 4957118808573391487157841)
                ·
                  refine ⟨3717839106430043615368381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957118808573391487157841 3717839106430043615368381)
                  ·
                    refine ⟨1394189664911266355763143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717839106430043615368381 1394189664911266355763143)
                    ·
                      rfl

theorem cell22_4072762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_4072762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072762 prefixEnd_4072762 := by exact prefixLift 4072762
  have htrace : WordTrace (prefixWord ++ tailWord_4072762) baseStart_4072762 baseEnd_4072762 := by
    simpa [prefixWord, tailWord_4072762, baseEnd_4072762] using wordTrace_append hprefix tailTrace_4072762
  have hstable : (prefixWord ++ tailWord_4072762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072762).length < 2 ^ (prefixWord ++ tailWord_4072762).sum := by decide
  have hdescent : baseEnd_4072762 < baseStart_4072762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072764 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_4072764 : Nat := 118140960795 + 4072764 * 2 ^ 59
def prefixEnd_4072764 : Nat := 4983230072969 + 3 ^ 40 * 4072764 * 2
def baseEnd_4072764 : Nat := 464730116517379672404379

theorem tailTrace_4072764 : CollatzResearch.WordTrace tailWord_4072764 prefixEnd_4072764 464730116517379672404379 := by
  unfold tailWord_4072764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74272953308539537779468673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99030604411386050372624897 74272953308539537779468673)
  ·
    refine ⟨55704714981404653334601505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74272953308539537779468673 55704714981404653334601505)
    ·
      refine ⟨41778536236053490000951129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55704714981404653334601505 41778536236053490000951129)
      ·
        refine ⟨31333902177040117500713347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41778536236053490000951129 31333902177040117500713347)
        ·
          refine ⟨47000853265560176251070021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31333902177040117500713347 47000853265560176251070021)
          ·
            refine ⟨8812659987292533047075629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47000853265560176251070021 8812659987292533047075629)
            ·
              refine ⟨3304747495234699892653361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8812659987292533047075629 3304747495234699892653361)
              ·
                refine ⟨2478560621426024919490021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304747495234699892653361 2478560621426024919490021)
                ·
                  refine ⟨464730116517379672404379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2478560621426024919490021 464730116517379672404379)
                  ·
                    rfl

theorem cell22_4072764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_4072764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072764 prefixEnd_4072764 := by exact prefixLift 4072764
  have htrace : WordTrace (prefixWord ++ tailWord_4072764) baseStart_4072764 baseEnd_4072764 := by
    simpa [prefixWord, tailWord_4072764, baseEnd_4072764] using wordTrace_append hprefix tailTrace_4072764
  have hstable : (prefixWord ++ tailWord_4072764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072764).length < 2 ^ (prefixWord ++ tailWord_4072764).sum := by decide
  have hdescent : baseEnd_4072764 < baseStart_4072764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072775 : List Nat := [1, 1, 4, 1, 2, 4, 2, 7]
def baseStart_4072775 : Nat := 118140960795 + 4072775 * 2 ^ 59
def prefixEnd_4072775 : Nat := 4983230072969 + 3 ^ 40 * 4072775 * 2
def baseEnd_4072775 : Nat := 154910457230770961687567

theorem tailTrace_4072775 : CollatzResearch.WordTrace tailWord_4072775 prefixEnd_4072775 154910457230770961687567 := by
  unfold tailWord_4072775
  simp only [CollatzResearch.WordTrace]
  refine ⟨148546307820039224437587779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99030871880026149625058519 148546307820039224437587779)
  ·
    refine ⟨222819461730058836656381669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148546307820039224437587779 222819461730058836656381669)
    ·
      refine ⟨41778649074386031873071563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222819461730058836656381669 41778649074386031873071563)
      ·
        refine ⟨62667973611579047809607345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41778649074386031873071563 62667973611579047809607345)
        ·
          refine ⟨47000980208684285857205509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62667973611579047809607345 47000980208684285857205509)
          ·
            refine ⟨8812683789128303598226033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47000980208684285857205509 8812683789128303598226033)
            ·
              refine ⟨6609512841846227698669525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812683789128303598226033 6609512841846227698669525)
              ·
                refine ⟨154910457230770961687567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6609512841846227698669525 154910457230770961687567)
                ·
                  rfl

theorem cell22_4072775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 7].length) (baseStart_4072775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072775 prefixEnd_4072775 := by exact prefixLift 4072775
  have htrace : WordTrace (prefixWord ++ tailWord_4072775) baseStart_4072775 baseEnd_4072775 := by
    simpa [prefixWord, tailWord_4072775, baseEnd_4072775] using wordTrace_append hprefix tailTrace_4072775
  have hstable : (prefixWord ++ tailWord_4072775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072775).length < 2 ^ (prefixWord ++ tailWord_4072775).sum := by decide
  have hdescent : baseEnd_4072775 < baseStart_4072775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072835 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_4072835 : Nat := 118140960795 + 4072835 * 2 ^ 59
def prefixEnd_4072835 : Nat := 4983230072969 + 3 ^ 40 * 4072835 * 2
def baseEnd_4072835 : Nat := 1394214654303118498687919

theorem tailTrace_4072835 : CollatzResearch.WordTrace tailWord_4072835 prefixEnd_4072835 1394214654303118498687919 := by
  unfold tailWord_4072835
  simp only [CollatzResearch.WordTrace]
  refine ⟨148548496199821854684771959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99032330799881236456514639 148548496199821854684771959)
  ·
    refine ⟨222822744299732782027157939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148548496199821854684771959 222822744299732782027157939)
    ·
      refine ⟨334234116449599173040736909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222822744299732782027157939 334234116449599173040736909)
      ·
        refine ⟨125337793668599689890276341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334234116449599173040736909 125337793668599689890276341)
        ·
          refine ⟨11750418156431220927213407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125337793668599689890276341 11750418156431220927213407)
          ·
            refine ⟨17625627234646831390820111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750418156431220927213407 17625627234646831390820111)
            ·
              refine ⟨26438440851970247086230167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17625627234646831390820111 26438440851970247086230167)
              ·
                refine ⟨39657661277955370629345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26438440851970247086230167 39657661277955370629345251)
                ·
                  refine ⟨59486491916933055944017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39657661277955370629345251 59486491916933055944017877)
                  ·
                    refine ⟨1394214654303118498687919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59486491916933055944017877 1394214654303118498687919)
                    ·
                      rfl

theorem cell22_4072835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_4072835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072835 prefixEnd_4072835 := by exact prefixLift 4072835
  have htrace : WordTrace (prefixWord ++ tailWord_4072835) baseStart_4072835 baseEnd_4072835 := by
    simpa [prefixWord, tailWord_4072835, baseEnd_4072835] using wordTrace_append hprefix tailTrace_4072835
  have hstable : (prefixWord ++ tailWord_4072835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072835).length < 2 ^ (prefixWord ++ tailWord_4072835).sum := by decide
  have hdescent : baseEnd_4072835 < baseStart_4072835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072867 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 1, 4]
def baseStart_4072867 : Nat := 118140960795 + 4072867 * 2 ^ 59
def prefixEnd_4072867 : Nat := 4983230072969 + 3 ^ 40 * 4072867 * 2
def baseEnd_4072867 : Nat := 1394225608557081081887821

theorem tailTrace_4072867 : CollatzResearch.WordTrace tailWord_4072867 prefixEnd_4072867 1394225608557081081887821 := by
  unfold tailWord_4072867
  simp only [CollatzResearch.WordTrace]
  refine ⟨148549663335705924149936855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99033108890470616099957903 148549663335705924149936855)
  ·
    refine ⟨222824495003558886224905283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148549663335705924149936855 222824495003558886224905283)
    ·
      refine ⟨334236742505338329337357925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222824495003558886224905283 334236742505338329337357925)
      ·
        refine ⟨62669389219750936750754611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334236742505338329337357925 62669389219750936750754611)
        ·
          refine ⟨94004083829626405126131917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62669389219750936750754611 94004083829626405126131917)
          ·
            refine ⟨35251531436109901922299469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94004083829626405126131917 35251531436109901922299469)
            ·
              refine ⟨13219324288541213220862301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35251531436109901922299469 13219324288541213220862301)
              ·
                refine ⟨4957246608202954957823363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13219324288541213220862301 4957246608202954957823363)
                ·
                  refine ⟨7435869912304432436735045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957246608202954957823363 7435869912304432436735045)
                  ·
                    refine ⟨1394225608557081081887821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435869912304432436735045 1394225608557081081887821)
                    ·
                      rfl

theorem cell22_4072867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4].length) (baseStart_4072867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072867 prefixEnd_4072867 := by exact prefixLift 4072867
  have htrace : WordTrace (prefixWord ++ tailWord_4072867) baseStart_4072867 baseEnd_4072867 := by
    simpa [prefixWord, tailWord_4072867, baseEnd_4072867] using wordTrace_append hprefix tailTrace_4072867
  have hstable : (prefixWord ++ tailWord_4072867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072867).length < 2 ^ (prefixWord ++ tailWord_4072867).sum := by decide
  have hdescent : baseEnd_4072867 < baseStart_4072867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072989 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 5]
def baseStart_4072989 : Nat := 118140960795 + 4072989 * 2 ^ 59
def prefixEnd_4072989 : Nat := 4983230072969 + 3 ^ 40 * 4072989 * 2
def baseEnd_4072989 : Nat := 464755790550104476779149

theorem tailTrace_4072989 : CollatzResearch.WordTrace tailWord_4072989 prefixEnd_4072989 464755790550104476779149 := by
  unfold tailWord_4072989
  simp only [CollatzResearch.WordTrace]
  refine ⟨148554113041263938985878021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99036075360842625990585347 148554113041263938985878021)
  ·
    refine ⟨27853896195236988559852129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148554113041263938985878021 27853896195236988559852129)
    ·
      refine ⟨20890422146427741419889097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27853896195236988559852129 20890422146427741419889097)
      ·
        refine ⟨15667816609820806064916823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20890422146427741419889097 15667816609820806064916823)
        ·
          refine ⟨23501724914731209097375235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667816609820806064916823 23501724914731209097375235)
          ·
            refine ⟨35252587372096813646062853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23501724914731209097375235 35252587372096813646062853)
            ·
              refine ⟨6609860132268152558636785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35252587372096813646062853 6609860132268152558636785)
              ·
                refine ⟨4957395099201114418977589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609860132268152558636785 4957395099201114418977589)
                ·
                  refine ⟨464755790550104476779149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957395099201114418977589 464755790550104476779149)
                  ·
                    rfl

theorem cell22_4072989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_4072989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072989 prefixEnd_4072989 := by exact prefixLift 4072989
  have htrace : WordTrace (prefixWord ++ tailWord_4072989) baseStart_4072989 baseEnd_4072989 := by
    simpa [prefixWord, tailWord_4072989, baseEnd_4072989] using wordTrace_append hprefix tailTrace_4072989
  have hstable : (prefixWord ++ tailWord_4072989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072989).length < 2 ^ (prefixWord ++ tailWord_4072989).sum := by decide
  have hdescent : baseEnd_4072989 < baseStart_4072989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4072993 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 1, 3]
def baseStart_4072993 : Nat := 118140960795 + 4072993 * 2 ^ 59
def prefixEnd_4072993 : Nat := 4983230072969 + 3 ^ 40 * 4072993 * 2
def baseEnd_4072993 : Nat := 1394268740932058753237435

theorem tailTrace_4072993 : CollatzResearch.WordTrace tailWord_4072993 prefixEnd_4072993 1394268740932058753237435 := by
  unfold tailWord_4072993
  simp only [CollatzResearch.WordTrace]
  refine ⟨148554258933249447669023633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99036172622166298446015755 148554258933249447669023633)
  ·
    refine ⟨111415694199937085751767725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148554258933249447669023633 111415694199937085751767725)
    ·
      refine ⟨41780885324976407156912897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111415694199937085751767725 41780885324976407156912897)
      ·
        refine ⟨31335663993732305367684673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41780885324976407156912897 31335663993732305367684673)
        ·
          refine ⟨23501747995299229025763505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31335663993732305367684673 23501747995299229025763505)
          ·
            refine ⟨17626310996474421769322629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23501747995299229025763505 17626310996474421769322629)
            ·
              refine ⟨3304933311838954081747993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17626310996474421769322629 3304933311838954081747993)
              ·
                refine ⟨2478699983879215561310995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304933311838954081747993 2478699983879215561310995)
                ·
                  refine ⟨3718049975818823341966493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478699983879215561310995 3718049975818823341966493)
                  ·
                    refine ⟨1394268740932058753237435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718049975818823341966493 1394268740932058753237435)
                    ·
                      rfl

theorem cell22_4072993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_4072993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4072993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4072993 prefixEnd_4072993 := by exact prefixLift 4072993
  have htrace : WordTrace (prefixWord ++ tailWord_4072993) baseStart_4072993 baseEnd_4072993 := by
    simpa [prefixWord, tailWord_4072993, baseEnd_4072993] using wordTrace_append hprefix tailTrace_4072993
  have hstable : (prefixWord ++ tailWord_4072993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4072993).length < 2 ^ (prefixWord ++ tailWord_4072993).sum := by decide
  have hdescent : baseEnd_4072993 < baseStart_4072993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4072993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073017 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 8]
def baseStart_4073017 : Nat := 118140960795 + 4073017 * 2 ^ 59
def prefixEnd_4073017 : Nat := 4983230072969 + 3 ^ 40 * 4073017 * 2
def baseEnd_4073017 : Nat := 464758985540843563545787

theorem tailTrace_4073017 : CollatzResearch.WordTrace tailWord_4073017 prefixEnd_4073017 464758985540843563545787 := by
  unfold tailWord_4073017
  simp only [CollatzResearch.WordTrace]
  refine ⟨148555134285162499767897305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99036756190108333178598203 148555134285162499767897305)
  ·
    refine ⟨111416350713871874825922979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148555134285162499767897305 111416350713871874825922979)
    ·
      refine ⟨167124526070807812238884469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111416350713871874825922979 167124526070807812238884469)
      ·
        refine ⟨15667924319138232397395419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167124526070807812238884469 15667924319138232397395419)
        ·
          refine ⟨23501886478707348596093129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667924319138232397395419 23501886478707348596093129)
          ·
            refine ⟨17626414859030511447069847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23501886478707348596093129 17626414859030511447069847)
            ·
              refine ⟨26439622288545767170604771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626414859030511447069847 26439622288545767170604771)
              ·
                refine ⟨39659433432818650755907157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26439622288545767170604771 39659433432818650755907157)
                ·
                  refine ⟨464758985540843563545787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39659433432818650755907157 464758985540843563545787)
                  ·
                    rfl

theorem cell22_4073017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_4073017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073017 prefixEnd_4073017 := by exact prefixLift 4073017
  have htrace : WordTrace (prefixWord ++ tailWord_4073017) baseStart_4073017 baseEnd_4073017 := by
    simpa [prefixWord, tailWord_4073017, baseEnd_4073017] using wordTrace_append hprefix tailTrace_4073017
  have hstable : (prefixWord ++ tailWord_4073017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073017).length < 2 ^ (prefixWord ++ tailWord_4073017).sum := by decide
  have hdescent : baseEnd_4073017 < baseStart_4073017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073036 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_4073036 : Nat := 118140960795 + 4073036 * 2 ^ 59
def prefixEnd_4073036 : Nat := 4983230072969 + 3 ^ 40 * 4073036 * 2
def baseEnd_4073036 : Nat := 1394283460710820974412303

theorem tailTrace_4073036 : CollatzResearch.WordTrace tailWord_4073036 prefixEnd_4073036 1394283460710820974412303 := by
  unfold tailWord_4073036
  simp only [CollatzResearch.WordTrace]
  refine ⟨74277913636046833006419481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99037218181395777341892641 74277913636046833006419481)
  ·
    refine ⟨55708435227035124754814611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74277913636046833006419481 55708435227035124754814611)
    ·
      refine ⟨83562652840552687132221917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55708435227035124754814611 83562652840552687132221917)
      ·
        refine ⟨31335994815207257674583219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83562652840552687132221917 31335994815207257674583219)
        ·
          refine ⟨47003992222810886511874829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31335994815207257674583219 47003992222810886511874829)
          ·
            refine ⟨17626497083554082441953061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47003992222810886511874829 17626497083554082441953061)
            ·
              refine ⟨3304968203166390457866199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17626497083554082441953061 3304968203166390457866199)
              ·
                refine ⟨4957452304749585686799299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304968203166390457866199 4957452304749585686799299)
                ·
                  refine ⟨7436178457124378530198949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957452304749585686799299 7436178457124378530198949)
                  ·
                    refine ⟨1394283460710820974412303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7436178457124378530198949 1394283460710820974412303)
                    ·
                      rfl

theorem cell22_4073036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_4073036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073036 prefixEnd_4073036 := by exact prefixLift 4073036
  have htrace : WordTrace (prefixWord ++ tailWord_4073036) baseStart_4073036 baseEnd_4073036 := by
    simpa [prefixWord, tailWord_4073036, baseEnd_4073036] using wordTrace_append hprefix tailTrace_4073036
  have hstable : (prefixWord ++ tailWord_4073036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073036).length < 2 ^ (prefixWord ++ tailWord_4073036).sum := by decide
  have hdescent : baseEnd_4073036 < baseStart_4073036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073064 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4073064 : Nat := 118140960795 + 4073064 * 2 ^ 59
def prefixEnd_4073064 : Nat := 4983230072969 + 3 ^ 40 * 4073064 * 2
def baseEnd_4073064 : Nat := 1394293045683038234712217

theorem tailTrace_4073064 : CollatzResearch.WordTrace tailWord_4073064 prefixEnd_4073064 1394293045683038234712217 := by
  unfold tailWord_4073064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74278424257996113397429123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99037899010661484529905497 74278424257996113397429123)
  ·
    refine ⟨111417636386994170096143685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74278424257996113397429123 111417636386994170096143685)
    ·
      refine ⟨20890806822561406893026941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111417636386994170096143685 20890806822561406893026941)
      ·
        refine ⟨7834052558460527584885103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20890806822561406893026941 7834052558460527584885103)
        ·
          refine ⟨11751078837690791377327655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7834052558460527584885103 11751078837690791377327655)
          ·
            refine ⟨17626618256536187065991483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11751078837690791377327655 17626618256536187065991483)
            ·
              refine ⟨26439927384804280598987225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17626618256536187065991483 26439927384804280598987225)
              ·
                refine ⟨19829945538603210449240419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26439927384804280598987225 19829945538603210449240419)
                ·
                  refine ⟨29744918307904815673860629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19829945538603210449240419 29744918307904815673860629)
                  ·
                    refine ⟨1394293045683038234712217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29744918307904815673860629 1394293045683038234712217)
                    ·
                      rfl

theorem cell22_4073064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4073064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073064 prefixEnd_4073064 := by exact prefixLift 4073064
  have htrace : WordTrace (prefixWord ++ tailWord_4073064) baseStart_4073064 baseEnd_4073064 := by
    simpa [prefixWord, tailWord_4073064, baseEnd_4073064] using wordTrace_append hprefix tailTrace_4073064
  have hstable : (prefixWord ++ tailWord_4073064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073064).length < 2 ^ (prefixWord ++ tailWord_4073064).sum := by decide
  have hdescent : baseEnd_4073064 < baseStart_4073064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073066 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4073066 : Nat := 118140960795 + 4073066 * 2 ^ 59
def prefixEnd_4073066 : Nat := 4983230072969 + 3 ^ 40 * 4073066 * 2
def baseEnd_4073066 : Nat := 1394293730323910896162211

theorem tailTrace_4073066 : CollatzResearch.WordTrace tailWord_4073066 prefixEnd_4073066 1394293730323910896162211 := by
  unfold tailWord_4073066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37139230365496245284107763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99037947641323320757620701 37139230365496245284107763)
  ·
    refine ⟨55708845548244367926161645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37139230365496245284107763 55708845548244367926161645)
    ·
      refine ⟨20890817080591637972310617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55708845548244367926161645 20890817080591637972310617)
      ·
        refine ⟨15668112810443728479232963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20890817080591637972310617 15668112810443728479232963)
        ·
          refine ⟨23502169215665592718849445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15668112810443728479232963 23502169215665592718849445)
          ·
            refine ⟨4406656727937298634784271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23502169215665592718849445 4406656727937298634784271)
            ·
              refine ⟨6609985091905947952176407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406656727937298634784271 6609985091905947952176407)
              ·
                refine ⟨9914977637858921928264611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609985091905947952176407 9914977637858921928264611)
                ·
                  refine ⟨14872466456788382892396917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914977637858921928264611 14872466456788382892396917)
                  ·
                    refine ⟨1394293730323910896162211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14872466456788382892396917 1394293730323910896162211)
                    ·
                      rfl

theorem cell22_4073066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4073066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073066 prefixEnd_4073066 := by exact prefixLift 4073066
  have htrace : WordTrace (prefixWord ++ tailWord_4073066) baseStart_4073066 baseEnd_4073066 := by
    simpa [prefixWord, tailWord_4073066, baseEnd_4073066] using wordTrace_append hprefix tailTrace_4073066
  have hstable : (prefixWord ++ tailWord_4073066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073066).length < 2 ^ (prefixWord ++ tailWord_4073066).sum := by decide
  have hdescent : baseEnd_4073066 < baseStart_4073066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073096 : List Nat := [2, 1, 3, 5, 1, 2, 8]
def baseStart_4073096 : Nat := 118140960795 + 4073096 * 2 ^ 59
def prefixEnd_4073096 : Nat := 4983230072969 + 3 ^ 40 * 4073096 * 2
def baseEnd_4073096 : Nat := 51640888886555585848597

theorem tailTrace_4073096 : CollatzResearch.WordTrace tailWord_4073096 prefixEnd_4073096 51640888886555585848597 := by
  unfold tailWord_4073096
  simp only [CollatzResearch.WordTrace]
  refine ⟨74279007825938148130011571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99038677101250864173348761 74279007825938148130011571)
  ·
    refine ⟨111418511738907222195017357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74279007825938148130011571 111418511738907222195017357)
    ·
      refine ⟨41781941902090208323131509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111418511738907222195017357 41781941902090208323131509)
      ·
        refine ⟨3917057053320957030293579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41781941902090208323131509 3917057053320957030293579)
        ·
          refine ⟨5875585579981435545440369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917057053320957030293579 5875585579981435545440369)
          ·
            refine ⟨4406689184986076659080277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5875585579981435545440369 4406689184986076659080277)
            ·
              refine ⟨51640888886555585848597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4406689184986076659080277 51640888886555585848597)
              ·
                rfl

theorem cell22_4073096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 8].length) (baseStart_4073096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073096 prefixEnd_4073096 := by exact prefixLift 4073096
  have htrace : WordTrace (prefixWord ++ tailWord_4073096) baseStart_4073096 baseEnd_4073096 := by
    simpa [prefixWord, tailWord_4073096, baseEnd_4073096] using wordTrace_append hprefix tailTrace_4073096
  have hstable : (prefixWord ++ tailWord_4073096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073096).length < 2 ^ (prefixWord ++ tailWord_4073096).sum := by decide
  have hdescent : baseEnd_4073096 < baseStart_4073096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073111 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 3, 3]
def baseStart_4073111 : Nat := 118140960795 + 4073111 * 2 ^ 59
def prefixEnd_4073111 : Nat := 4983230072969 + 3 ^ 40 * 4073111 * 2
def baseEnd_4073111 : Nat := 1394309134743545778787073

theorem tailTrace_4073111 : CollatzResearch.WordTrace tailWord_4073111 prefixEnd_4073111 1394309134743545778787073 := by
  unfold tailWord_4073111
  simp only [CollatzResearch.WordTrace]
  refine ⟨148558562746821953821819187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99039041831214635881212791 148558562746821953821819187)
  ·
    refine ⟨222837844120232930732728781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148558562746821953821819187 222837844120232930732728781)
    ·
      refine ⟨83564191545087349024773293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222837844120232930732728781 83564191545087349024773293)
      ·
        refine ⟨31336571829407755884289985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83564191545087349024773293 31336571829407755884289985)
        ·
          refine ⟨23502428872055816913217489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31336571829407755884289985 23502428872055816913217489)
          ·
            refine ⟨17626821654041862684913117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23502428872055816913217489 17626821654041862684913117)
            ·
              refine ⟨6610058120265698506842419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17626821654041862684913117 6610058120265698506842419)
              ·
                refine ⟨9915087180398547760263629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610058120265698506842419 9915087180398547760263629)
                ·
                  refine ⟨3718157692649455410098861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9915087180398547760263629 3718157692649455410098861)
                  ·
                    refine ⟨1394309134743545778787073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718157692649455410098861 1394309134743545778787073)
                    ·
                      rfl

theorem cell22_4073111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_4073111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073111 prefixEnd_4073111 := by exact prefixLift 4073111
  have htrace : WordTrace (prefixWord ++ tailWord_4073111) baseStart_4073111 baseEnd_4073111 := by
    simpa [prefixWord, tailWord_4073111, baseEnd_4073111] using wordTrace_append hprefix tailTrace_4073111
  have hstable : (prefixWord ++ tailWord_4073111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073111).length < 2 ^ (prefixWord ++ tailWord_4073111).sum := by decide
  have hdescent : baseEnd_4073111 < baseStart_4073111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4073162 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4073162 : Nat := 118140960795 + 4073162 * 2 ^ 59
def prefixEnd_4073162 : Nat := 4983230072969 + 3 ^ 40 * 4073162 * 2
def baseEnd_4073162 : Nat := 1394326593085798645761917

theorem tailTrace_4073162 : CollatzResearch.WordTrace tailWord_4073162 prefixEnd_4073162 1394326593085798645761917 := by
  unfold tailWord_4073162
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140105717409297382981435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99040281913091459687950493 37140105717409297382981435)
  ·
    refine ⟨55710158576113946074472153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37140105717409297382981435 55710158576113946074472153)
    ·
      refine ⟨41782618932085459555854115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55710158576113946074472153 41782618932085459555854115)
      ·
        refine ⟨62673928398128189333781173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41782618932085459555854115 62673928398128189333781173)
        ·
          refine ⟨5875680787324517750041985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62673928398128189333781173 5875680787324517750041985)
          ·
            refine ⟨4406760590493388312531489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5875680787324517750041985 4406760590493388312531489)
            ·
              refine ⟨3305070442870041234398617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4406760590493388312531489 3305070442870041234398617)
              ·
                refine ⟨2478802832152530925798963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3305070442870041234398617 2478802832152530925798963)
                ·
                  refine ⟨3718204248228796388698445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478802832152530925798963 3718204248228796388698445)
                  ·
                    refine ⟨1394326593085798645761917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3718204248228796388698445 1394326593085798645761917)
                    ·
                      rfl

theorem cell22_4073162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4073162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4073162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4073162 prefixEnd_4073162 := by exact prefixLift 4073162
  have htrace : WordTrace (prefixWord ++ tailWord_4073162) baseStart_4073162 baseEnd_4073162 := by
    simpa [prefixWord, tailWord_4073162, baseEnd_4073162] using wordTrace_append hprefix tailTrace_4073162
  have hstable : (prefixWord ++ tailWord_4073162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4073162).length < 2 ^ (prefixWord ++ tailWord_4073162).sum := by decide
  have hdescent : baseEnd_4073162 < baseStart_4073162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4073162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
