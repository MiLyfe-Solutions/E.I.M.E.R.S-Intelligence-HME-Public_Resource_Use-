import V185TrunkScan22Chunk183

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1641402 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_1641402 : Nat := 118140960795 + 1641402 * 2 ^ 59
def prefixEnd_1641402 : Nat := 4983230072969 + 3 ^ 40 * 1641402 * 2
def baseEnd_1641402 : Nat := 561885448834194827217557

theorem tailTrace_1641402 : CollatzResearch.WordTrace tailWord_1641402 prefixEnd_1641402 561885448834194827217557 := by
  unfold tailWord_1641402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966712299872089497141615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39911232799658905325710973 14966712299872089497141615)
  ·
    refine ⟨22450068449808134245712423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14966712299872089497141615 22450068449808134245712423)
    ·
      refine ⟨33675102674712201368568635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22450068449808134245712423 33675102674712201368568635)
      ·
        refine ⟨50512654012068302052852953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33675102674712201368568635 50512654012068302052852953)
        ·
          refine ⟨37884490509051226539639715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50512654012068302052852953 37884490509051226539639715)
          ·
            refine ⟨56826735763576839809459573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37884490509051226539639715 56826735763576839809459573)
            ·
              refine ⟨5327506477835328732136835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56826735763576839809459573 5327506477835328732136835)
              ·
                refine ⟨7991259716752993098205253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327506477835328732136835 7991259716752993098205253)
                ·
                  refine ⟨1498361196891186205913485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7991259716752993098205253 1498361196891186205913485)
                  ·
                    refine ⟨561885448834194827217557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498361196891186205913485 561885448834194827217557)
                    ·
                      rfl

theorem cell22_1641402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_1641402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641402 prefixEnd_1641402 := by exact prefixLift 1641402
  have htrace : WordTrace (prefixWord ++ tailWord_1641402) baseStart_1641402 baseEnd_1641402 := by
    simpa [prefixWord, tailWord_1641402, baseEnd_1641402] using wordTrace_append hprefix tailTrace_1641402
  have hstable : (prefixWord ++ tailWord_1641402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641402).length < 2 ^ (prefixWord ++ tailWord_1641402).sum := by decide
  have hdescent : baseEnd_1641402 < baseStart_1641402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641432 : List Nat := [2, 1, 2, 2, 2, 3, 4, 6]
def baseStart_1641432 : Nat := 118140960795 + 1641432 * 2 ^ 59
def prefixEnd_1641432 : Nat := 4983230072969 + 3 ^ 40 * 1641432 * 2
def baseEnd_1641432 : Nat := 62432857605253860996385

theorem tailTrace_1641432 : CollatzResearch.WordTrace tailWord_1641432 prefixEnd_1641432 62432857605253860996385 := by
  unfold tailWord_1641432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933971694689836556079275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39911962259586448741439033 29933971694689836556079275)
  ·
    refine ⟨44900957542034754834118913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933971694689836556079275 44900957542034754834118913)
    ·
      refine ⟨33675718156526066125589185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44900957542034754834118913 33675718156526066125589185)
      ·
        refine ⟨25256788617394549594191889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33675718156526066125589185 25256788617394549594191889)
        ·
          refine ⟨18942591463045912195643917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25256788617394549594191889 18942591463045912195643917)
          ·
            refine ⟨7103471798642217073366469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18942591463045912195643917 7103471798642217073366469)
            ·
              refine ⟨1331900962245415701256213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7103471798642217073366469 1331900962245415701256213)
              ·
                refine ⟨62432857605253860996385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1331900962245415701256213 62432857605253860996385)
                ·
                  rfl

theorem cell22_1641432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_1641432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641432 prefixEnd_1641432 := by exact prefixLift 1641432
  have htrace : WordTrace (prefixWord ++ tailWord_1641432) baseStart_1641432 baseEnd_1641432 := by
    simpa [prefixWord, tailWord_1641432, baseEnd_1641432] using wordTrace_append hprefix tailTrace_1641432
  have hstable : (prefixWord ++ tailWord_1641432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641432).length < 2 ^ (prefixWord ++ tailWord_1641432).sum := by decide
  have hdescent : baseEnd_1641432 < baseStart_1641432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641470 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1641470 : Nat := 118140960795 + 1641470 * 2 ^ 59
def prefixEnd_1641470 : Nat := 4983230072969 + 3 ^ 40 * 1641470 * 2
def baseEnd_1641470 : Nat := 561908726623865316517349

theorem tailTrace_1641470 : CollatzResearch.WordTrace tailWord_1641470 prefixEnd_1641470 561908726623865316517349 := by
  unfold tailWord_1641470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483666170405250700255233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39912886242161337068027909 7483666170405250700255233)
  ·
    refine ⟨5612749627803938025191425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7483666170405250700255233 5612749627803938025191425)
    ·
      refine ⟨4209562220852953518893569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5612749627803938025191425 4209562220852953518893569)
      ·
        refine ⟨3157171665639715139170177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209562220852953518893569 3157171665639715139170177)
        ·
          refine ⟨2367878749229786354377633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157171665639715139170177 2367878749229786354377633)
          ·
            refine ⟨1775909061922339765783225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367878749229786354377633 1775909061922339765783225)
            ·
              refine ⟨1331931796441754824337419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775909061922339765783225 1331931796441754824337419)
              ·
                refine ⟨1997897694662632236506129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331931796441754824337419 1997897694662632236506129)
                ·
                  refine ⟨1498423270996974177379597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1997897694662632236506129 1498423270996974177379597)
                  ·
                    refine ⟨561908726623865316517349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498423270996974177379597 561908726623865316517349)
                    ·
                      rfl

theorem cell22_1641470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1641470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641470 prefixEnd_1641470 := by exact prefixLift 1641470
  have htrace : WordTrace (prefixWord ++ tailWord_1641470) baseStart_1641470 baseEnd_1641470 := by
    simpa [prefixWord, tailWord_1641470, baseEnd_1641470] using wordTrace_append hprefix tailTrace_1641470
  have hstable : (prefixWord ++ tailWord_1641470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641470).length < 2 ^ (prefixWord ++ tailWord_1641470).sum := by decide
  have hdescent : baseEnd_1641470 < baseStart_1641470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641477 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 5]
def baseStart_1641477 : Nat := 118140960795 + 1641477 * 2 ^ 59
def prefixEnd_1641477 : Nat := 4983230072969 + 3 ^ 40 * 1641477 * 2
def baseEnd_1641477 : Nat := 187303707622306543864109

theorem tailTrace_1641477 : CollatzResearch.WordTrace tailWord_1641477 prefixEnd_1641477 187303707622306543864109 := by
  unfold tailWord_1641477
  simp only [CollatzResearch.WordTrace]
  refine ⟨59869584674216645797546685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39913056449477763865031123 59869584674216645797546685)
  ·
    refine ⟨22451094252831242174080007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59869584674216645797546685 22451094252831242174080007)
    ·
      refine ⟨33676641379246863261120011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22451094252831242174080007 33676641379246863261120011)
      ·
        refine ⟨50514962068870294891680017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33676641379246863261120011 50514962068870294891680017)
        ·
          refine ⟨37886221551652721168760013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50514962068870294891680017 37886221551652721168760013)
          ·
            refine ⟨14207333081869770438285005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37886221551652721168760013 14207333081869770438285005)
            ·
              refine ⟨5327749905701163914356877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14207333081869770438285005 5327749905701163914356877)
              ·
                refine ⟨1997906214637936467883829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5327749905701163914356877 1997906214637936467883829)
                ·
                  refine ⟨187303707622306543864109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997906214637936467883829 187303707622306543864109)
                  ·
                    rfl

theorem cell22_1641477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_1641477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641477 prefixEnd_1641477 := by exact prefixLift 1641477
  have htrace : WordTrace (prefixWord ++ tailWord_1641477) baseStart_1641477 baseEnd_1641477 := by
    simpa [prefixWord, tailWord_1641477, baseEnd_1641477] using wordTrace_append hprefix tailTrace_1641477
  have hstable : (prefixWord ++ tailWord_1641477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641477).length < 2 ^ (prefixWord ++ tailWord_1641477).sum := by decide
  have hdescent : baseEnd_1641477 < baseStart_1641477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641511 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 5]
def baseStart_1641511 : Nat := 118140960795 + 1641511 * 2 ^ 59
def prefixEnd_1641511 : Nat := 4983230072969 + 3 ^ 40 * 1641511 * 2
def baseEnd_1641511 : Nat := 187307587253918292080741

theorem tailTrace_1641511 : CollatzResearch.WordTrace tailWord_1641511 prefixEnd_1641511 187307587253918292080741 := by
  unfold tailWord_1641511
  simp only [CollatzResearch.WordTrace]
  refine ⟨59870824756093469604284387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39913883170728979736189591 59870824756093469604284387)
  ·
    refine ⟨89806237134140204406426581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59870824756093469604284387 89806237134140204406426581)
    ·
      refine ⟨2104833682831411040775623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 89806237134140204406426581 2104833682831411040775623)
      ·
        refine ⟨3157250524247116561163435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104833682831411040775623 3157250524247116561163435)
        ·
          refine ⟨4735875786370674841745153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157250524247116561163435 4735875786370674841745153)
          ·
            refine ⟨3551906839778006131308865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735875786370674841745153 3551906839778006131308865)
            ·
              refine ⟨2663930129833504598481649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551906839778006131308865 2663930129833504598481649)
              ·
                refine ⟨1997947597375128448861237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663930129833504598481649 1997947597375128448861237)
                ·
                  refine ⟨187307587253918292080741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997947597375128448861237 187307587253918292080741)
                  ·
                    rfl

theorem cell22_1641511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 5].length) (baseStart_1641511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641511 prefixEnd_1641511 := by exact prefixLift 1641511
  have htrace : WordTrace (prefixWord ++ tailWord_1641511) baseStart_1641511 baseEnd_1641511 := by
    simpa [prefixWord, tailWord_1641511, baseEnd_1641511] using wordTrace_append hprefix tailTrace_1641511
  have hstable : (prefixWord ++ tailWord_1641511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641511).length < 2 ^ (prefixWord ++ tailWord_1641511).sum := by decide
  have hdescent : baseEnd_1641511 < baseStart_1641511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641522 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1641522 : Nat := 118140960795 + 1641522 * 2 ^ 59
def prefixEnd_1641522 : Nat := 4983230072969 + 3 ^ 40 * 1641522 * 2
def baseEnd_1641522 : Nat := 187308842428851504739063

theorem tailTrace_1641522 : CollatzResearch.WordTrace tailWord_1641522 prefixEnd_1641522 187308842428851504739063 := by
  unfold tailWord_1641522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14967806489763404620733705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39914150639369078988623213 14967806489763404620733705)
  ·
    refine ⟨11225854867322553465550279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14967806489763404620733705 11225854867322553465550279)
    ·
      refine ⟨16838782300983830198325419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11225854867322553465550279 16838782300983830198325419)
      ·
        refine ⟨25258173451475745297488129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16838782300983830198325419 25258173451475745297488129)
        ·
          refine ⟨18943630088606808973116097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25258173451475745297488129 18943630088606808973116097)
          ·
            refine ⟨14207722566455106729837073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18943630088606808973116097 14207722566455106729837073)
            ·
              refine ⟨10655791924841330047377805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14207722566455106729837073 10655791924841330047377805)
              ·
                refine ⟨3995921971815498767766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10655791924841330047377805 3995921971815498767766677)
                ·
                  refine ⟨187308842428851504739063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3995921971815498767766677 187308842428851504739063)
                  ·
                    rfl

theorem cell22_1641522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1641522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641522 prefixEnd_1641522 := by exact prefixLift 1641522
  have htrace : WordTrace (prefixWord ++ tailWord_1641522) baseStart_1641522 baseEnd_1641522 := by
    simpa [prefixWord, tailWord_1641522, baseEnd_1641522] using wordTrace_append hprefix tailTrace_1641522
  have hstable : (prefixWord ++ tailWord_1641522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641522).length < 2 ^ (prefixWord ++ tailWord_1641522).sum := by decide
  have hdescent : baseEnd_1641522 < baseStart_1641522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641554 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1641554 : Nat := 118140960795 + 1641554 * 2 ^ 59
def prefixEnd_1641554 : Nat := 4983230072969 + 3 ^ 40 * 1641554 * 2
def baseEnd_1641554 : Nat := 561937481540517097417091

theorem tailTrace_1641554 : CollatzResearch.WordTrace tailWord_1641554 prefixEnd_1641554 561937481540517097417091 := by
  unfold tailWord_1641554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968098273734421987024929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39914928729958458632066477 14968098273734421987024929)
  ·
    refine ⟨11226073705300816490268697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14968098273734421987024929 11226073705300816490268697)
    ·
      refine ⟨8419555278975612367701523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11226073705300816490268697 8419555278975612367701523)
      ·
        refine ⟨12629332918463418551552285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419555278975612367701523 12629332918463418551552285)
        ·
          refine ⟨4735999844423781956832107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12629332918463418551552285 4735999844423781956832107)
          ·
            refine ⟨7103999766635672935248161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735999844423781956832107 7103999766635672935248161)
            ·
              refine ⟨5327999824976754701436121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7103999766635672935248161 5327999824976754701436121)
              ·
                refine ⟨3995999868732566026077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5327999824976754701436121 3995999868732566026077091)
                ·
                  refine ⟨5993999803098849039115637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995999868732566026077091 5993999803098849039115637)
                  ·
                    refine ⟨561937481540517097417091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5993999803098849039115637 561937481540517097417091)
                    ·
                      rfl

theorem cell22_1641554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1641554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641554 prefixEnd_1641554 := by exact prefixLift 1641554
  have htrace : WordTrace (prefixWord ++ tailWord_1641554) baseStart_1641554 baseEnd_1641554 := by
    simpa [prefixWord, tailWord_1641554, baseEnd_1641554] using wordTrace_append hprefix tailTrace_1641554
  have hstable : (prefixWord ++ tailWord_1641554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641554).length < 2 ^ (prefixWord ++ tailWord_1641554).sum := by decide
  have hdescent : baseEnd_1641554 < baseStart_1641554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641601 : List Nat := [1, 2, 4, 2, 2, 3, 2, 6]
def baseStart_1641601 : Nat := 118140960795 + 1641601 * 2 ^ 59
def prefixEnd_1641601 : Nat := 4983230072969 + 3 ^ 40 * 1641601 * 2
def baseEnd_1641601 : Nat := 62439285622336071276883

theorem tailTrace_1641601 : CollatzResearch.WordTrace tailWord_1641601 prefixEnd_1641601 62439285622336071276883 := by
  unfold tailWord_1641601
  simp only [CollatzResearch.WordTrace]
  refine ⟨59874107325767414975060657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39916071550511609983373771 59874107325767414975060657)
  ·
    refine ⟨44905580494325561231295493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59874107325767414975060657 44905580494325561231295493)
    ·
      refine ⟨8419796342686042730867905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44905580494325561231295493 8419796342686042730867905)
      ·
        refine ⟨6314847257014532048150929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8419796342686042730867905 6314847257014532048150929)
        ·
          refine ⟨4736135442760899036113197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6314847257014532048150929 4736135442760899036113197)
          ·
            refine ⟨1776050791035337138542449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4736135442760899036113197 1776050791035337138542449)
            ·
              refine ⟨1332038093276502853906837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776050791035337138542449 1332038093276502853906837)
              ·
                refine ⟨62439285622336071276883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1332038093276502853906837 62439285622336071276883)
                ·
                  rfl

theorem cell22_1641601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 6].length) (baseStart_1641601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641601 prefixEnd_1641601 := by exact prefixLift 1641601
  have htrace : WordTrace (prefixWord ++ tailWord_1641601) baseStart_1641601 baseEnd_1641601 := by
    simpa [prefixWord, tailWord_1641601, baseEnd_1641601] using wordTrace_append hprefix tailTrace_1641601
  have hstable : (prefixWord ++ tailWord_1641601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641601).length < 2 ^ (prefixWord ++ tailWord_1641601).sum := by decide
  have hdescent : baseEnd_1641601 < baseStart_1641601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641616 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 1, 3]
def baseStart_1641616 : Nat := 118140960795 + 1641616 * 2 ^ 59
def prefixEnd_1641616 : Nat := 4983230072969 + 3 ^ 40 * 1641616 * 2
def baseEnd_1641616 : Nat := 561958705407569602366901

theorem tailTrace_1641616 : CollatzResearch.WordTrace tailWord_1641616 prefixEnd_1641616 561958705407569602366901 := by
  unfold tailWord_1641616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29937327210356536268428351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39916436280475381691237801 29937327210356536268428351)
  ·
    refine ⟨44905990815534804402642527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29937327210356536268428351 44905990815534804402642527)
    ·
      refine ⟨67358986223302206603963791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44905990815534804402642527 67358986223302206603963791)
      ·
        refine ⟨101038479334953309905945687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67358986223302206603963791 101038479334953309905945687)
        ·
          refine ⟨151557719002429964858918531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101038479334953309905945687 151557719002429964858918531)
          ·
            refine ⟨227336578503644947288377797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151557719002429964858918531 227336578503644947288377797)
            ·
              refine ⟨42625608469433427616570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227336578503644947288377797 42625608469433427616570837)
              ·
                refine ⟨999037698502345959763379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42625608469433427616570837 999037698502345959763379)
                ·
                  refine ⟨1498556547753518939645069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999037698502345959763379 1498556547753518939645069)
                  ·
                    refine ⟨561958705407569602366901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498556547753518939645069 561958705407569602366901)
                    ·
                      rfl

theorem cell22_1641616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_1641616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641616 prefixEnd_1641616 := by exact prefixLift 1641616
  have htrace : WordTrace (prefixWord ++ tailWord_1641616) baseStart_1641616 baseEnd_1641616 := by
    simpa [prefixWord, tailWord_1641616, baseEnd_1641616] using wordTrace_append hprefix tailTrace_1641616
  have hstable : (prefixWord ++ tailWord_1641616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641616).length < 2 ^ (prefixWord ++ tailWord_1641616).sum := by decide
  have hdescent : baseEnd_1641616 < baseStart_1641616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641629 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 5]
def baseStart_1641629 : Nat := 118140960795 + 1641629 * 2 ^ 59
def prefixEnd_1641629 : Nat := 4983230072969 + 3 ^ 40 * 1641629 * 2
def baseEnd_1641629 : Nat := 187321051857747300597287

theorem tailTrace_1641629 : CollatzResearch.WordTrace tailWord_1641629 prefixEnd_1641629 187321051857747300597287 := by
  unfold tailWord_1641629
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875128569665975757079941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39916752379777317171386627 59875128569665975757079941)
  ·
    refine ⟨11226586606812370454452489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59875128569665975757079941 11226586606812370454452489)
    ·
      refine ⟨8419939955109277840839367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11226586606812370454452489 8419939955109277840839367)
      ·
        refine ⟨12629909932663916761259051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419939955109277840839367 12629909932663916761259051)
        ·
          refine ⟨18944864898995875141888577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12629909932663916761259051 18944864898995875141888577)
          ·
            refine ⟨14208648674246906356416433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18944864898995875141888577 14208648674246906356416433)
            ·
              refine ⟨10656486505685179767312325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14208648674246906356416433 10656486505685179767312325)
              ·
                refine ⟨1998091219815971206371061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10656486505685179767312325 1998091219815971206371061)
                ·
                  refine ⟨187321051857747300597287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998091219815971206371061 187321051857747300597287)
                  ·
                    rfl

theorem cell22_1641629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_1641629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641629 prefixEnd_1641629 := by exact prefixLift 1641629
  have htrace : WordTrace (prefixWord ++ tailWord_1641629) baseStart_1641629 baseEnd_1641629 := by
    simpa [prefixWord, tailWord_1641629, baseEnd_1641629] using wordTrace_append hprefix tailTrace_1641629
  have hstable : (prefixWord ++ tailWord_1641629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641629).length < 2 ^ (prefixWord ++ tailWord_1641629).sum := by decide
  have hdescent : baseEnd_1641629 < baseStart_1641629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641659 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 1, 4]
def baseStart_1641659 : Nat := 118140960795 + 1641659 * 2 ^ 59
def prefixEnd_1641659 : Nat := 4983230072969 + 3 ^ 40 * 1641659 * 2
def baseEnd_1641659 : Nat := 561973425186331823541769

theorem tailTrace_1641659 : CollatzResearch.WordTrace tailWord_1641659 prefixEnd_1641659 561973425186331823541769 := by
  unfold tailWord_1641659
  simp only [CollatzResearch.WordTrace]
  refine ⟨59876222759557290880672031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39917481839704860587114687 59876222759557290880672031)
  ·
    refine ⟨89814334139335936321008047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59876222759557290880672031 89814334139335936321008047)
    ·
      refine ⟨134721501209003904481512071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89814334139335936321008047 134721501209003904481512071)
      ·
        refine ⟨202082251813505856722268107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134721501209003904481512071 202082251813505856722268107)
        ·
          refine ⟨303123377720258785083402161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202082251813505856722268107 303123377720258785083402161)
          ·
            refine ⟨227342533290194088812551621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303123377720258785083402161 227342533290194088812551621)
            ·
              refine ⟨42626724991911391652353429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227342533290194088812551621 42626724991911391652353429)
              ·
                refine ⟨1998127733995846483704067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42626724991911391652353429 1998127733995846483704067)
                ·
                  refine ⟨2997191600993769725556101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998127733995846483704067 2997191600993769725556101)
                  ·
                    refine ⟨561973425186331823541769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997191600993769725556101 561973425186331823541769)
                    ·
                      rfl

theorem cell22_1641659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4].length) (baseStart_1641659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641659 prefixEnd_1641659 := by exact prefixLift 1641659
  have htrace : WordTrace (prefixWord ++ tailWord_1641659) baseStart_1641659 baseEnd_1641659 := by
    simpa [prefixWord, tailWord_1641659, baseEnd_1641659] using wordTrace_append hprefix tailTrace_1641659
  have hstable : (prefixWord ++ tailWord_1641659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641659).length < 2 ^ (prefixWord ++ tailWord_1641659).sum := by decide
  have hdescent : baseEnd_1641659 < baseStart_1641659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641684 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1641684 : Nat := 118140960795 + 1641684 * 2 ^ 59
def prefixEnd_1641684 : Nat := 4983230072969 + 3 ^ 40 * 1641684 * 2
def baseEnd_1641684 : Nat := 561981983197240091666693

theorem tailTrace_1641684 : CollatzResearch.WordTrace tailWord_1641684 prefixEnd_1641684 561981983197240091666693 := by
  unfold tailWord_1641684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29938567292233360075166053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39918089722977813433554737 29938567292233360075166053)
  ·
    refine ⟨5613481367293755014093635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29938567292233360075166053 5613481367293755014093635)
    ·
      refine ⟨8420222050940632521140453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613481367293755014093635 8420222050940632521140453)
      ·
        refine ⟨1578791634551368597713835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8420222050940632521140453 1578791634551368597713835)
        ·
          refine ⟨2368187451827052896570753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578791634551368597713835 2368187451827052896570753)
          ·
            refine ⟨1776140588870289672428065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2368187451827052896570753 1776140588870289672428065)
            ·
              refine ⟨1332105441652717254321049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776140588870289672428065 1332105441652717254321049)
              ·
                refine ⟨999079081239537940740787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332105441652717254321049 999079081239537940740787)
                ·
                  refine ⟨1498618621859306911111181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999079081239537940740787 1498618621859306911111181)
                  ·
                    refine ⟨561981983197240091666693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498618621859306911111181 561981983197240091666693)
                    ·
                      rfl

theorem cell22_1641684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1641684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641684 prefixEnd_1641684 := by exact prefixLift 1641684
  have htrace : WordTrace (prefixWord ++ tailWord_1641684) baseStart_1641684 baseEnd_1641684 := by
    simpa [prefixWord, tailWord_1641684, baseEnd_1641684] using wordTrace_append hprefix tailTrace_1641684
  have hstable : (prefixWord ++ tailWord_1641684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641684).length < 2 ^ (prefixWord ++ tailWord_1641684).sum := by decide
  have hdescent : baseEnd_1641684 < baseStart_1641684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641704 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1641704 : Nat := 118140960795 + 1641704 * 2 ^ 59
def prefixEnd_1641704 : Nat := 4983230072969 + 3 ^ 40 * 1641704 * 2
def baseEnd_1641704 : Nat := 561988829605966706166631

theorem tailTrace_1641704 : CollatzResearch.WordTrace tailWord_1641704 prefixEnd_1641704 561988829605966706166631 := by
  unfold tailWord_1641704
  simp only [CollatzResearch.WordTrace]
  refine ⟨29938932022197131783030083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39918576029596175710706777 29938932022197131783030083)
  ·
    refine ⟨44908398033295697674545125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29938932022197131783030083 44908398033295697674545125)
    ·
      refine ⟨8420324631242943313977211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44908398033295697674545125 8420324631242943313977211)
      ·
        refine ⟨12630486946864414970965817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8420324631242943313977211 12630486946864414970965817)
        ·
          refine ⟨9472865210148311228224363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12630486946864414970965817 9472865210148311228224363)
          ·
            refine ⟨14209297815222466842336545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9472865210148311228224363 14209297815222466842336545)
            ·
              refine ⟨10656973361416850131752409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14209297815222466842336545 10656973361416850131752409)
              ·
                refine ⟨7992730021062637598814307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10656973361416850131752409 7992730021062637598814307)
                ·
                  refine ⟨11989095031593956398221461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7992730021062637598814307 11989095031593956398221461)
                  ·
                    refine ⟨561988829605966706166631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11989095031593956398221461 561988829605966706166631)
                    ·
                      rfl

theorem cell22_1641704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1641704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641704 prefixEnd_1641704 := by exact prefixLift 1641704
  have htrace : WordTrace (prefixWord ++ tailWord_1641704) baseStart_1641704 baseEnd_1641704 := by
    simpa [prefixWord, tailWord_1641704, baseEnd_1641704] using wordTrace_append hprefix tailTrace_1641704
  have hstable : (prefixWord ++ tailWord_1641704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641704).length < 2 ^ (prefixWord ++ tailWord_1641704).sum := by decide
  have hdescent : baseEnd_1641704 < baseStart_1641704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641706 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1641706 : Nat := 118140960795 + 1641706 * 2 ^ 59
def prefixEnd_1641706 : Nat := 4983230072969 + 3 ^ 40 * 1641706 * 2
def baseEnd_1641706 : Nat := 561989514246839367616625

theorem tailTrace_1641706 : CollatzResearch.WordTrace tailWord_1641706 prefixEnd_1641706 561989514246839367616625 := by
  unfold tailWord_1641706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969484247596754476908243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39918624660258011938421981 14969484247596754476908243)
  ·
    refine ⟨22454226371395131715362365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14969484247596754476908243 22454226371395131715362365)
    ·
      refine ⟨8420334889273174393260887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22454226371395131715362365 8420334889273174393260887)
      ·
        refine ⟨12630502333909761589891331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8420334889273174393260887 12630502333909761589891331)
        ·
          refine ⟨18945753500864642384836997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12630502333909761589891331 18945753500864642384836997)
          ·
            refine ⟨3552328781412120447156937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18945753500864642384836997 3552328781412120447156937)
            ·
              refine ⟨2664246586059090335367703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552328781412120447156937 2664246586059090335367703)
              ·
                refine ⟨3996369879088635503051555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664246586059090335367703 3996369879088635503051555)
                ·
                  refine ⟨5994554818632953254577333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996369879088635503051555 5994554818632953254577333)
                  ·
                    refine ⟨561989514246839367616625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5994554818632953254577333 561989514246839367616625)
                    ·
                      rfl

theorem cell22_1641706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1641706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641706 prefixEnd_1641706 := by exact prefixLift 1641706
  have htrace : WordTrace (prefixWord ++ tailWord_1641706) baseStart_1641706 baseEnd_1641706 := by
    simpa [prefixWord, tailWord_1641706, baseEnd_1641706] using wordTrace_append hprefix tailTrace_1641706
  have hstable : (prefixWord ++ tailWord_1641706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641706).length < 2 ^ (prefixWord ++ tailWord_1641706).sum := by decide
  have hdescent : baseEnd_1641706 < baseStart_1641706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641768 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1641768 : Nat := 118140960795 + 1641768 * 2 ^ 59
def prefixEnd_1641768 : Nat := 4983230072969 + 3 ^ 40 * 1641768 * 2
def baseEnd_1641768 : Nat := 562010738113891872566435

theorem tailTrace_1641768 : CollatzResearch.WordTrace tailWord_1641768 prefixEnd_1641768 562010738113891872566435 := by
  unfold tailWord_1641768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29940099158081201248194979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39920132210774934997593305 29940099158081201248194979)
  ·
    refine ⟨44910148737121801872292469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29940099158081201248194979 44910148737121801872292469)
    ·
      refine ⟨4210326444105168925527419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44910148737121801872292469 4210326444105168925527419)
      ·
        refine ⟨6315489666157753388291129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210326444105168925527419 6315489666157753388291129)
        ·
          refine ⟨4736617249618315041218347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6315489666157753388291129 4736617249618315041218347)
          ·
            refine ⟨7104925874427472561827521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736617249618315041218347 7104925874427472561827521)
            ·
              refine ⟨5328694405820604421370641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104925874427472561827521 5328694405820604421370641)
              ·
                refine ⟨3996520804365453316027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328694405820604421370641 3996520804365453316027981)
                ·
                  refine ⟨1498695301637044993510493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3996520804365453316027981 1498695301637044993510493)
                  ·
                    refine ⟨562010738113891872566435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498695301637044993510493 562010738113891872566435)
                    ·
                      rfl

theorem cell22_1641768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1641768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641768 prefixEnd_1641768 := by exact prefixLift 1641768
  have htrace : WordTrace (prefixWord ++ tailWord_1641768) baseStart_1641768 baseEnd_1641768 := by
    simpa [prefixWord, tailWord_1641768, baseEnd_1641768] using wordTrace_append hprefix tailTrace_1641768
  have hstable : (prefixWord ++ tailWord_1641768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641768).length < 2 ^ (prefixWord ++ tailWord_1641768).sum := by decide
  have hdescent : baseEnd_1641768 < baseStart_1641768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641826 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1641826 : Nat := 118140960795 + 1641826 * 2 ^ 59
def prefixEnd_1641826 : Nat := 4983230072969 + 3 ^ 40 * 1641826 * 2
def baseEnd_1641826 : Nat := 187343530899733018205419

theorem tailTrace_1641826 : CollatzResearch.WordTrace tailWord_1641826 prefixEnd_1641826 187343530899733018205419 := by
  unfold tailWord_1641826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970578437488069600500333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39921542499968185601334221 14970578437488069600500333)
  ·
    refine ⟨5613966914058026100187625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14970578437488069600500333 5613966914058026100187625)
    ·
      refine ⟨4210475185543519575140719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5613966914058026100187625 4210475185543519575140719)
      ·
        refine ⟨6315712778315279362711079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210475185543519575140719 6315712778315279362711079)
        ·
          refine ⟨9473569167472919044066619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315712778315279362711079 9473569167472919044066619)
          ·
            refine ⟨14210353751209378566099929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9473569167472919044066619 14210353751209378566099929)
            ·
              refine ⟨10657765313407033924574947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14210353751209378566099929 10657765313407033924574947)
              ·
                refine ⟨15986647970110550886862421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10657765313407033924574947 15986647970110550886862421)
                ·
                  refine ⟨187343530899733018205419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15986647970110550886862421 187343530899733018205419)
                  ·
                    rfl

theorem cell22_1641826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1641826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641826 prefixEnd_1641826 := by exact prefixLift 1641826
  have htrace : WordTrace (prefixWord ++ tailWord_1641826) baseStart_1641826 baseEnd_1641826 := by
    simpa [prefixWord, tailWord_1641826, baseEnd_1641826] using wordTrace_append hprefix tailTrace_1641826
  have hstable : (prefixWord ++ tailWord_1641826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641826).length < 2 ^ (prefixWord ++ tailWord_1641826).sum := by decide
  have hdescent : baseEnd_1641826 < baseStart_1641826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641828 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1641828 : Nat := 118140960795 + 1641828 * 2 ^ 59
def prefixEnd_1641828 : Nat := 4983230072969 + 3 ^ 40 * 1641828 * 2
def baseEnd_1641828 : Nat := 562031277340071716066251

theorem tailTrace_1641828 : CollatzResearch.WordTrace tailWord_1641828 prefixEnd_1641828 562031277340071716066251 := by
  unfold tailWord_1641828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941193347972516371787069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39921591130630021829049425 29941193347972516371787069)
  ·
    refine ⟨11227947505489693639420151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29941193347972516371787069 11227947505489693639420151)
    ·
      refine ⟨16841921258234540459130227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11227947505489693639420151 16841921258234540459130227)
      ·
        refine ⟨25262881887351810688695341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16841921258234540459130227 25262881887351810688695341)
        ·
          refine ⟨9473580707756929008260753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25262881887351810688695341 9473580707756929008260753)
          ·
            refine ⟨7105185530817696756195565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9473580707756929008260753 7105185530817696756195565)
            ·
              refine ⟨2664444574056636283573337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7105185530817696756195565 2664444574056636283573337)
              ·
                refine ⟨1998333430542477212680003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664444574056636283573337 1998333430542477212680003)
                ·
                  refine ⟨2997500145813715819020005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998333430542477212680003 2997500145813715819020005)
                  ·
                    refine ⟨562031277340071716066251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997500145813715819020005 562031277340071716066251)
                    ·
                      rfl

theorem cell22_1641828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1641828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641828 prefixEnd_1641828 := by exact prefixLift 1641828
  have htrace : WordTrace (prefixWord ++ tailWord_1641828) baseStart_1641828 baseEnd_1641828 := by
    simpa [prefixWord, tailWord_1641828, baseEnd_1641828] using wordTrace_append hprefix tailTrace_1641828
  have hstable : (prefixWord ++ tailWord_1641828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641828).length < 2 ^ (prefixWord ++ tailWord_1641828).sum := by decide
  have hdescent : baseEnd_1641828 < baseStart_1641828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641841 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_1641841 : Nat := 118140960795 + 1641841 * 2 ^ 59
def prefixEnd_1641841 : Nat := 4983230072969 + 3 ^ 40 * 1641841 * 2
def baseEnd_1641841 : Nat := 562035727505744015491211

theorem tailTrace_1641841 : CollatzResearch.WordTrace tailWord_1641841 prefixEnd_1641841 562035727505744015491211 := by
  unfold tailWord_1641841
  simp only [CollatzResearch.WordTrace]
  refine ⟨59882860844897935963797377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39921907229931957309198251 59882860844897935963797377)
  ·
    refine ⟨44912145633673451972848033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59882860844897935963797377 44912145633673451972848033)
    ·
      refine ⟨33684109225255088979636025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44912145633673451972848033 33684109225255088979636025)
      ·
        refine ⟨25263081918941316734727019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33684109225255088979636025 25263081918941316734727019)
        ·
          refine ⟨37894622878411975102090529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25263081918941316734727019 37894622878411975102090529)
          ·
            refine ⟨28420967158808981326567897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37894622878411975102090529 28420967158808981326567897)
            ·
              refine ⟨21315725369106735994925923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28420967158808981326567897 21315725369106735994925923)
              ·
                refine ⟨31973588053660103992388885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21315725369106735994925923 31973588053660103992388885)
                ·
                  refine ⟨1498761940015317374643229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31973588053660103992388885 1498761940015317374643229)
                  ·
                    refine ⟨562035727505744015491211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498761940015317374643229 562035727505744015491211)
                    ·
                      rfl

theorem cell22_1641841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_1641841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641841 prefixEnd_1641841 := by exact prefixLift 1641841
  have htrace : WordTrace (prefixWord ++ tailWord_1641841) baseStart_1641841 baseEnd_1641841 := by
    simpa [prefixWord, tailWord_1641841, baseEnd_1641841] using wordTrace_append hprefix tailTrace_1641841
  have hstable : (prefixWord ++ tailWord_1641841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641841).length < 2 ^ (prefixWord ++ tailWord_1641841).sum := by decide
  have hdescent : baseEnd_1641841 < baseStart_1641841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641860 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1641860 : Nat := 118140960795 + 1641860 * 2 ^ 59
def prefixEnd_1641860 : Nat := 4983230072969 + 3 ^ 40 * 1641860 * 2
def baseEnd_1641860 : Nat := 187347410531344766422051

theorem tailTrace_1641860 : CollatzResearch.WordTrace tailWord_1641860 prefixEnd_1641860 187347410531344766422051 := by
  unfold tailWord_1641860
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941776915914551104369517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39922369221219401472492689 29941776915914551104369517)
  ·
    refine ⟨11228166343467956664138569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29941776915914551104369517 11228166343467956664138569)
    ·
      refine ⟨8421124757600967498103927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11228166343467956664138569 8421124757600967498103927)
      ·
        refine ⟨12631687136401451247155891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421124757600967498103927 12631687136401451247155891)
        ·
          refine ⟨18947530704602176870733837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631687136401451247155891 18947530704602176870733837)
          ·
            refine ⟨7105324014225816326525189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18947530704602176870733837 7105324014225816326525189)
            ·
              refine ⟨1332248252667340561223473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7105324014225816326525189 1332248252667340561223473)
              ·
                refine ⟨999186189500505420917605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332248252667340561223473 999186189500505420917605)
                ·
                  refine ⟨187347410531344766422051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999186189500505420917605 187347410531344766422051)
                  ·
                    rfl

theorem cell22_1641860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1641860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641860 prefixEnd_1641860 := by exact prefixLift 1641860
  have htrace : WordTrace (prefixWord ++ tailWord_1641860) baseStart_1641860 baseEnd_1641860 := by
    simpa [prefixWord, tailWord_1641860, baseEnd_1641860] using wordTrace_append hprefix tailTrace_1641860
  have hstable : (prefixWord ++ tailWord_1641860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641860).length < 2 ^ (prefixWord ++ tailWord_1641860).sum := by decide
  have hdescent : baseEnd_1641860 < baseStart_1641860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641890 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1641890 : Nat := 118140960795 + 1641890 * 2 ^ 59
def prefixEnd_1641890 : Nat := 4983230072969 + 3 ^ 40 * 1641890 * 2
def baseEnd_1641890 : Nat := 562052501207124221016061

theorem tailTrace_1641890 : CollatzResearch.WordTrace tailWord_1641890 prefixEnd_1641890 562052501207124221016061 := by
  unfold tailWord_1641890
  simp only [CollatzResearch.WordTrace]
  refine ⟨14971162005430104333082781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39923098681146944888220749 14971162005430104333082781)
  ·
    refine ⟨5614185752036289124906043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14971162005430104333082781 5614185752036289124906043)
    ·
      refine ⟨8421278628054433687359065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614185752036289124906043 8421278628054433687359065)
      ·
        refine ⟨6315958971040825265519299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8421278628054433687359065 6315958971040825265519299)
        ·
          refine ⟨9473938456561237898278949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315958971040825265519299 9473938456561237898278949)
          ·
            refine ⟨1776363460605232105927303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9473938456561237898278949 1776363460605232105927303)
            ·
              refine ⟨2664545190907848158890955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776363460605232105927303 2664545190907848158890955)
              ·
                refine ⟨3996817786361772238336433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664545190907848158890955 3996817786361772238336433)
                ·
                  refine ⟨2997613339771329178752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3996817786361772238336433 2997613339771329178752325)
                  ·
                    refine ⟨562052501207124221016061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2997613339771329178752325 562052501207124221016061)
                    ·
                      rfl

theorem cell22_1641890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1641890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641890 prefixEnd_1641890 := by exact prefixLift 1641890
  have htrace : WordTrace (prefixWord ++ tailWord_1641890) baseStart_1641890 baseEnd_1641890 := by
    simpa [prefixWord, tailWord_1641890, baseEnd_1641890] using wordTrace_append hprefix tailTrace_1641890
  have hstable : (prefixWord ++ tailWord_1641890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641890).length < 2 ^ (prefixWord ++ tailWord_1641890).sum := by decide
  have hdescent : baseEnd_1641890 < baseStart_1641890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641920 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 1, 3]
def baseStart_1641920 : Nat := 118140960795 + 1641920 * 2 ^ 59
def prefixEnd_1641920 : Nat := 4983230072969 + 3 ^ 40 * 1641920 * 2
def baseEnd_1641920 : Nat := 562062770820214142765969

theorem tailTrace_1641920 : CollatzResearch.WordTrace tailWord_1641920 prefixEnd_1641920 562062770820214142765969 := by
  unfold tailWord_1641920
  simp only [CollatzResearch.WordTrace]
  refine ⟨29942871105805866227961607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39923828141074488303948809 29942871105805866227961607)
  ·
    refine ⟨44914306658708799341942411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29942871105805866227961607 44914306658708799341942411)
    ·
      refine ⟨67371459988063199012913617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44914306658708799341942411 67371459988063199012913617)
      ·
        refine ⟨50528594991047399259685213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67371459988063199012913617 50528594991047399259685213)
        ·
          refine ⟨18948223121642774722381955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50528594991047399259685213 18948223121642774722381955)
          ·
            refine ⟨28422334682464162083572933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948223121642774722381955 28422334682464162083572933)
            ·
              refine ⟨5329187752962030390669925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28422334682464162083572933 5329187752962030390669925)
              ·
                refine ⟨999222703680380698250611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5329187752962030390669925 999222703680380698250611)
                ·
                  refine ⟨1498834055520571047375917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999222703680380698250611 1498834055520571047375917)
                  ·
                    refine ⟨562062770820214142765969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498834055520571047375917 562062770820214142765969)
                    ·
                      rfl

theorem cell22_1641920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_1641920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641920 prefixEnd_1641920 := by exact prefixLift 1641920
  have htrace : WordTrace (prefixWord ++ tailWord_1641920) baseStart_1641920 baseEnd_1641920 := by
    simpa [prefixWord, tailWord_1641920, baseEnd_1641920] using wordTrace_append hprefix tailTrace_1641920
  have hstable : (prefixWord ++ tailWord_1641920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641920).length < 2 ^ (prefixWord ++ tailWord_1641920).sum := by decide
  have hdescent : baseEnd_1641920 < baseStart_1641920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641931 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_1641931 : Nat := 118140960795 + 1641931 * 2 ^ 59
def prefixEnd_1641931 : Nat := 4983230072969 + 3 ^ 40 * 1641931 * 2
def baseEnd_1641931 : Nat := 562066536345013780740935

theorem tailTrace_1641931 : CollatzResearch.WordTrace tailWord_1641931 prefixEnd_1641931 562066536345013780740935 := by
  unfold tailWord_1641931
  simp only [CollatzResearch.WordTrace]
  refine ⟨59886143414571881334573647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39924095609714587556382431 59886143414571881334573647)
  ·
    refine ⟨89829215121857822001860471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59886143414571881334573647 89829215121857822001860471)
    ·
      refine ⟨134743822682786733002790707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89829215121857822001860471 134743822682786733002790707)
      ·
        refine ⟨202115734024180099504186061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134743822682786733002790707 202115734024180099504186061)
        ·
          refine ⟨75793400259067537314069773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202115734024180099504186061 75793400259067537314069773)
          ·
            refine ⟨28422525097150326492776165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75793400259067537314069773 28422525097150326492776165)
            ·
              refine ⟨5329223455715686217395531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28422525097150326492776165 5329223455715686217395531)
              ·
                refine ⟨7993835183573529326093297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329223455715686217395531 7993835183573529326093297)
                ·
                  refine ⟨5995376387680146994569973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993835183573529326093297 5995376387680146994569973)
                  ·
                    refine ⟨562066536345013780740935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5995376387680146994569973 562066536345013780740935)
                    ·
                      rfl

theorem cell22_1641931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_1641931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641931 prefixEnd_1641931 := by exact prefixLift 1641931
  have htrace : WordTrace (prefixWord ++ tailWord_1641931) baseStart_1641931 baseEnd_1641931 := by
    simpa [prefixWord, tailWord_1641931, baseEnd_1641931] using wordTrace_append hprefix tailTrace_1641931
  have hstable : (prefixWord ++ tailWord_1641931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641931).length < 2 ^ (prefixWord ++ tailWord_1641931).sum := by decide
  have hdescent : baseEnd_1641931 < baseStart_1641931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642051 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 11]
def baseStart_1642051 : Nat := 118140960795 + 1642051 * 2 ^ 59
def prefixEnd_1642051 : Nat := 4983230072969 + 3 ^ 40 * 1642051 * 2
def baseEnd_1642051 : Nat := 187369204932457822580189

theorem tailTrace_1642051 : CollatzResearch.WordTrace tailWord_1642051 prefixEnd_1642051 187369204932457822580189 := by
  unfold tailWord_1642051
  simp only [CollatzResearch.WordTrace]
  refine ⟨59890520174137141828942007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39927013449424761219294671 59890520174137141828942007)
  ·
    refine ⟨89835780261205712743413011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59890520174137141828942007 89835780261205712743413011)
    ·
      refine ⟨134753670391808569115119517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89835780261205712743413011 134753670391808569115119517)
      ·
        refine ⟨50532626396928213418169819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134753670391808569115119517 50532626396928213418169819)
        ·
          refine ⟨75798939595392320127254729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50532626396928213418169819 75798939595392320127254729)
          ·
            refine ⟨56849204696544240095441047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75798939595392320127254729 56849204696544240095441047)
            ·
              refine ⟨85273807044816360143161571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56849204696544240095441047 85273807044816360143161571)
              ·
                refine ⟨127910710567224540214742357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85273807044816360143161571 127910710567224540214742357)
                ·
                  refine ⟨187369204932457822580189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 127910710567224540214742357 187369204932457822580189)
                  ·
                    rfl

theorem cell22_1642051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_1642051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642051 prefixEnd_1642051 := by exact prefixLift 1642051
  have htrace : WordTrace (prefixWord ++ tailWord_1642051) baseStart_1642051 baseEnd_1642051 := by
    simpa [prefixWord, tailWord_1642051, baseEnd_1642051] using wordTrace_append hprefix tailTrace_1642051
  have hstable : (prefixWord ++ tailWord_1642051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642051).length < 2 ^ (prefixWord ++ tailWord_1642051).sum := by decide
  have hdescent : baseEnd_1642051 < baseStart_1642051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642068 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1642068 : Nat := 118140960795 + 1642068 * 2 ^ 59
def prefixEnd_1642068 : Nat := 4983230072969 + 3 ^ 40 * 1642068 * 2
def baseEnd_1642068 : Nat := 187371144748263696688505

theorem tailTrace_1642068 : CollatzResearch.WordTrace tailWord_1642068 prefixEnd_1642068 187371144748263696688505 := by
  unfold tailWord_1642068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29945570107537776866155429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39927426810050369154873905 29945570107537776866155429)
  ·
    refine ⟨5614794395163333162404143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29945570107537776866155429 5614794395163333162404143)
    ·
      refine ⟨8422191592744999743606215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614794395163333162404143 8422191592744999743606215)
      ·
        refine ⟨12633287389117499615409323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422191592744999743606215 12633287389117499615409323)
        ·
          refine ⟨18949931083676249423113985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12633287389117499615409323 18949931083676249423113985)
          ·
            refine ⟨14212448312757187067335489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18949931083676249423113985 14212448312757187067335489)
            ·
              refine ⟨10659336234567890300501617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14212448312757187067335489 10659336234567890300501617)
              ·
                refine ⟨7994502175925917725376213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10659336234567890300501617 7994502175925917725376213)
                ·
                  refine ⟨187371144748263696688505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7994502175925917725376213 187371144748263696688505)
                  ·
                    rfl

theorem cell22_1642068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1642068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642068 prefixEnd_1642068 := by exact prefixLift 1642068
  have htrace : WordTrace (prefixWord ++ tailWord_1642068) baseStart_1642068 baseEnd_1642068 := by
    simpa [prefixWord, tailWord_1642068, baseEnd_1642068] using wordTrace_append hprefix tailTrace_1642068
  have hstable : (prefixWord ++ tailWord_1642068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642068).length < 2 ^ (prefixWord ++ tailWord_1642068).sum := by decide
  have hdescent : baseEnd_1642068 < baseStart_1642068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642083 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_1642083 : Nat := 118140960795 + 1642083 * 2 ^ 59
def prefixEnd_1642083 : Nat := 4983230072969 + 3 ^ 40 * 1642083 * 2
def baseEnd_1642083 : Nat := 562118569051336050940469

theorem tailTrace_1642083 : CollatzResearch.WordTrace tailWord_1642083 prefixEnd_1642083 562118569051336050940469 := by
  unfold tailWord_1642083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59891687310021211294106903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39927791540014140862737935 59891687310021211294106903)
  ·
    refine ⟨89837530965031816941160355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59891687310021211294106903 89837530965031816941160355)
    ·
      refine ⟨134756296447547725411740533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89837530965031816941160355 134756296447547725411740533)
      ·
        refine ⟨12633402791957599257350675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134756296447547725411740533 12633402791957599257350675)
        ·
          refine ⟨18950104187936398886026013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12633402791957599257350675 18950104187936398886026013)
          ·
            refine ⟨7106289070476149582259755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18950104187936398886026013 7106289070476149582259755)
            ·
              refine ⟨10659433605714224373389633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106289070476149582259755 10659433605714224373389633)
              ·
                refine ⟨7994575204285668280042225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10659433605714224373389633 7994575204285668280042225)
                ·
                  refine ⟨5995931403214251210031669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7994575204285668280042225 5995931403214251210031669)
                  ·
                    refine ⟨562118569051336050940469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5995931403214251210031669 562118569051336050940469)
                    ·
                      rfl

theorem cell22_1642083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_1642083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642083 prefixEnd_1642083 := by exact prefixLift 1642083
  have htrace : WordTrace (prefixWord ++ tailWord_1642083) baseStart_1642083 baseEnd_1642083 := by
    simpa [prefixWord, tailWord_1642083, baseEnd_1642083] using wordTrace_append hprefix tailTrace_1642083
  have hstable : (prefixWord ++ tailWord_1642083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642083).length < 2 ^ (prefixWord ++ tailWord_1642083).sum := by decide
  have hdescent : baseEnd_1642083 < baseStart_1642083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642085 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 5]
def baseStart_1642085 : Nat := 118140960795 + 1642085 * 2 ^ 59
def prefixEnd_1642085 : Nat := 4983230072969 + 3 ^ 40 * 1642085 * 2
def baseEnd_1642085 : Nat := 187373084564069570796821

theorem tailTrace_1642085 : CollatzResearch.WordTrace tailWord_1642085 prefixEnd_1642085 187373084564069570796821 := by
  unfold tailWord_1642085
  simp only [CollatzResearch.WordTrace]
  refine ⟨59891760256013965635679709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39927840170675977090453139 59891760256013965635679709)
  ·
    refine ⟨22459410096005237113379891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59891760256013965635679709 22459410096005237113379891)
    ·
      refine ⟨33689115144007855670069837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22459410096005237113379891 33689115144007855670069837)
      ·
        refine ⟨12633418179002945876276189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33689115144007855670069837 12633418179002945876276189)
        ·
          refine ⟨4737531817126104703603571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12633418179002945876276189 4737531817126104703603571)
          ·
            refine ⟨7106297725689157055405357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737531817126104703603571 7106297725689157055405357)
            ·
              refine ⟨2664861647133433895777009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7106297725689157055405357 2664861647133433895777009)
              ·
                refine ⟨1998646235350075421832757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664861647133433895777009 1998646235350075421832757)
                ·
                  refine ⟨187373084564069570796821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998646235350075421832757 187373084564069570796821)
                  ·
                    rfl

theorem cell22_1642085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_1642085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642085 prefixEnd_1642085 := by exact prefixLift 1642085
  have htrace : WordTrace (prefixWord ++ tailWord_1642085) baseStart_1642085 baseEnd_1642085 := by
    simpa [prefixWord, tailWord_1642085, baseEnd_1642085] using wordTrace_append hprefix tailTrace_1642085
  have hstable : (prefixWord ++ tailWord_1642085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642085).length < 2 ^ (prefixWord ++ tailWord_1642085).sum := by decide
  have hdescent : baseEnd_1642085 < baseStart_1642085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642128 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_1642128 : Nat := 118140960795 + 1642128 * 2 ^ 59
def prefixEnd_1642128 : Nat := 4983230072969 + 3 ^ 40 * 1642128 * 2
def baseEnd_1642128 : Nat := 562133973470970933565331

theorem tailTrace_1642128 : CollatzResearch.WordTrace tailWord_1642128 prefixEnd_1642128 562133973470970933565331 := by
  unfold tailWord_1642128
  simp only [CollatzResearch.WordTrace]
  refine ⟨29946664297429091989747519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39928885729905455986330025 29946664297429091989747519)
  ·
    refine ⟨44919996446143637984621279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29946664297429091989747519 44919996446143637984621279)
    ·
      refine ⟨67379994669215456976931919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44919996446143637984621279 67379994669215456976931919)
      ·
        refine ⟨101069992003823185465397879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67379994669215456976931919 101069992003823185465397879)
        ·
          refine ⟨151604988005734778198096819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101069992003823185465397879 151604988005734778198096819)
          ·
            refine ⟨227407482008602167297145229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151604988005734778198096819 227407482008602167297145229)
            ·
              refine ⟨85277805753225812736429461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227407482008602167297145229 85277805753225812736429461)
              ·
                refine ⟨3997397144682459972020131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85277805753225812736429461 3997397144682459972020131)
                ·
                  refine ⟨5996095717023689958030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997397144682459972020131 5996095717023689958030197)
                  ·
                    refine ⟨562133973470970933565331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5996095717023689958030197 562133973470970933565331)
                    ·
                      rfl

theorem cell22_1642128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_1642128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642128 prefixEnd_1642128 := by exact prefixLift 1642128
  have htrace : WordTrace (prefixWord ++ tailWord_1642128) baseStart_1642128 baseEnd_1642128 := by
    simpa [prefixWord, tailWord_1642128, baseEnd_1642128] using wordTrace_append hprefix tailTrace_1642128
  have hstable : (prefixWord ++ tailWord_1642128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642128).length < 2 ^ (prefixWord ++ tailWord_1642128).sum := by decide
  have hdescent : baseEnd_1642128 < baseStart_1642128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642147 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 4]
def baseStart_1642147 : Nat := 118140960795 + 1642147 * 2 ^ 59
def prefixEnd_1642147 : Nat := 4983230072969 + 3 ^ 40 * 1642147 * 2
def baseEnd_1642147 : Nat := 187380159186420405780091

theorem tailTrace_1642147 : CollatzResearch.WordTrace tailWord_1642147 prefixEnd_1642147 187380159186420405780091 := by
  unfold tailWord_1642147
  simp only [CollatzResearch.WordTrace]
  refine ⟨59894021581789350224436695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39929347721192900149624463 59894021581789350224436695)
  ·
    refine ⟨89841032372684025336655043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59894021581789350224436695 89841032372684025336655043)
    ·
      refine ⟨134761548559026038004982565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89841032372684025336655043 134761548559026038004982565)
      ·
        refine ⟨25267790354817382125934231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134761548559026038004982565 25267790354817382125934231)
        ·
          refine ⟨37901685532226073188901347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25267790354817382125934231 37901685532226073188901347)
          ·
            refine ⟨56852528298339109783352021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37901685532226073188901347 56852528298339109783352021)
            ·
              refine ⟨1332481131992322885547313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56852528298339109783352021 1332481131992322885547313)
              ·
                refine ⟨999360848994242164160485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332481131992322885547313 999360848994242164160485)
                ·
                  refine ⟨187380159186420405780091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999360848994242164160485 187380159186420405780091)
                  ·
                    rfl

theorem cell22_1642147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 4].length) (baseStart_1642147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642147 prefixEnd_1642147 := by exact prefixLift 1642147
  have htrace : WordTrace (prefixWord ++ tailWord_1642147) baseStart_1642147 baseEnd_1642147 := by
    simpa [prefixWord, tailWord_1642147, baseEnd_1642147] using wordTrace_append hprefix tailTrace_1642147
  have hstable : (prefixWord ++ tailWord_1642147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642147).length < 2 ^ (prefixWord ++ tailWord_1642147).sum := by decide
  have hdescent : baseEnd_1642147 < baseStart_1642147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642166 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1642166 : Nat := 118140960795 + 1642166 * 2 ^ 59
def prefixEnd_1642166 : Nat := 4983230072969 + 3 ^ 40 * 1642166 * 2
def baseEnd_1642166 : Nat := 562146981647551501115215

theorem tailTrace_1642166 : CollatzResearch.WordTrace tailWord_1642166 prefixEnd_1642166 562146981647551501115215 := by
  unfold tailWord_1642166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743419660545032279336147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39929809712480344312918901 3743419660545032279336147)
  ·
    refine ⟨5615129490817548419004221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3743419660545032279336147 5615129490817548419004221)
    ·
      refine ⟨2105673559056580657126583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5615129490817548419004221 2105673559056580657126583)
      ·
        refine ⟨3158510338584870985689875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105673559056580657126583 3158510338584870985689875)
        ·
          refine ⟨4737765507877306478534813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3158510338584870985689875 4737765507877306478534813)
          ·
            refine ⟨1776662065453989929450555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4737765507877306478534813 1776662065453989929450555)
            ·
              refine ⟨2664993098180984894175833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776662065453989929450555 2664993098180984894175833)
              ·
                refine ⟨1998744823635738670631875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664993098180984894175833 1998744823635738670631875)
                ·
                  refine ⟨2998117235453608005947813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998744823635738670631875 2998117235453608005947813)
                  ·
                    refine ⟨562146981647551501115215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998117235453608005947813 562146981647551501115215)
                    ·
                      rfl

theorem cell22_1642166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1642166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642166 prefixEnd_1642166 := by exact prefixLift 1642166
  have htrace : WordTrace (prefixWord ++ tailWord_1642166) baseStart_1642166 baseEnd_1642166 := by
    simpa [prefixWord, tailWord_1642166, baseEnd_1642166] using wordTrace_append hprefix tailTrace_1642166
  have hstable : (prefixWord ++ tailWord_1642166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642166).length < 2 ^ (prefixWord ++ tailWord_1642166).sum := by decide
  have hdescent : baseEnd_1642166 < baseStart_1642166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642220 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1642220 : Nat := 118140960795 + 1642220 * 2 ^ 59
def prefixEnd_1642220 : Nat := 4983230072969 + 3 ^ 40 * 1642220 * 2
def baseEnd_1642220 : Nat := 187388488983704453421683

theorem tailTrace_1642220 : CollatzResearch.WordTrace tailWord_1642220 prefixEnd_1642220 187388488983704453421683 := by
  unfold tailWord_1642220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948342055262441845922057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39931122740349922461229409 29948342055262441845922057)
  ·
    refine ⟨22461256541446831384441543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29948342055262441845922057 22461256541446831384441543)
    ·
      refine ⟨33691884812170247076662315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22461256541446831384441543 33691884812170247076662315)
      ·
        refine ⟨50537827218255370614993473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33691884812170247076662315 50537827218255370614993473)
        ·
          refine ⟨37903370413691527961245105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50537827218255370614993473 37903370413691527961245105)
          ·
            refine ⟨28427527810268645970933829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37903370413691527961245105 28427527810268645970933829)
            ·
              refine ⟨5330161464425371119550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28427527810268645970933829 5330161464425371119550093)
              ·
                refine ⟨1998810549159514169831285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5330161464425371119550093 1998810549159514169831285)
                ·
                  refine ⟨187388488983704453421683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998810549159514169831285 187388488983704453421683)
                  ·
                    rfl

theorem cell22_1642220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1642220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642220 prefixEnd_1642220 := by exact prefixLift 1642220
  have htrace : WordTrace (prefixWord ++ tailWord_1642220) baseStart_1642220 baseEnd_1642220 := by
    simpa [prefixWord, tailWord_1642220, baseEnd_1642220] using wordTrace_append hprefix tailTrace_1642220
  have hstable : (prefixWord ++ tailWord_1642220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642220).length < 2 ^ (prefixWord ++ tailWord_1642220).sum := by decide
  have hdescent : baseEnd_1642220 < baseStart_1642220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642312 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_1642312 : Nat := 118140960795 + 1642312 * 2 ^ 59
def prefixEnd_1642312 : Nat := 4983230072969 + 3 ^ 40 * 1642312 * 2
def baseEnd_1642312 : Nat := 562196960431255786964767

theorem tailTrace_1642312 : CollatzResearch.WordTrace tailWord_1642312 prefixEnd_1642312 562196960431255786964767 := by
  unfold tailWord_1642312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950019813095791702096595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39933359750794388936128793 29950019813095791702096595)
  ·
    refine ⟨44925029719643687553144893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29950019813095791702096595 44925029719643687553144893)
    ·
      refine ⟨16846886144866382832429335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44925029719643687553144893 16846886144866382832429335)
      ·
        refine ⟨25270329217299574248644003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16846886144866382832429335 25270329217299574248644003)
        ·
          refine ⟨37905493825949361372966005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25270329217299574248644003 37905493825949361372966005)
          ·
            refine ⟨3553640046182752628715563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37905493825949361372966005 3553640046182752628715563)
            ·
              refine ⟨5330460069274128943073345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553640046182752628715563 5330460069274128943073345)
              ·
                refine ⟨3997845051955596707305009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5330460069274128943073345 3997845051955596707305009)
                ·
                  refine ⟨2998383788966697530478757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997845051955596707305009 2998383788966697530478757)
                  ·
                    refine ⟨562196960431255786964767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998383788966697530478757 562196960431255786964767)
                    ·
                      rfl

theorem cell22_1642312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_1642312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642312 prefixEnd_1642312 := by exact prefixLift 1642312
  have htrace : WordTrace (prefixWord ++ tailWord_1642312) baseStart_1642312 baseEnd_1642312 := by
    simpa [prefixWord, tailWord_1642312, baseEnd_1642312] using wordTrace_append hprefix tailTrace_1642312
  have hstable : (prefixWord ++ tailWord_1642312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642312).length < 2 ^ (prefixWord ++ tailWord_1642312).sum := by decide
  have hdescent : baseEnd_1642312 < baseStart_1642312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642316 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1642316 : Nat := 118140960795 + 1642316 * 2 ^ 59
def prefixEnd_1642316 : Nat := 4983230072969 + 3 ^ 40 * 1642316 * 2
def baseEnd_1642316 : Nat := 187399443237667036621585

theorem tailTrace_1642316 : CollatzResearch.WordTrace tailWord_1642316 prefixEnd_1642316 187399443237667036621585 := by
  unfold tailWord_1642316
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950092759088546043669401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39933457012118061391559201 29950092759088546043669401)
  ·
    refine ⟨22462569569316409532752051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29950092759088546043669401 22462569569316409532752051)
    ·
      refine ⟨33693854353974614299128077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22462569569316409532752051 33693854353974614299128077)
      ·
        refine ⟨12635195382740480362173029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33693854353974614299128077 12635195382740480362173029)
        ·
          refine ⟨2369099134263840067907443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12635195382740480362173029 2369099134263840067907443)
          ·
            refine ⟨3553648701395760101861165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369099134263840067907443 3553648701395760101861165)
            ·
              refine ⟨1332618263023410038197937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3553648701395760101861165 1332618263023410038197937)
              ·
                refine ⟨999463697267557528648453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332618263023410038197937 999463697267557528648453)
                ·
                  refine ⟨187399443237667036621585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999463697267557528648453 187399443237667036621585)
                  ·
                    rfl

theorem cell22_1642316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1642316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642316 prefixEnd_1642316 := by exact prefixLift 1642316
  have htrace : WordTrace (prefixWord ++ tailWord_1642316) baseStart_1642316 baseEnd_1642316 := by
    simpa [prefixWord, tailWord_1642316, baseEnd_1642316] using wordTrace_append hprefix tailTrace_1642316
  have hstable : (prefixWord ++ tailWord_1642316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642316).length < 2 ^ (prefixWord ++ tailWord_1642316).sum := by decide
  have hdescent : baseEnd_1642316 < baseStart_1642316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642327 : List Nat := [1, 1, 3, 2, 5, 1, 2, 7]
def baseStart_1642327 : Nat := 118140960795 + 1642327 * 2 ^ 59
def prefixEnd_1642327 : Nat := 4983230072969 + 3 ^ 40 * 1642327 * 2
def baseEnd_1642327 : Nat := 62466899470866749759969

theorem tailTrace_1642327 : CollatzResearch.WordTrace tailWord_1642327 prefixEnd_1642327 62466899470866749759969 := by
  unfold tailWord_1642327
  simp only [CollatzResearch.WordTrace]
  refine ⟨59900586721137240965989235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39933724480758160643992823 59900586721137240965989235)
  ·
    refine ⟨89850880081705861448983853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59900586721137240965989235 89850880081705861448983853)
    ·
      refine ⟨33694080030639698043368945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89850880081705861448983853 33694080030639698043368945)
      ·
        refine ⟨25270560022979773532526709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33694080030639698043368945 25270560022979773532526709)
        ·
          refine ⟨2369115002154353768674379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25270560022979773532526709 2369115002154353768674379)
          ·
            refine ⟨3553672503231530653011569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369115002154353768674379 3553672503231530653011569)
            ·
              refine ⟨2665254377423647989758677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553672503231530653011569 2665254377423647989758677)
              ·
                refine ⟨62466899470866749759969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2665254377423647989758677 62466899470866749759969)
                ·
                  rfl

theorem cell22_1642327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 7].length) (baseStart_1642327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642327 prefixEnd_1642327 := by exact prefixLift 1642327
  have htrace : WordTrace (prefixWord ++ tailWord_1642327) baseStart_1642327 baseEnd_1642327 := by
    simpa [prefixWord, tailWord_1642327, baseEnd_1642327] using wordTrace_append hprefix tailTrace_1642327
  have hstable : (prefixWord ++ tailWord_1642327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642327).length < 2 ^ (prefixWord ++ tailWord_1642327).sum := by decide
  have hdescent : baseEnd_1642327 < baseStart_1642327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642346 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1642346 : Nat := 118140960795 + 1642346 * 2 ^ 59
def prefixEnd_1642346 : Nat := 4983230072969 + 3 ^ 40 * 1642346 * 2
def baseEnd_1642346 : Nat := 562208599326091031614663

theorem tailTrace_1642346 : CollatzResearch.WordTrace tailWord_1642346 prefixEnd_1642346 562208599326091031614663 := by
  unfold tailWord_1642346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14975319927017101802732723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39934186472045604807287261 14975319927017101802732723)
  ·
    refine ⟨22462979890525652704099085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14975319927017101802732723 22462979890525652704099085)
    ·
      refine ⟨8423617458947119764037157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22462979890525652704099085 8423617458947119764037157)
      ·
        refine ⟨1579428273552584955756967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8423617458947119764037157 1579428273552584955756967)
        ·
          refine ⟨2369142410328877433635451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579428273552584955756967 2369142410328877433635451)
          ·
            refine ⟨3553713615493316150453177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369142410328877433635451 3553713615493316150453177)
            ·
              refine ⟨2665285211619987112839883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553713615493316150453177 2665285211619987112839883)
              ·
                refine ⟨3997927817429980669259825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665285211619987112839883 3997927817429980669259825)
                ·
                  refine ⟨2998445863072485501944869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3997927817429980669259825 2998445863072485501944869)
                  ·
                    refine ⟨562208599326091031614663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998445863072485501944869 562208599326091031614663)
                    ·
                      rfl

theorem cell22_1642346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1642346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642346 prefixEnd_1642346 := by exact prefixLift 1642346
  have htrace : WordTrace (prefixWord ++ tailWord_1642346) baseStart_1642346 baseEnd_1642346 := by
    simpa [prefixWord, tailWord_1642346, baseEnd_1642346] using wordTrace_append hprefix tailTrace_1642346
  have hstable : (prefixWord ++ tailWord_1642346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642346).length < 2 ^ (prefixWord ++ tailWord_1642346).sum := by decide
  have hdescent : baseEnd_1642346 < baseStart_1642346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642372 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1642372 : Nat := 118140960795 + 1642372 * 2 ^ 59
def prefixEnd_1642372 : Nat := 4983230072969 + 3 ^ 40 * 1642372 * 2
def baseEnd_1642372 : Nat := 187405833219145210154861

theorem tailTrace_1642372 : CollatzResearch.WordTrace tailWord_1642372 prefixEnd_1642372 187405833219145210154861 := by
  unfold tailWord_1642372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951114002987106825688685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39934818670649475767584913 29951114002987106825688685)
  ·
    refine ⟨11231667751120165059633257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29951114002987106825688685 11231667751120165059633257)
    ·
      refine ⟨8423750813340123794724943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11231667751120165059633257 8423750813340123794724943)
      ·
        refine ⟨12635626220010185692087415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8423750813340123794724943 12635626220010185692087415)
        ·
          refine ⟨18953439330015278538131123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12635626220010185692087415 18953439330015278538131123)
          ·
            refine ⟨28430158995022917807196685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18953439330015278538131123 28430158995022917807196685)
            ·
              refine ⟨10661309623133594177698757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28430158995022917807196685 10661309623133594177698757)
              ·
                refine ⟨1998995554337548908318517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10661309623133594177698757 1998995554337548908318517)
                ·
                  refine ⟨187405833219145210154861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1998995554337548908318517 187405833219145210154861)
                  ·
                    rfl

theorem cell22_1642372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1642372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642372 prefixEnd_1642372 := by exact prefixLift 1642372
  have htrace : WordTrace (prefixWord ++ tailWord_1642372) baseStart_1642372 baseEnd_1642372 := by
    simpa [prefixWord, tailWord_1642372, baseEnd_1642372] using wordTrace_append hprefix tailTrace_1642372
  have hstable : (prefixWord ++ tailWord_1642372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642372).length < 2 ^ (prefixWord ++ tailWord_1642372).sum := by decide
  have hdescent : baseEnd_1642372 < baseStart_1642372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642492 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1642492 : Nat := 118140960795 + 1642492 * 2 ^ 59
def prefixEnd_1642492 : Nat := 4983230072969 + 3 ^ 40 * 1642492 * 2
def baseEnd_1642492 : Nat := 562258578109795317464215

theorem tailTrace_1642492 : CollatzResearch.WordTrace tailWord_1642492 prefixEnd_1642492 562258578109795317464215 := by
  unfold tailWord_1642492
  simp only [CollatzResearch.WordTrace]
  refine ⟨29953302382769737072872865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39937736510359649430497153 29953302382769737072872865)
  ·
    refine ⟨22464976787077302804654649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29953302382769737072872865 22464976787077302804654649)
    ·
      refine ⟨16848732590307977103490987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22464976787077302804654649 16848732590307977103490987)
      ·
        refine ⟨25273098885461965655236481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16848732590307977103490987 25273098885461965655236481)
        ·
          refine ⟨18954824164096474241427361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25273098885461965655236481 18954824164096474241427361)
          ·
            refine ⟨14216118123072355681070521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18954824164096474241427361 14216118123072355681070521)
            ·
              refine ⟨10662088592304266760802891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14216118123072355681070521 10662088592304266760802891)
              ·
                refine ⟨15993132888456400141204337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662088592304266760802891 15993132888456400141204337)
                ·
                  refine ⟨11994849666342300105903253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15993132888456400141204337 11994849666342300105903253)
                  ·
                    refine ⟨562258578109795317464215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11994849666342300105903253 562258578109795317464215)
                    ·
                      rfl

theorem cell22_1642492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1642492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642492 prefixEnd_1642492 := by exact prefixLift 1642492
  have htrace : WordTrace (prefixWord ++ tailWord_1642492) baseStart_1642492 baseEnd_1642492 := by
    simpa [prefixWord, tailWord_1642492, baseEnd_1642492] using wordTrace_append hprefix tailTrace_1642492
  have hstable : (prefixWord ++ tailWord_1642492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642492).length < 2 ^ (prefixWord ++ tailWord_1642492).sum := by decide
  have hdescent : baseEnd_1642492 < baseStart_1642492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642545 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 1, 3]
def baseStart_1642545 : Nat := 118140960795 + 1642545 * 2 ^ 59
def prefixEnd_1642545 : Nat := 4983230072969 + 3 ^ 40 * 1642545 * 2
def baseEnd_1642545 : Nat := 562276721092920845889053

theorem tailTrace_1642545 : CollatzResearch.WordTrace tailWord_1642545 prefixEnd_1642545 562276721092920845889053 := by
  unfold tailWord_1642545
  simp only [CollatzResearch.WordTrace]
  refine ⟨59908537834347464197425089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39939025222898309464950059 59908537834347464197425089)
  ·
    refine ⟨44931403375760598148068817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59908537834347464197425089 44931403375760598148068817)
    ·
      refine ⟨33698552531820448611051613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44931403375760598148068817 33698552531820448611051613)
      ·
        refine ⟨12636957199432668229144355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33698552531820448611051613 12636957199432668229144355)
        ·
          refine ⟨18955435799149002343716533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12636957199432668229144355 18955435799149002343716533)
          ·
            refine ⟨1777072106170218969723425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18955435799149002343716533 1777072106170218969723425)
            ·
              refine ⟨1332804079627664227292569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777072106170218969723425 1332804079627664227292569)
              ·
                refine ⟨999603059720748170469427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332804079627664227292569 999603059720748170469427)
                ·
                  refine ⟨1499404589581122255704141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999603059720748170469427 1499404589581122255704141)
                  ·
                    refine ⟨562276721092920845889053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1499404589581122255704141 562276721092920845889053)
                    ·
                      rfl

theorem cell22_1642545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_1642545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642545 prefixEnd_1642545 := by exact prefixLift 1642545
  have htrace : WordTrace (prefixWord ++ tailWord_1642545) baseStart_1642545 baseEnd_1642545 := by
    simpa [prefixWord, tailWord_1642545, baseEnd_1642545] using wordTrace_append hprefix tailTrace_1642545
  have hstable : (prefixWord ++ tailWord_1642545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642545).length < 2 ^ (prefixWord ++ tailWord_1642545).sum := by decide
  have hdescent : baseEnd_1642545 < baseStart_1642545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642584 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_1642584 : Nat := 118140960795 + 1642584 * 2 ^ 59
def prefixEnd_1642584 : Nat := 4983230072969 + 3 ^ 40 * 1642584 * 2
def baseEnd_1642584 : Nat := 562290071589937744163933

theorem tailTrace_1642584 : CollatzResearch.WordTrace tailWord_1642584 prefixEnd_1642584 562290071589937744163933 := by
  unfold tailWord_1642584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29954980140603086929047403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39939973520804115905396537 29954980140603086929047403)
  ·
    refine ⟨44932470210904630393571105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29954980140603086929047403 44932470210904630393571105)
    ·
      refine ⟨33699352658178472795178329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44932470210904630393571105 33699352658178472795178329)
      ·
        refine ⟨25274514493633854596383747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33699352658178472795178329 25274514493633854596383747)
        ·
          refine ⟨37911771740450781894575621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25274514493633854596383747 37911771740450781894575621)
          ·
            refine ⟨7108457201334521605232929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37911771740450781894575621 7108457201334521605232929)
            ·
              refine ⟨5331342901000891203924697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7108457201334521605232929 5331342901000891203924697)
              ·
                refine ⟨3998507175750668402943523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331342901000891203924697 3998507175750668402943523)
                ·
                  refine ⟨5997760763626002604415285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998507175750668402943523 5997760763626002604415285)
                  ·
                    refine ⟨562290071589937744163933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5997760763626002604415285 562290071589937744163933)
                    ·
                      rfl

theorem cell22_1642584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_1642584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642584 prefixEnd_1642584 := by exact prefixLift 1642584
  have htrace : WordTrace (prefixWord ++ tailWord_1642584) baseStart_1642584 baseEnd_1642584 := by
    simpa [prefixWord, tailWord_1642584, baseEnd_1642584] using wordTrace_append hprefix tailTrace_1642584
  have hstable : (prefixWord ++ tailWord_1642584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642584).length < 2 ^ (prefixWord ++ tailWord_1642584).sum := by decide
  have hdescent : baseEnd_1642584 < baseStart_1642584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642586 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_1642586 : Nat := 118140960795 + 1642586 * 2 ^ 59
def prefixEnd_1642586 : Nat := 4983230072969 + 3 ^ 40 * 1642586 * 2
def baseEnd_1642586 : Nat := 187430252076936801871309

theorem tailTrace_1642586 : CollatzResearch.WordTrace tailWord_1642586 prefixEnd_1642586 187430252076936801871309 := by
  unfold tailWord_1642586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977508306799732049916903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39940022151465952133111741 14977508306799732049916903)
  ·
    refine ⟨22466262460199598074875355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14977508306799732049916903 22466262460199598074875355)
    ·
      refine ⟨33699393690299397112313033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22466262460199598074875355 33699393690299397112313033)
      ·
        refine ⟨25274545267724547834234775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33699393690299397112313033 25274545267724547834234775)
        ·
          refine ⟨37911817901586821751352163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25274545267724547834234775 37911817901586821751352163)
          ·
            refine ⟨56867726852380232627028245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37911817901586821751352163 56867726852380232627028245)
            ·
              refine ⟨2665674696205323404391949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56867726852380232627028245 2665674696205323404391949)
              ·
                refine ⟨999628011076996276646981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2665674696205323404391949 999628011076996276646981)
                ·
                  refine ⟨187430252076936801871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999628011076996276646981 187430252076936801871309)
                  ·
                    rfl

theorem cell22_1642586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_1642586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642586 prefixEnd_1642586 := by exact prefixLift 1642586
  have htrace : WordTrace (prefixWord ++ tailWord_1642586) baseStart_1642586 baseEnd_1642586 := by
    simpa [prefixWord, tailWord_1642586, baseEnd_1642586] using wordTrace_append hprefix tailTrace_1642586
  have hstable : (prefixWord ++ tailWord_1642586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642586).length < 2 ^ (prefixWord ++ tailWord_1642586).sum := by decide
  have hdescent : baseEnd_1642586 < baseStart_1642586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642588 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1642588 : Nat := 118140960795 + 1642588 * 2 ^ 59
def prefixEnd_1642588 : Nat := 4983230072969 + 3 ^ 40 * 1642588 * 2
def baseEnd_1642588 : Nat := 562291440871683067063921

theorem tailTrace_1642588 : CollatzResearch.WordTrace tailWord_1642588 prefixEnd_1642588 562291440871683067063921 := by
  unfold tailWord_1642588
  simp only [CollatzResearch.WordTrace]
  refine ⟨29955053086595841270620209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39940070782127788360826945 29955053086595841270620209)
  ·
    refine ⟨22466289814946880952965157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29955053086595841270620209 22466289814946880952965157)
    ·
      refine ⟨4212429340302540178680967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22466289814946880952965157 4212429340302540178680967)
      ·
        refine ⟨6318644010453810268021451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212429340302540178680967 6318644010453810268021451)
        ·
          refine ⟨9477966015680715402032177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318644010453810268021451 9477966015680715402032177)
          ·
            refine ⟨7108474511760536551524133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9477966015680715402032177 7108474511760536551524133)
            ·
              refine ⟨1332838970955100603410775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7108474511760536551524133 1332838970955100603410775)
              ·
                refine ⟨1999258456432650905116163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332838970955100603410775 1999258456432650905116163)
                ·
                  refine ⟨2998887684648976357674245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999258456432650905116163 2998887684648976357674245)
                  ·
                    refine ⟨562291440871683067063921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998887684648976357674245 562291440871683067063921)
                    ·
                      rfl

theorem cell22_1642588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1642588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642588 prefixEnd_1642588 := by exact prefixLift 1642588
  have htrace : WordTrace (prefixWord ++ tailWord_1642588) baseStart_1642588 baseEnd_1642588 := by
    simpa [prefixWord, tailWord_1642588, baseEnd_1642588] using wordTrace_append hprefix tailTrace_1642588
  have hstable : (prefixWord ++ tailWord_1642588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642588).length < 2 ^ (prefixWord ++ tailWord_1642588).sum := by decide
  have hdescent : baseEnd_1642588 < baseStart_1642588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642599 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1642599 : Nat := 118140960795 + 1642599 * 2 ^ 59
def prefixEnd_1642599 : Nat := 4983230072969 + 3 ^ 40 * 1642599 * 2
def baseEnd_1642599 : Nat := 562295206396482705038887

theorem tailTrace_1642599 : CollatzResearch.WordTrace tailWord_1642599 prefixEnd_1642599 562295206396482705038887 := by
  unfold tailWord_1642599
  simp only [CollatzResearch.WordTrace]
  refine ⟨59910507376151831419890851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39940338250767887613260567 59910507376151831419890851)
  ·
    refine ⟨89865761064227747129836277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59910507376151831419890851 89865761064227747129836277)
    ·
      refine ⟨8424915099771351293422151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89865761064227747129836277 8424915099771351293422151)
      ·
        refine ⟨12637372649657026940133227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8424915099771351293422151 12637372649657026940133227)
        ·
          refine ⟨18956058974485540410199841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12637372649657026940133227 18956058974485540410199841)
          ·
            refine ⟨14217044230864155307649881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18956058974485540410199841 14217044230864155307649881)
            ·
              refine ⟨10662783173148116480737411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14217044230864155307649881 10662783173148116480737411)
              ·
                refine ⟨15994174759722174721106117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662783173148116480737411 15994174759722174721106117)
                ·
                  refine ⟨2998907767447907760207397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15994174759722174721106117 2998907767447907760207397)
                  ·
                    refine ⟨562295206396482705038887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2998907767447907760207397 562295206396482705038887)
                    ·
                      rfl

theorem cell22_1642599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1642599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642599 prefixEnd_1642599 := by exact prefixLift 1642599
  have htrace : WordTrace (prefixWord ++ tailWord_1642599) baseStart_1642599 baseEnd_1642599 := by
    simpa [prefixWord, tailWord_1642599, baseEnd_1642599] using wordTrace_append hprefix tailTrace_1642599
  have hstable : (prefixWord ++ tailWord_1642599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642599).length < 2 ^ (prefixWord ++ tailWord_1642599).sum := by decide
  have hdescent : baseEnd_1642599 < baseStart_1642599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642674 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1642674 : Nat := 118140960795 + 1642674 * 2 ^ 59
def prefixEnd_1642674 : Nat := 4983230072969 + 3 ^ 40 * 1642674 * 2
def baseEnd_1642674 : Nat := 562320880429207509413657

theorem tailTrace_1642674 : CollatzResearch.WordTrace tailWord_1642674 prefixEnd_1642674 562320880429207509413657 := by
  unfold tailWord_1642674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978310712720029807217769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39942161900586746152580717 14978310712720029807217769)
  ·
    refine ⟨11233733034540022355413327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14978310712720029807217769 11233733034540022355413327)
    ·
      refine ⟨16850599551810033533119991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11233733034540022355413327 16850599551810033533119991)
      ·
        refine ⟨25275899327715050299679987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16850599551810033533119991 25275899327715050299679987)
        ·
          refine ⟨37913848991572575449519981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25275899327715050299679987 37913848991572575449519981)
          ·
            refine ⟨14217693371839715793569993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37913848991572575449519981 14217693371839715793569993)
            ·
              refine ⟨10663270028879786845177495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14217693371839715793569993 10663270028879786845177495)
              ·
                refine ⟨15994905043319680267766243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10663270028879786845177495 15994905043319680267766243)
                ·
                  refine ⟨23992357564979520401649365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15994905043319680267766243 23992357564979520401649365)
                  ·
                    refine ⟨562320880429207509413657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23992357564979520401649365 562320880429207509413657)
                    ·
                      rfl

theorem cell22_1642674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1642674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642674 prefixEnd_1642674 := by exact prefixLift 1642674
  have htrace : WordTrace (prefixWord ++ tailWord_1642674) baseStart_1642674 baseEnd_1642674 := by
    simpa [prefixWord, tailWord_1642674, baseEnd_1642674] using wordTrace_append hprefix tailTrace_1642674
  have hstable : (prefixWord ++ tailWord_1642674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642674).length < 2 ^ (prefixWord ++ tailWord_1642674).sum := by decide
  have hdescent : baseEnd_1642674 < baseStart_1642674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642710 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1642710 : Nat := 118140960795 + 1642710 * 2 ^ 59
def prefixEnd_1642710 : Nat := 4983230072969 + 3 ^ 40 * 1642710 * 2
def baseEnd_1642710 : Nat := 187444401321638471837849

theorem tailTrace_1642710 : CollatzResearch.WordTrace tailWord_1642710 prefixEnd_1642710 187444401321638471837849 := by
  unfold tailWord_1642710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744659742421856086073849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39943037252499798251454389 3744659742421856086073849)
  ·
    refine ⟨2808494806816392064555387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3744659742421856086073849 2808494806816392064555387)
    ·
      refine ⟨4212742210224588096833081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808494806816392064555387 4212742210224588096833081)
      ·
        refine ⟨3159556657668441072624811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212742210224588096833081 3159556657668441072624811)
        ·
          refine ⟨4739334986502661608937217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159556657668441072624811 4739334986502661608937217)
          ·
            refine ⟨3554501239876996206702913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739334986502661608937217 3554501239876996206702913)
            ·
              refine ⟨2665875929907747155027185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554501239876996206702913 2665875929907747155027185)
              ·
                refine ⟨1999406947430810366270389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665875929907747155027185 1999406947430810366270389)
                ·
                  refine ⟨187444401321638471837849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1999406947430810366270389 187444401321638471837849)
                  ·
                    rfl

theorem cell22_1642710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1642710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642710 prefixEnd_1642710 := by exact prefixLift 1642710
  have htrace : WordTrace (prefixWord ++ tailWord_1642710) baseStart_1642710 baseEnd_1642710 := by
    simpa [prefixWord, tailWord_1642710, baseEnd_1642710] using wordTrace_append hprefix tailTrace_1642710
  have hstable : (prefixWord ++ tailWord_1642710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642710).length < 2 ^ (prefixWord ++ tailWord_1642710).sum := by decide
  have hdescent : baseEnd_1642710 < baseStart_1642710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642719 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1642719 : Nat := 118140960795 + 1642719 * 2 ^ 59
def prefixEnd_1642719 : Nat := 4983230072969 + 3 ^ 40 * 1642719 * 2
def baseEnd_1642719 : Nat := 562336284848842392038519

theorem tailTrace_1642719 : CollatzResearch.WordTrace tailWord_1642719 prefixEnd_1642719 562336284848842392038519 := by
  unfold tailWord_1642719
  simp only [CollatzResearch.WordTrace]
  refine ⟨59914884135717091914259211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39943256090478061276172807 59914884135717091914259211)
  ·
    refine ⟨89872326203575637871388817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59914884135717091914259211 89872326203575637871388817)
    ·
      refine ⟨67404244652681728403541613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89872326203575637871388817 67404244652681728403541613)
      ·
        refine ⟨25276591744755648151328105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67404244652681728403541613 25276591744755648151328105)
        ·
          refine ⟨18957443808566736113496079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25276591744755648151328105 18957443808566736113496079)
          ·
            refine ⟨28436165712850104170244119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18957443808566736113496079 28436165712850104170244119)
            ·
              refine ⟨42654248569275156255366179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28436165712850104170244119 42654248569275156255366179)
              ·
                refine ⟨63981372853912734383049269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42654248569275156255366179 63981372853912734383049269)
                ·
                  refine ⟨5998253705054318848410869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63981372853912734383049269 5998253705054318848410869)
                  ·
                    refine ⟨562336284848842392038519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5998253705054318848410869 562336284848842392038519)
                    ·
                      rfl

theorem cell22_1642719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1642719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642719 prefixEnd_1642719 := by exact prefixLift 1642719
  have htrace : WordTrace (prefixWord ++ tailWord_1642719) baseStart_1642719 baseEnd_1642719 := by
    simpa [prefixWord, tailWord_1642719, baseEnd_1642719] using wordTrace_append hprefix tailTrace_1642719
  have hstable : (prefixWord ++ tailWord_1642719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642719).length < 2 ^ (prefixWord ++ tailWord_1642719).sum := by decide
  have hdescent : baseEnd_1642719 < baseStart_1642719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642749 : List Nat := [1, 4, 1, 1, 1, 1, 1, 12]
def baseStart_1642749 : Nat := 118140960795 + 1642749 * 2 ^ 59
def prefixEnd_1642749 : Nat := 4983230072969 + 3 ^ 40 * 1642749 * 2
def baseEnd_1642749 : Nat := 62482950495770257087603

theorem tailTrace_1642749 : CollatzResearch.WordTrace tailWord_1642749 prefixEnd_1642749 62482950495770257087603 := by
  unfold tailWord_1642749
  simp only [CollatzResearch.WordTrace]
  refine ⟨59915978325608407037851301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39943985550405604691900867 59915978325608407037851301)
  ·
    refine ⟨11234245936051576319597119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59915978325608407037851301 11234245936051576319597119)
    ·
      refine ⟨16851368904077364479395679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11234245936051576319597119 16851368904077364479395679)
      ·
        refine ⟨25277053356116046719093519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16851368904077364479395679 25277053356116046719093519)
        ·
          refine ⟨37915580034174070078640279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25277053356116046719093519 37915580034174070078640279)
          ·
            refine ⟨56873370051261105117960419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37915580034174070078640279 56873370051261105117960419)
            ·
              refine ⟨85310055076891657676940629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56873370051261105117960419 85310055076891657676940629)
              ·
                refine ⟨62482950495770257087603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 85310055076891657676940629 62482950495770257087603)
                ·
                  rfl

theorem cell22_1642749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 12].length) (baseStart_1642749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642749 prefixEnd_1642749 := by exact prefixLift 1642749
  have htrace : WordTrace (prefixWord ++ tailWord_1642749) baseStart_1642749 baseEnd_1642749 := by
    simpa [prefixWord, tailWord_1642749, baseEnd_1642749] using wordTrace_append hprefix tailTrace_1642749
  have hstable : (prefixWord ++ tailWord_1642749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642749).length < 2 ^ (prefixWord ++ tailWord_1642749).sum := by decide
  have hdescent : baseEnd_1642749 < baseStart_1642749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642779 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_1642779 : Nat := 118140960795 + 1642779 * 2 ^ 59
def prefixEnd_1642779 : Nat := 4983230072969 + 3 ^ 40 * 1642779 * 2
def baseEnd_1642779 : Nat := 562356824075022235538335

theorem tailTrace_1642779 : CollatzResearch.WordTrace tailWord_1642779 prefixEnd_1642779 562356824075022235538335 := by
  unfold tailWord_1642779
  simp only [CollatzResearch.WordTrace]
  refine ⟨59917072515499722161443391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39944715010333148107628927 59917072515499722161443391)
  ·
    refine ⟨89875608773249583242165087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59917072515499722161443391 89875608773249583242165087)
    ·
      refine ⟨134813413159874374863247631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89875608773249583242165087 134813413159874374863247631)
      ·
        refine ⟨202220119739811562294871447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134813413159874374863247631 202220119739811562294871447)
        ·
          refine ⟨303330179609717343442307171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202220119739811562294871447 303330179609717343442307171)
          ·
            refine ⟨454995269414576015163460757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303330179609717343442307171 454995269414576015163460757)
            ·
              refine ⟨21327903253808250710787223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 454995269414576015163460757 21327903253808250710787223)
              ·
                refine ⟨31991854880712376066180835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21327903253808250710787223 31991854880712376066180835)
                ·
                  refine ⟨47987782321068564099271253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31991854880712376066180835 47987782321068564099271253)
                  ·
                    refine ⟨562356824075022235538335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47987782321068564099271253 562356824075022235538335)
                    ·
                      rfl

theorem cell22_1642779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_1642779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642779 prefixEnd_1642779 := by exact prefixLift 1642779
  have htrace : WordTrace (prefixWord ++ tailWord_1642779) baseStart_1642779 baseEnd_1642779 := by
    simpa [prefixWord, tailWord_1642779, baseEnd_1642779] using wordTrace_append hprefix tailTrace_1642779
  have hstable : (prefixWord ++ tailWord_1642779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642779).length < 2 ^ (prefixWord ++ tailWord_1642779).sum := by decide
  have hdescent : baseEnd_1642779 < baseStart_1642779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642832 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 1, 3]
def baseStart_1642832 : Nat := 118140960795 + 1642832 * 2 ^ 59
def prefixEnd_1642832 : Nat := 4983230072969 + 3 ^ 40 * 1642832 * 2
def baseEnd_1642832 : Nat := 562374967058147763963173

theorem tailTrace_1642832 : CollatzResearch.WordTrace tailWord_1642832 prefixEnd_1642832 562374967058147763963173 := by
  unfold tailWord_1642832
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959502792153856106561375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39946003722871808142081833 29959502792153856106561375)
  ·
    refine ⟨44939254188230784159842063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29959502792153856106561375 44939254188230784159842063)
    ·
      refine ⟨67408881282346176239763095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44939254188230784159842063 67408881282346176239763095)
      ·
        refine ⟨101113321923519264359644643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67408881282346176239763095 101113321923519264359644643)
        ·
          refine ⟨151669982885278896539466965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101113321923519264359644643 151669982885278896539466965)
          ·
            refine ⟨3554765223873724137643757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 151669982885278896539466965 3554765223873724137643757)
            ·
              refine ⟨1333036958952646551616409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554765223873724137643757 1333036958952646551616409)
              ·
                refine ⟨999777719214484913712307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333036958952646551616409 999777719214484913712307)
                ·
                  refine ⟨1499666578821727370568461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999777719214484913712307 1499666578821727370568461)
                  ·
                    refine ⟨562374967058147763963173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1499666578821727370568461 562374967058147763963173)
                    ·
                      rfl

theorem cell22_1642832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_1642832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642832 prefixEnd_1642832 := by exact prefixLift 1642832
  have htrace : WordTrace (prefixWord ++ tailWord_1642832) baseStart_1642832 baseEnd_1642832 := by
    simpa [prefixWord, tailWord_1642832, baseEnd_1642832] using wordTrace_append hprefix tailTrace_1642832
  have hstable : (prefixWord ++ tailWord_1642832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642832).length < 2 ^ (prefixWord ++ tailWord_1642832).sum := by decide
  have hdescent : baseEnd_1642832 < baseStart_1642832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642841 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_1642841 : Nat := 118140960795 + 1642841 * 2 ^ 59
def prefixEnd_1642841 : Nat := 4983230072969 + 3 ^ 40 * 1642841 * 2
def baseEnd_1642841 : Nat := 562378047942074740488145

theorem tailTrace_1642841 : CollatzResearch.WordTrace tailWord_1642841 prefixEnd_1642841 562378047942074740488145 := by
  unfold tailWord_1642841
  simp only [CollatzResearch.WordTrace]
  refine ⟨59919333841275106750200377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39946222560850071166800251 59919333841275106750200377)
  ·
    refine ⟨44939500380956330062650283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59919333841275106750200377 44939500380956330062650283)
    ·
      refine ⟨67409250571434495093975425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44939500380956330062650283 67409250571434495093975425)
      ·
        refine ⟨50556937928575871320481569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67409250571434495093975425 50556937928575871320481569)
        ·
          refine ⟨37917703446431903490361177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50556937928575871320481569 37917703446431903490361177)
          ·
            refine ⟨28438277584823927617770883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37917703446431903490361177 28438277584823927617770883)
            ·
              refine ⟨42657416377235891426656325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28438277584823927617770883 42657416377235891426656325)
              ·
                refine ⟨7998265570731729642498061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42657416377235891426656325 7998265570731729642498061)
                ·
                  refine ⟨2999349589024398615936773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7998265570731729642498061 2999349589024398615936773)
                  ·
                    refine ⟨562378047942074740488145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999349589024398615936773 562378047942074740488145)
                    ·
                      rfl

theorem cell22_1642841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_1642841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642841 prefixEnd_1642841 := by exact prefixLift 1642841
  have htrace : WordTrace (prefixWord ++ tailWord_1642841) baseStart_1642841 baseEnd_1642841 := by
    simpa [prefixWord, tailWord_1642841, baseEnd_1642841] using wordTrace_append hprefix tailTrace_1642841
  have hstable : (prefixWord ++ tailWord_1642841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642841).length < 2 ^ (prefixWord ++ tailWord_1642841).sum := by decide
  have hdescent : baseEnd_1642841 < baseStart_1642841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642873 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 4]
def baseStart_1642873 : Nat := 118140960795 + 1642873 * 2 ^ 59
def prefixEnd_1642873 : Nat := 4983230072969 + 3 ^ 40 * 1642873 * 2
def baseEnd_1642873 : Nat := 187463000732012441229349

theorem tailTrace_1642873 : CollatzResearch.WordTrace tailWord_1642873 prefixEnd_1642873 187463000732012441229349 := by
  unfold tailWord_1642873
  simp only [CollatzResearch.WordTrace]
  refine ⟨59920500977159176215365273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39947000651439450810243515 59920500977159176215365273)
  ·
    refine ⟨44940375732869382161523955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59920500977159176215365273 44940375732869382161523955)
    ·
      refine ⟨67410563599304073242285933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44940375732869382161523955 67410563599304073242285933)
      ·
        refine ⟨25278961349739027465857225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67410563599304073242285933 25278961349739027465857225)
        ·
          refine ⟨18959221012304270599392919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25278961349739027465857225 18959221012304270599392919)
          ·
            refine ⟨28438831518456405899089379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18959221012304270599392919 28438831518456405899089379)
            ·
              refine ⟨42658247277684608848634069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28438831518456405899089379 42658247277684608848634069)
              ·
                refine ⟨999802670570733019889861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42658247277684608848634069 999802670570733019889861)
                ·
                  refine ⟨187463000732012441229349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999802670570733019889861 187463000732012441229349)
                  ·
                    rfl

theorem cell22_1642873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_1642873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642873 prefixEnd_1642873 := by exact prefixLift 1642873
  have htrace : WordTrace (prefixWord ++ tailWord_1642873) baseStart_1642873 baseEnd_1642873 := by
    simpa [prefixWord, tailWord_1642873, baseEnd_1642873] using wordTrace_append hprefix tailTrace_1642873
  have hstable : (prefixWord ++ tailWord_1642873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642873).length < 2 ^ (prefixWord ++ tailWord_1642873).sum := by decide
  have hdescent : baseEnd_1642873 < baseStart_1642873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642875 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 1, 4]
def baseStart_1642875 : Nat := 118140960795 + 1642875 * 2 ^ 59
def prefixEnd_1642875 : Nat := 4983230072969 + 3 ^ 40 * 1642875 * 2
def baseEnd_1642875 : Nat := 562389686836909985138041

theorem tailTrace_1642875 : CollatzResearch.WordTrace tailWord_1642875 prefixEnd_1642875 562389686836909985138041 := by
  unfold tailWord_1642875
  simp only [CollatzResearch.WordTrace]
  refine ⟨59920573923151930556938079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39947049282101287037958719 59920573923151930556938079)
  ·
    refine ⟨89880860884727895835407119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59920573923151930556938079 89880860884727895835407119)
    ·
      refine ⟨134821291327091843753110679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89880860884727895835407119 134821291327091843753110679)
      ·
        refine ⟨202231936990637765629666019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134821291327091843753110679 202231936990637765629666019)
        ·
          refine ⟨303347905485956648444499029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202231936990637765629666019 303347905485956648444499029)
          ·
            refine ⟨3554858267413554473958973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 303347905485956648444499029 3554858267413554473958973)
            ·
              refine ⟨1333071850280082927734615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554858267413554473958973 1333071850280082927734615)
              ·
                refine ⟨1999607775420124391601923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333071850280082927734615 1999607775420124391601923)
                ·
                  refine ⟨2999411663130186587402885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999607775420124391601923 2999411663130186587402885)
                  ·
                    refine ⟨562389686836909985138041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2999411663130186587402885 562389686836909985138041)
                    ·
                      rfl

theorem cell22_1642875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 4].length) (baseStart_1642875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642875 prefixEnd_1642875 := by exact prefixLift 1642875
  have htrace : WordTrace (prefixWord ++ tailWord_1642875) baseStart_1642875 baseEnd_1642875 := by
    simpa [prefixWord, tailWord_1642875, baseEnd_1642875] using wordTrace_append hprefix tailTrace_1642875
  have hstable : (prefixWord ++ tailWord_1642875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642875).length < 2 ^ (prefixWord ++ tailWord_1642875).sum := by decide
  have hdescent : baseEnd_1642875 < baseStart_1642875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642920 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1642920 : Nat := 118140960795 + 1642920 * 2 ^ 59
def prefixEnd_1642920 : Nat := 4983230072969 + 3 ^ 40 * 1642920 * 2
def baseEnd_1642920 : Nat := 562405091256544867762903

theorem tailTrace_1642920 : CollatzResearch.WordTrace tailWord_1642920 prefixEnd_1642920 562405091256544867762903 := by
  unfold tailWord_1642920
  simp only [CollatzResearch.WordTrace]
  refine ⟨29961107603994451621163107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39948143471992602161550809 29961107603994451621163107)
  ·
    refine ⟨44941661405991677431744661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29961107603994451621163107 44941661405991677431744661)
    ·
      refine ⟨2106640378405859879613031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44941661405991677431744661 2106640378405859879613031)
      ·
        refine ⟨3159960567608789819419547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106640378405859879613031 3159960567608789819419547)
        ·
          refine ⟨4739940851413184729129321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159960567608789819419547 4739940851413184729129321)
          ·
            refine ⟨3554955638559888546846991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4739940851413184729129321 3554955638559888546846991)
            ·
              refine ⟨5332433457839832820270487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554955638559888546846991 5332433457839832820270487)
              ·
                refine ⟨7998650186759749230405731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332433457839832820270487 7998650186759749230405731)
                ·
                  refine ⟨11997975280139623845608597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7998650186759749230405731 11997975280139623845608597)
                  ·
                    refine ⟨562405091256544867762903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11997975280139623845608597 562405091256544867762903)
                    ·
                      rfl

theorem cell22_1642920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1642920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642920 prefixEnd_1642920 := by exact prefixLift 1642920
  have htrace : WordTrace (prefixWord ++ tailWord_1642920) baseStart_1642920 baseEnd_1642920 := by
    simpa [prefixWord, tailWord_1642920, baseEnd_1642920] using wordTrace_append hprefix tailTrace_1642920
  have hstable : (prefixWord ++ tailWord_1642920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642920).length < 2 ^ (prefixWord ++ tailWord_1642920).sum := by decide
  have hdescent : baseEnd_1642920 < baseStart_1642920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642984 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1642984 : Nat := 118140960795 + 1642984 * 2 ^ 59
def prefixEnd_1642984 : Nat := 4983230072969 + 3 ^ 40 * 1642984 * 2
def baseEnd_1642984 : Nat := 562426999764470034162707

theorem tailTrace_1642984 : CollatzResearch.WordTrace tailWord_1642984 prefixEnd_1642984 562426999764470034162707 := by
  unfold tailWord_1642984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29962274739878521086328003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39949699653171361448437337 29962274739878521086328003)
  ·
    refine ⟨44943412109817781629492005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29962274739878521086328003 44943412109817781629492005)
    ·
      refine ⟨8426889770590834055529751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44943412109817781629492005 8426889770590834055529751)
      ·
        refine ⟨12640334655886251083294627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426889770590834055529751 12640334655886251083294627)
        ·
          refine ⟨18960501983829376624941941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640334655886251083294627 18960501983829376624941941)
          ·
            refine ⟨1777547060984004058588307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18960501983829376624941941 1777547060984004058588307)
            ·
              refine ⟨2666320591476006087882461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777547060984004058588307 2666320591476006087882461)
              ·
                refine ⟨999870221803502282955923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2666320591476006087882461 999870221803502282955923)
                ·
                  refine ⟨1499805332705253424433885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999870221803502282955923 1499805332705253424433885)
                  ·
                    refine ⟨562426999764470034162707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1499805332705253424433885 562426999764470034162707)
                    ·
                      rfl

theorem cell22_1642984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1642984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1642984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1642984 prefixEnd_1642984 := by exact prefixLift 1642984
  have htrace : WordTrace (prefixWord ++ tailWord_1642984) baseStart_1642984 baseEnd_1642984 := by
    simpa [prefixWord, tailWord_1642984, baseEnd_1642984] using wordTrace_append hprefix tailTrace_1642984
  have hstable : (prefixWord ++ tailWord_1642984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642984).length < 2 ^ (prefixWord ++ tailWord_1642984).sum := by decide
  have hdescent : baseEnd_1642984 < baseStart_1642984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643138 : List Nat := [3, 4, 3, 1, 1, 2, 2, 6]
def baseStart_1643138 : Nat := 118140960795 + 1643138 * 2 ^ 59
def prefixEnd_1643138 : Nat := 4983230072969 + 3 ^ 40 * 1643138 * 2
def baseEnd_1643138 : Nat := 62497746345740551756915

theorem tailTrace_1643138 : CollatzResearch.WordTrace tailWord_1643138 prefixEnd_1643138 62497746345740551756915 := by
  unfold tailWord_1643138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982541580299781618440517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39953444214132750982508045 14982541580299781618440517)
  ·
    refine ⟨2809226546306209053457597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14982541580299781618440517 2809226546306209053457597)
    ·
      refine ⟨1053459954864828395046599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2809226546306209053457597 1053459954864828395046599)
      ·
        refine ⟨1580189932297242592569899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053459954864828395046599 1580189932297242592569899)
        ·
          refine ⟨2370284898445863888854849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580189932297242592569899 2370284898445863888854849)
          ·
            refine ⟨1777713673834397916641137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370284898445863888854849 1777713673834397916641137)
            ·
              refine ⟨1333285255375798437480853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777713673834397916641137 1333285255375798437480853)
              ·
                refine ⟨62497746345740551756915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1333285255375798437480853 62497746345740551756915)
                ·
                  rfl

theorem cell22_1643138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_1643138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643138 prefixEnd_1643138 := by exact prefixLift 1643138
  have htrace : WordTrace (prefixWord ++ tailWord_1643138) baseStart_1643138 baseEnd_1643138 := by
    simpa [prefixWord, tailWord_1643138, baseEnd_1643138] using wordTrace_append hprefix tailTrace_1643138
  have hstable : (prefixWord ++ tailWord_1643138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643138).length < 2 ^ (prefixWord ++ tailWord_1643138).sum := by decide
  have hdescent : baseEnd_1643138 < baseStart_1643138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643213 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1643213 : Nat := 118140960795 + 1643213 * 2 ^ 59
def prefixEnd_1643213 : Nat := 4983230072969 + 3 ^ 40 * 1643213 * 2
def baseEnd_1643213 : Nat := 562505391144389770187005

theorem tailTrace_1643213 : CollatzResearch.WordTrace tailWord_1643213 prefixEnd_1643213 562505391144389770187005 := by
  unfold tailWord_1643213
  simp only [CollatzResearch.WordTrace]
  refine ⟨59932901795927414282742293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39955267863951609521828195 59932901795927414282742293)
  ·
    refine ⟨2809354771684097544503545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59932901795927414282742293 2809354771684097544503545)
    ·
      refine ⟨2107016078763073158377659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2809354771684097544503545 2107016078763073158377659)
      ·
        refine ⟨3160524118144609737566489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107016078763073158377659 3160524118144609737566489)
        ·
          refine ⟨2370393088608457303174867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3160524118144609737566489 2370393088608457303174867)
          ·
            refine ⟨3555589632912685954762301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370393088608457303174867 3555589632912685954762301)
            ·
              refine ⟨1333346112342257233035863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3555589632912685954762301 1333346112342257233035863)
              ·
                refine ⟨2000019168513385849553795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333346112342257233035863 2000019168513385849553795)
                ·
                  refine ⟨3000028752770078774330693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000019168513385849553795 3000028752770078774330693)
                  ·
                    refine ⟨562505391144389770187005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3000028752770078774330693 562505391144389770187005)
                    ·
                      rfl

theorem cell22_1643213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1643213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643213 prefixEnd_1643213 := by exact prefixLift 1643213
  have htrace : WordTrace (prefixWord ++ tailWord_1643213) baseStart_1643213 baseEnd_1643213 := by
    simpa [prefixWord, tailWord_1643213, baseEnd_1643213] using wordTrace_append hprefix tailTrace_1643213
  have hstable : (prefixWord ++ tailWord_1643213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643213).length < 2 ^ (prefixWord ++ tailWord_1643213).sum := by decide
  have hdescent : baseEnd_1643213 < baseStart_1643213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643228 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_1643228 : Nat := 118140960795 + 1643228 * 2 ^ 59
def prefixEnd_1643228 : Nat := 4983230072969 + 3 ^ 40 * 1643228 * 2
def baseEnd_1643228 : Nat := 187503508650311577020653

theorem tailTrace_1643228 : CollatzResearch.WordTrace tailWord_1643228 prefixEnd_1643228 187503508650311577020653 := by
  unfold tailWord_1643228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966724445436535922269169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39955632593915381229692225 29966724445436535922269169)
  ·
    refine ⟨22475043334077401941701877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29966724445436535922269169 22475043334077401941701877)
    ·
      refine ⟨2107035312569756432034551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22475043334077401941701877 2107035312569756432034551)
      ·
        refine ⟨3160552968854634648051827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107035312569756432034551 3160552968854634648051827)
        ·
          refine ⟨4740829453281951972077741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160552968854634648051827 4740829453281951972077741)
          ·
            refine ⟨1777811044980731989529153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4740829453281951972077741 1777811044980731989529153)
            ·
              refine ⟨1333358283735548992146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777811044980731989529153 1333358283735548992146865)
              ·
                refine ⟨1000018712801661744110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333358283735548992146865 1000018712801661744110149)
                ·
                  refine ⟨187503508650311577020653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000018712801661744110149 187503508650311577020653)
                  ·
                    rfl

theorem cell22_1643228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_1643228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643228 prefixEnd_1643228 := by exact prefixLift 1643228
  have htrace : WordTrace (prefixWord ++ tailWord_1643228) baseStart_1643228 baseEnd_1643228 := by
    simpa [prefixWord, tailWord_1643228, baseEnd_1643228] using wordTrace_append hprefix tailTrace_1643228
  have hstable : (prefixWord ++ tailWord_1643228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643228).length < 2 ^ (prefixWord ++ tailWord_1643228).sum := by decide
  have hdescent : baseEnd_1643228 < baseStart_1643228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643254 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1643254 : Nat := 118140960795 + 1643254 * 2 ^ 59
def prefixEnd_1643254 : Nat := 4983230072969 + 3 ^ 40 * 1643254 * 2
def baseEnd_1643254 : Nat := 562519426282279329911879

theorem tailTrace_1643254 : CollatzResearch.WordTrace tailWord_1643254 prefixEnd_1643254 562519426282279329911879 := by
  unfold tailWord_1643254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745899824298679892811551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39956264792519252189989877 3745899824298679892811551)
  ·
    refine ⟨5618849736448019839217327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745899824298679892811551 5618849736448019839217327)
    ·
      refine ⟨8428274604672029758825991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618849736448019839217327 8428274604672029758825991)
      ·
        refine ⟨12642411907008044638238987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428274604672029758825991 12642411907008044638238987)
        ·
          refine ⟨18963617860512066957358481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12642411907008044638238987 18963617860512066957358481)
          ·
            refine ⟨14222713395384050218018861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18963617860512066957358481 14222713395384050218018861)
            ·
              refine ⟨5333517523269018831757073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14222713395384050218018861 5333517523269018831757073)
              ·
                refine ⟨4000138142451764123817805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333517523269018831757073 4000138142451764123817805)
                ·
                  refine ⟨1500051803419411546431677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4000138142451764123817805 1500051803419411546431677)
                  ·
                    refine ⟨562519426282279329911879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500051803419411546431677 562519426282279329911879)
                    ·
                      rfl

theorem cell22_1643254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1643254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643254 prefixEnd_1643254 := by exact prefixLift 1643254
  have htrace : WordTrace (prefixWord ++ tailWord_1643254) baseStart_1643254 baseEnd_1643254 := by
    simpa [prefixWord, tailWord_1643254, baseEnd_1643254] using wordTrace_append hprefix tailTrace_1643254
  have hstable : (prefixWord ++ tailWord_1643254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643254).length < 2 ^ (prefixWord ++ tailWord_1643254).sum := by decide
  have hdescent : baseEnd_1643254 < baseStart_1643254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643265 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1643265 : Nat := 118140960795 + 1643265 * 2 ^ 59
def prefixEnd_1643265 : Nat := 4983230072969 + 3 ^ 40 * 1643265 * 2
def baseEnd_1643265 : Nat := 562523191807078967886845

theorem tailTrace_1643265 : CollatzResearch.WordTrace tailWord_1643265 prefixEnd_1643265 562523191807078967886845 := by
  unfold tailWord_1643265
  simp only [CollatzResearch.WordTrace]
  refine ⟨59934798391739027163635249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39956532261159351442423499 59934798391739027163635249)
  ·
    refine ⟨44951098793804270372726437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59934798391739027163635249 44951098793804270372726437)
    ·
      refine ⟨8428331023838300694886207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44951098793804270372726437 8428331023838300694886207)
      ·
        refine ⟨12642496535757451042329311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428331023838300694886207 12642496535757451042329311)
        ·
          refine ⟨18963744803636176563493967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12642496535757451042329311 18963744803636176563493967)
          ·
            refine ⟨28445617205454264845240951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18963744803636176563493967 28445617205454264845240951)
            ·
              refine ⟨42668425808181397267861427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28445617205454264845240951 42668425808181397267861427)
              ·
                refine ⟨64002638712272095901792141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42668425808181397267861427 64002638712272095901792141)
                ·
                  refine ⟨24000989517102035963172053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64002638712272095901792141 24000989517102035963172053)
                  ·
                    refine ⟨562523191807078967886845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24000989517102035963172053 562523191807078967886845)
                    ·
                      rfl

theorem cell22_1643265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1643265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643265 prefixEnd_1643265 := by exact prefixLift 1643265
  have htrace : WordTrace (prefixWord ++ tailWord_1643265) baseStart_1643265 baseEnd_1643265 := by
    simpa [prefixWord, tailWord_1643265, baseEnd_1643265] using wordTrace_append hprefix tailTrace_1643265
  have hstable : (prefixWord ++ tailWord_1643265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643265).length < 2 ^ (prefixWord ++ tailWord_1643265).sum := by decide
  have hdescent : baseEnd_1643265 < baseStart_1643265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643271 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 1, 3]
def baseStart_1643271 : Nat := 118140960795 + 1643271 * 2 ^ 59
def prefixEnd_1643271 : Nat := 4983230072969 + 3 ^ 40 * 1643271 * 2
def baseEnd_1643271 : Nat := 562525245729696952236827

theorem tailTrace_1643271 : CollatzResearch.WordTrace tailWord_1643271 prefixEnd_1643271 562525245729696952236827 := by
  unfold tailWord_1643271
  simp only [CollatzResearch.WordTrace]
  refine ⟨59935017229717290188353667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39956678153144860125569111 59935017229717290188353667)
  ·
    refine ⟨89902525844575935282530501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59935017229717290188353667 89902525844575935282530501)
    ·
      refine ⟨16856723595857987865474469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89902525844575935282530501 16856723595857987865474469)
      ·
        refine ⟨3160635674223372724776463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16856723595857987865474469 3160635674223372724776463)
        ·
          refine ⟨4740953511335059087164695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160635674223372724776463 4740953511335059087164695)
          ·
            refine ⟨7111430267002588630747043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740953511335059087164695 7111430267002588630747043)
            ·
              refine ⟨10667145400503882946120565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111430267002588630747043 10667145400503882946120565)
              ·
                refine ⟨1000044881297239026198803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10667145400503882946120565 1000044881297239026198803)
                ·
                  refine ⟨1500067321945858539298205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000044881297239026198803 1500067321945858539298205)
                  ·
                    refine ⟨562525245729696952236827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500067321945858539298205 562525245729696952236827)
                    ·
                      rfl

theorem cell22_1643271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_1643271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643271 prefixEnd_1643271 := by exact prefixLift 1643271
  have htrace : WordTrace (prefixWord ++ tailWord_1643271) baseStart_1643271 baseEnd_1643271 := by
    simpa [prefixWord, tailWord_1643271, baseEnd_1643271] using wordTrace_append hprefix tailTrace_1643271
  have hstable : (prefixWord ++ tailWord_1643271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643271).length < 2 ^ (prefixWord ++ tailWord_1643271).sum := by decide
  have hdescent : baseEnd_1643271 < baseStart_1643271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643314 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_1643314 : Nat := 118140960795 + 1643314 * 2 ^ 59
def prefixEnd_1643314 : Nat := 4983230072969 + 3 ^ 40 * 1643314 * 2
def baseEnd_1643314 : Nat := 562539965508459173411695

theorem tailTrace_1643314 : CollatzResearch.WordTrace tailWord_1643314 prefixEnd_1643314 562539965508459173411695 := by
  unfold tailWord_1643314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984146392140377133042249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39957723712374339021445997 14984146392140377133042249)
  ·
    refine ⟨11238109794105282849781687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14984146392140377133042249 11238109794105282849781687)
    ·
      refine ⟨16857164691157924274672531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11238109794105282849781687 16857164691157924274672531)
      ·
        refine ⟨25285747036736886412008797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16857164691157924274672531 25285747036736886412008797)
        ·
          refine ⟨9482155138776332404503299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25285747036736886412008797 9482155138776332404503299)
          ·
            refine ⟨14223232708164498606754949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482155138776332404503299 14223232708164498606754949)
            ·
              refine ⟨2666856132780843488766553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14223232708164498606754949 2666856132780843488766553)
              ·
                refine ⟨2000142099585632616574915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666856132780843488766553 2000142099585632616574915)
                ·
                  refine ⟨3000213149378448924862373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000142099585632616574915 3000213149378448924862373)
                  ·
                    refine ⟨562539965508459173411695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3000213149378448924862373 562539965508459173411695)
                    ·
                      rfl

theorem cell22_1643314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_1643314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643314 prefixEnd_1643314 := by exact prefixLift 1643314
  have htrace : WordTrace (prefixWord ++ tailWord_1643314) baseStart_1643314 baseEnd_1643314 := by
    simpa [prefixWord, tailWord_1643314, baseEnd_1643314] using wordTrace_append hprefix tailTrace_1643314
  have hstable : (prefixWord ++ tailWord_1643314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643314).length < 2 ^ (prefixWord ++ tailWord_1643314).sum := by decide
  have hdescent : baseEnd_1643314 < baseStart_1643314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643346 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_1643346 : Nat := 118140960795 + 1643346 * 2 ^ 59
def prefixEnd_1643346 : Nat := 4983230072969 + 3 ^ 40 * 1643346 * 2
def baseEnd_1643346 : Nat := 187516973254140585537199

theorem tailTrace_1643346 : CollatzResearch.WordTrace tailWord_1643346 prefixEnd_1643346 187516973254140585537199 := by
  unfold tailWord_1643346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984438176111394499333473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39958501802963718664889261 14984438176111394499333473)
  ·
    refine ⟨11238328632083545874500105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14984438176111394499333473 11238328632083545874500105)
    ·
      refine ⟨8428746474062659405875079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11238328632083545874500105 8428746474062659405875079)
      ·
        refine ⟨12643119711093989108812619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428746474062659405875079 12643119711093989108812619)
        ·
          refine ⟨18964679566640983663218929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643119711093989108812619 18964679566640983663218929)
          ·
            refine ⟨14223509674980737747414197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18964679566640983663218929 14223509674980737747414197)
            ·
              refine ⟨1333454032029444163820081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14223509674980737747414197 1333454032029444163820081)
              ·
                refine ⟨1000090524022083122865061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333454032029444163820081 1000090524022083122865061)
                ·
                  refine ⟨187516973254140585537199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000090524022083122865061 187516973254140585537199)
                  ·
                    rfl

theorem cell22_1643346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_1643346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643346 prefixEnd_1643346 := by exact prefixLift 1643346
  have htrace : WordTrace (prefixWord ++ tailWord_1643346) baseStart_1643346 baseEnd_1643346 := by
    simpa [prefixWord, tailWord_1643346, baseEnd_1643346] using wordTrace_append hprefix tailTrace_1643346
  have hstable : (prefixWord ++ tailWord_1643346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643346).length < 2 ^ (prefixWord ++ tailWord_1643346).sum := by decide
  have hdescent : baseEnd_1643346 < baseStart_1643346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643355 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_1643355 : Nat := 118140960795 + 1643355 * 2 ^ 59
def prefixEnd_1643355 : Nat := 4983230072969 + 3 ^ 40 * 1643355 * 2
def baseEnd_1643355 : Nat := 562554000646348733136569

theorem tailTrace_1643355 : CollatzResearch.WordTrace tailWord_1643355 prefixEnd_1643355 562554000646348733136569 := by
  unfold tailWord_1643355
  simp only [CollatzResearch.WordTrace]
  refine ⟨59938080961412972534411519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39958720640941981689607679 59938080961412972534411519)
  ·
    refine ⟨89907121442119458801617279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59938080961412972534411519 89907121442119458801617279)
    ·
      refine ⟨134860682163179188202425919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89907121442119458801617279 134860682163179188202425919)
      ·
        refine ⟨202291023244768782303638879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134860682163179188202425919 202291023244768782303638879)
        ·
          refine ⟨303436534867153173455458319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202291023244768782303638879 303436534867153173455458319)
          ·
            refine ⟨455154802300729760183187479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303436534867153173455458319 455154802300729760183187479)
            ·
              refine ⟨682732203451094640274781219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455154802300729760183187479 682732203451094640274781219)
              ·
                refine ⟨1024098305176641960412171829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682732203451094640274781219 1024098305176641960412171829)
                ·
                  refine ⟨96009216110310183788641109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1024098305176641960412171829 96009216110310183788641109)
                  ·
                    refine ⟨562554000646348733136569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 96009216110310183788641109 562554000646348733136569)
                    ·
                      rfl

theorem cell22_1643355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_1643355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643355 prefixEnd_1643355 := by exact prefixLift 1643355
  have htrace : WordTrace (prefixWord ++ tailWord_1643355) baseStart_1643355 baseEnd_1643355 := by
    simpa [prefixWord, tailWord_1643355, baseEnd_1643355] using wordTrace_append hprefix tailTrace_1643355
  have hstable : (prefixWord ++ tailWord_1643355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643355).length < 2 ^ (prefixWord ++ tailWord_1643355).sum := by decide
  have hdescent : baseEnd_1643355 < baseStart_1643355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643453 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 5]
def baseStart_1643453 : Nat := 118140960795 + 1643453 * 2 ^ 59
def prefixEnd_1643453 : Nat := 4983230072969 + 3 ^ 40 * 1643453 * 2
def baseEnd_1643453 : Nat := 187529182683036381395423

theorem tailTrace_1643453 : CollatzResearch.WordTrace tailWord_1643453 prefixEnd_1643453 187529182683036381395423 := by
  unfold tailWord_1643453
  simp only [CollatzResearch.WordTrace]
  refine ⟨59941655315057935271479013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39961103543371956847652675 59941655315057935271479013)
  ·
    refine ⟨11239060371573362863402315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59941655315057935271479013 11239060371573362863402315)
    ·
      refine ⟨16858590557360044295103473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11239060371573362863402315 16858590557360044295103473)
      ·
        refine ⟨12643942918020033221327605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16858590557360044295103473 12643942918020033221327605)
        ·
          refine ⟨1185369648564378114499463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12643942918020033221327605 1185369648564378114499463)
          ·
            refine ⟨1778054472846567171749195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185369648564378114499463 1778054472846567171749195)
            ·
              refine ⟨2667081709269850757623793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778054472846567171749195 2667081709269850757623793)
              ·
                refine ⟨2000311281952388068217845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667081709269850757623793 2000311281952388068217845)
                ·
                  refine ⟨187529182683036381395423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2000311281952388068217845 187529182683036381395423)
                  ·
                    rfl

theorem cell22_1643453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_1643453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643453 prefixEnd_1643453 := by exact prefixLift 1643453
  have htrace : WordTrace (prefixWord ++ tailWord_1643453) baseStart_1643453 baseEnd_1643453 := by
    simpa [prefixWord, tailWord_1643453, baseEnd_1643453] using wordTrace_append hprefix tailTrace_1643453
  have hstable : (prefixWord ++ tailWord_1643453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643453).length < 2 ^ (prefixWord ++ tailWord_1643453).sum := by decide
  have hdescent : baseEnd_1643453 < baseStart_1643453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643498 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_1643498 : Nat := 118140960795 + 1643498 * 2 ^ 59
def prefixEnd_1643498 : Nat := 4983230072969 + 3 ^ 40 * 1643498 * 2
def baseEnd_1643498 : Nat := 187534317489581342270377

theorem tailTrace_1643498 : CollatzResearch.WordTrace tailWord_1643498 prefixEnd_1643498 187534317489581342270377 := by
  unfold tailWord_1643498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14985824149973726989216787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39962197733263271971244765 14985824149973726989216787)
  ·
    refine ⟨22478736224960590483825181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14985824149973726989216787 22478736224960590483825181)
    ·
      refine ⟨8429526084360221431434443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22478736224960590483825181 8429526084360221431434443)
      ·
        refine ⟨12644289126540332147151665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429526084360221431434443 12644289126540332147151665)
        ·
          refine ⟨9483216844905249110363749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12644289126540332147151665 9483216844905249110363749)
          ·
            refine ⟨1778103158419734208193203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9483216844905249110363749 1778103158419734208193203)
            ·
              refine ⟨2667154737629601312289805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778103158419734208193203 2667154737629601312289805)
              ·
                refine ⟨1000183026611100492108677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2667154737629601312289805 1000183026611100492108677)
                ·
                  refine ⟨187534317489581342270377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000183026611100492108677 187534317489581342270377)
                  ·
                    rfl

theorem cell22_1643498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_1643498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643498 prefixEnd_1643498 := by exact prefixLift 1643498
  have htrace : WordTrace (prefixWord ++ tailWord_1643498) baseStart_1643498 baseEnd_1643498 := by
    simpa [prefixWord, tailWord_1643498, baseEnd_1643498] using wordTrace_append hprefix tailTrace_1643498
  have hstable : (prefixWord ++ tailWord_1643498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643498).length < 2 ^ (prefixWord ++ tailWord_1643498).sum := by decide
  have hdescent : baseEnd_1643498 < baseStart_1643498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643530 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_1643530 : Nat := 118140960795 + 1643530 * 2 ^ 59
def prefixEnd_1643530 : Nat := 4983230072969 + 3 ^ 40 * 1643530 * 2
def baseEnd_1643530 : Nat := 562613906722706610011033

theorem tailTrace_1643530 : CollatzResearch.WordTrace tailWord_1643530 prefixEnd_1643530 562613906722706610011033 := by
  unfold tailWord_1643530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986115933944744355508011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39962975823852651614688029 14986115933944744355508011)
  ·
    refine ⟨22479173900917116533262017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14986115933944744355508011 22479173900917116533262017)
    ·
      refine ⟨16859380425687837399946513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22479173900917116533262017 16859380425687837399946513)
      ·
        refine ⟨12644535319265878049959885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16859380425687837399946513 12644535319265878049959885)
        ·
          refine ⟨4741700744724704268734957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12644535319265878049959885 4741700744724704268734957)
          ·
            refine ⟨1778137779271764100775609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4741700744724704268734957 1778137779271764100775609)
            ·
              refine ⟨1333603334453823075581707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778137779271764100775609 1333603334453823075581707)
              ·
                refine ⟨2000405001680734613372561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333603334453823075581707 2000405001680734613372561)
                ·
                  refine ⟨1500303751260550960029421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2000405001680734613372561 1500303751260550960029421)
                  ·
                    refine ⟨562613906722706610011033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500303751260550960029421 562613906722706610011033)
                    ·
                      rfl

theorem cell22_1643530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_1643530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643530 prefixEnd_1643530 := by exact prefixLift 1643530
  have htrace : WordTrace (prefixWord ++ tailWord_1643530) baseStart_1643530 baseEnd_1643530 := by
    simpa [prefixWord, tailWord_1643530, baseEnd_1643530] using wordTrace_append hprefix tailTrace_1643530
  have hstable : (prefixWord ++ tailWord_1643530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643530).length < 2 ^ (prefixWord ++ tailWord_1643530).sum := by decide
  have hdescent : baseEnd_1643530 < baseStart_1643530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643569 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1643569 : Nat := 118140960795 + 1643569 * 2 ^ 59
def prefixEnd_1643569 : Nat := 4983230072969 + 3 ^ 40 * 1643569 * 2
def baseEnd_1643569 : Nat := 562627257219723508285913

theorem tailTrace_1643569 : CollatzResearch.WordTrace tailWord_1643569 prefixEnd_1643569 562627257219723508285913 := by
  unfold tailWord_1643569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59945886182637687082701761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39963924121758458055134507 59945886182637687082701761)
  ·
    refine ⟨44959414636978265312026321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59945886182637687082701761 44959414636978265312026321)
    ·
      refine ⟨33719560977733698984019741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44959414636978265312026321 33719560977733698984019741)
      ·
        refine ⟨12644835366650137119007403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33719560977733698984019741 12644835366650137119007403)
        ·
          refine ⟨18967253049975205678511105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12644835366650137119007403 18967253049975205678511105)
          ·
            refine ⟨14225439787481404258883329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18967253049975205678511105 14225439787481404258883329)
            ·
              refine ⟨10669079840611053194162497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14225439787481404258883329 10669079840611053194162497)
              ·
                refine ⟨8001809880458289895621873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10669079840611053194162497 8001809880458289895621873)
                ·
                  refine ⟨6001357410343717421716405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8001809880458289895621873 6001357410343717421716405)
                  ·
                    refine ⟨562627257219723508285913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6001357410343717421716405 562627257219723508285913)
                    ·
                      rfl

theorem cell22_1643569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1643569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643569 prefixEnd_1643569 := by exact prefixLift 1643569
  have htrace : WordTrace (prefixWord ++ tailWord_1643569) baseStart_1643569 baseEnd_1643569 := by
    simpa [prefixWord, tailWord_1643569, baseEnd_1643569] using wordTrace_append hprefix tailTrace_1643569
  have hstable : (prefixWord ++ tailWord_1643569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643569).length < 2 ^ (prefixWord ++ tailWord_1643569).sum := by decide
  have hdescent : baseEnd_1643569 < baseStart_1643569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643584 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_1643584 : Nat := 118140960795 + 1643584 * 2 ^ 59
def prefixEnd_1643584 : Nat := 4983230072969 + 3 ^ 40 * 1643584 * 2
def baseEnd_1643584 : Nat := 562632392026268469160867

theorem tailTrace_1643584 : CollatzResearch.WordTrace tailWord_1643584 prefixEnd_1643584 562632392026268469160867 := by
  unfold tailWord_1643584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973216638791672322248903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39964288851722229762998537 29973216638791672322248903)
  ·
    refine ⟨44959824958187508483373355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29973216638791672322248903 44959824958187508483373355)
    ·
      refine ⟨67439737437281262725060033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44959824958187508483373355 67439737437281262725060033)
      ·
        refine ⟨50579803077960947043795025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67439737437281262725060033 50579803077960947043795025)
        ·
          refine ⟨37934852308470710282846269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50579803077960947043795025 37934852308470710282846269)
          ·
            refine ⟨14225569615676516356067351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37934852308470710282846269 14225569615676516356067351)
            ·
              refine ⟨21338354423514774534101027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225569615676516356067351 21338354423514774534101027)
              ·
                refine ⟨32007531635272161801151541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21338354423514774534101027 32007531635272161801151541)
                ·
                  refine ⟨3000706090806765168857957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32007531635272161801151541 3000706090806765168857957)
                  ·
                    refine ⟨562632392026268469160867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3000706090806765168857957 562632392026268469160867)
                    ·
                      rfl

theorem cell22_1643584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_1643584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643584 prefixEnd_1643584 := by exact prefixLift 1643584
  have htrace : WordTrace (prefixWord ++ tailWord_1643584) baseStart_1643584 baseEnd_1643584 := by
    simpa [prefixWord, tailWord_1643584, baseEnd_1643584] using wordTrace_append hprefix tailTrace_1643584
  have hstable : (prefixWord ++ tailWord_1643584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643584).length < 2 ^ (prefixWord ++ tailWord_1643584).sum := by decide
  have hdescent : baseEnd_1643584 < baseStart_1643584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643631 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 4, 3]
def baseStart_1643631 : Nat := 118140960795 + 1643631 * 2 ^ 59
def prefixEnd_1643631 : Nat := 4983230072969 + 3 ^ 40 * 1643631 * 2
def baseEnd_1643631 : Nat := 562648481086776013235723

theorem tailTrace_1643631 : CollatzResearch.WordTrace tailWord_1643631 prefixEnd_1643631 562648481086776013235723 := by
  unfold tailWord_1643631
  simp only [CollatzResearch.WordTrace]
  refine ⟨59948147508413071671458747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39965431672275381114305831 59948147508413071671458747)
  ·
    refine ⟨89922221262619607507188121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59948147508413071671458747 89922221262619607507188121)
    ·
      refine ⟨67441665946964705630391091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89922221262619607507188121 67441665946964705630391091)
      ·
        refine ⟨101162498920447058445586637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67441665946964705630391091 101162498920447058445586637)
        ·
          refine ⟨37935937095167646917094989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101162498920447058445586637 37935937095167646917094989)
          ·
            refine ⟨14225976410687867593910621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37935937095167646917094989 14225976410687867593910621)
            ·
              refine ⟨5334741154007950347716483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14225976410687867593910621 5334741154007950347716483)
              ·
                refine ⟨8002111731011925521574725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334741154007950347716483 8002111731011925521574725)
                ·
                  refine ⟨1500395949564736035295261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8002111731011925521574725 1500395949564736035295261)
                  ·
                    refine ⟨562648481086776013235723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500395949564736035295261 562648481086776013235723)
                    ·
                      rfl

theorem cell22_1643631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_1643631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643631 prefixEnd_1643631 := by exact prefixLift 1643631
  have htrace : WordTrace (prefixWord ++ tailWord_1643631) baseStart_1643631 baseEnd_1643631 := by
    simpa [prefixWord, tailWord_1643631, baseEnd_1643631] using wordTrace_append hprefix tailTrace_1643631
  have hstable : (prefixWord ++ tailWord_1643631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643631).length < 2 ^ (prefixWord ++ tailWord_1643631).sum := by decide
  have hdescent : baseEnd_1643631 < baseStart_1643631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643644 : List Nat := [2, 2, 2, 1, 1, 3, 2, 9]
def baseStart_1643644 : Nat := 118140960795 + 1643644 * 2 ^ 59
def prefixEnd_1643644 : Nat := 4983230072969 + 3 ^ 40 * 1643644 * 2
def baseEnd_1643644 : Nat := 62516992361383145851187

theorem tailTrace_1643644 : CollatzResearch.WordTrace tailWord_1643644 prefixEnd_1643644 62516992361383145851187 := by
  unfold tailWord_1643644
  simp only [CollatzResearch.WordTrace]
  refine ⟨29974310828682987445840993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39965747771577316594454657 29974310828682987445840993)
  ·
    refine ⟨22480733121512240584380745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29974310828682987445840993 22480733121512240584380745)
    ·
      refine ⟨16860549841134180438285559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22480733121512240584380745 16860549841134180438285559)
      ·
        refine ⟨25290824761701270657428339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16860549841134180438285559 25290824761701270657428339)
        ·
          refine ⟨37936237142551905986142509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25290824761701270657428339 37936237142551905986142509)
          ·
            refine ⟨14226088928456964744803441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37936237142551905986142509 14226088928456964744803441)
            ·
              refine ⟨10669566696342723558602581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14226088928456964744803441 10669566696342723558602581)
              ·
                refine ⟨62516992361383145851187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10669566696342723558602581 62516992361383145851187)
                ·
                  rfl

theorem cell22_1643644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_1643644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643644 prefixEnd_1643644 := by exact prefixLift 1643644
  have htrace : WordTrace (prefixWord ++ tailWord_1643644) baseStart_1643644 baseEnd_1643644 := by
    simpa [prefixWord, tailWord_1643644, baseEnd_1643644] using wordTrace_append hprefix tailTrace_1643644
  have hstable : (prefixWord ++ tailWord_1643644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643644).length < 2 ^ (prefixWord ++ tailWord_1643644).sum := by decide
  have hdescent : baseEnd_1643644 < baseStart_1643644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643678 : List Nat := [4, 3, 1, 1, 2, 3, 8]
def baseStart_1643678 : Nat := 118140960795 + 1643678 * 2 ^ 59
def prefixEnd_1643678 : Nat := 4983230072969 + 3 ^ 40 * 1643678 * 2
def baseEnd_1643678 : Nat := 20839428523973465085577

theorem tailTrace_1643678 : CollatzResearch.WordTrace tailWord_1643678 prefixEnd_1643678 20839428523973465085577 := by
  unfold tailWord_1643678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493732717405349837302461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39966574492828532465613125 7493732717405349837302461)
  ·
    refine ⟨2810149769027006188988423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7493732717405349837302461 2810149769027006188988423)
    ·
      refine ⟨4215224653540509283482635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810149769027006188988423 4215224653540509283482635)
      ·
        refine ⟨6322836980310763925223953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215224653540509283482635 6322836980310763925223953)
        ·
          refine ⟨4742127735233072943917965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6322836980310763925223953 4742127735233072943917965)
          ·
            refine ⟨1778297900712402353969237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4742127735233072943917965 1778297900712402353969237)
            ·
              refine ⟨20839428523973465085577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1778297900712402353969237 20839428523973465085577)
              ·
                rfl

theorem cell22_1643678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 8].length) (baseStart_1643678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643678 prefixEnd_1643678 := by exact prefixLift 1643678
  have htrace : WordTrace (prefixWord ++ tailWord_1643678) baseStart_1643678 baseEnd_1643678 := by
    simpa [prefixWord, tailWord_1643678, baseEnd_1643678] using wordTrace_append hprefix tailTrace_1643678
  have hstable : (prefixWord ++ tailWord_1643678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643678).length < 2 ^ (prefixWord ++ tailWord_1643678).sum := by decide
  have hdescent : baseEnd_1643678 < baseStart_1643678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643781 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_1643781 : Nat := 118140960795 + 1643781 * 2 ^ 59
def prefixEnd_1643781 : Nat := 4983230072969 + 3 ^ 40 * 1643781 * 2
def baseEnd_1643781 : Nat := 562699829152225621985263

theorem tailTrace_1643781 : CollatzResearch.WordTrace tailWord_1643781 prefixEnd_1643781 562699829152225621985263 := by
  unfold tailWord_1643781
  simp only [CollatzResearch.WordTrace]
  refine ⟨59953618457869647289419197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39969078971913098192946131 59953618457869647289419197)
  ·
    refine ⟨22482606921701117733532199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59953618457869647289419197 22482606921701117733532199)
    ·
      refine ⟨33723910382551676600298299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22482606921701117733532199 33723910382551676600298299)
      ·
        refine ⟨50585865573827514900447449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33723910382551676600298299 50585865573827514900447449)
        ·
          refine ⟨37939399180370636175335587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50585865573827514900447449 37939399180370636175335587)
          ·
            refine ⟨56909098770555954263003381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37939399180370636175335587 56909098770555954263003381)
            ·
              refine ⟨5335228009739620712156567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56909098770555954263003381 5335228009739620712156567)
              ·
                refine ⟨8002842014609431068234851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335228009739620712156567 8002842014609431068234851)
                ·
                  refine ⟨12004263021914146602352277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002842014609431068234851 12004263021914146602352277)
                  ·
                    refine ⟨562699829152225621985263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12004263021914146602352277 562699829152225621985263)
                    ·
                      rfl

theorem cell22_1643781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_1643781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643781 prefixEnd_1643781 := by exact prefixLift 1643781
  have htrace : WordTrace (prefixWord ++ tailWord_1643781) baseStart_1643781 baseEnd_1643781 := by
    simpa [prefixWord, tailWord_1643781, baseEnd_1643781] using wordTrace_append hprefix tailTrace_1643781
  have hstable : (prefixWord ++ tailWord_1643781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643781).length < 2 ^ (prefixWord ++ tailWord_1643781).sum := by decide
  have hdescent : baseEnd_1643781 < baseStart_1643781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643800 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_1643800 : Nat := 118140960795 + 1643800 * 2 ^ 59
def prefixEnd_1643800 : Nat := 4983230072969 + 3 ^ 40 * 1643800 * 2
def baseEnd_1643800 : Nat := 562706333240515905760205

theorem tailTrace_1643800 : CollatzResearch.WordTrace tailWord_1643800 prefixEnd_1643800 562706333240515905760205 := by
  unfold tailWord_1643800
  simp only [CollatzResearch.WordTrace]
  refine ⟨29977155722400406767180427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39969540963200542356240569 29977155722400406767180427)
  ·
    refine ⟨44965733583600610150770641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29977155722400406767180427 44965733583600610150770641)
    ·
      refine ⟨33724300187700457613077981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44965733583600610150770641 33724300187700457613077981)
      ·
        refine ⟨12646612570387671604904243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33724300187700457613077981 12646612570387671604904243)
        ·
          refine ⟨18969918855581507407356365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646612570387671604904243 18969918855581507407356365)
          ·
            refine ⟨7113719570843065277758637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18969918855581507407356365 7113719570843065277758637)
            ·
              refine ⟨2667644839066149479159489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7113719570843065277758637 2667644839066149479159489)
              ·
                refine ⟨2000733629299612109369617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2667644839066149479159489 2000733629299612109369617)
                ·
                  refine ⟨1500550221974709082027213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2000733629299612109369617 1500550221974709082027213)
                  ·
                    refine ⟨562706333240515905760205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500550221974709082027213 562706333240515905760205)
                    ·
                      rfl

theorem cell22_1643800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_1643800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643800 prefixEnd_1643800 := by exact prefixLift 1643800
  have htrace : WordTrace (prefixWord ++ tailWord_1643800) baseStart_1643800 baseEnd_1643800 := by
    simpa [prefixWord, tailWord_1643800, baseEnd_1643800] using wordTrace_append hprefix tailTrace_1643800
  have hstable : (prefixWord ++ tailWord_1643800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643800).length < 2 ^ (prefixWord ++ tailWord_1643800).sum := by decide
  have hdescent : baseEnd_1643800 < baseStart_1643800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643828 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1643828 : Nat := 118140960795 + 1643828 * 2 ^ 59
def prefixEnd_1643828 : Nat := 4983230072969 + 3 ^ 40 * 1643828 * 2
def baseEnd_1643828 : Nat := 562715918212733166060119

theorem tailTrace_1643828 : CollatzResearch.WordTrace tailWord_1643828 prefixEnd_1643828 562715918212733166060119 := by
  unfold tailWord_1643828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29977666344349687158190069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39970221792466249544253425 29977666344349687158190069)
  ·
    refine ⟨2810406219782783171080319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29977666344349687158190069 2810406219782783171080319)
    ·
      refine ⟨4215609329674174756620479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810406219782783171080319 4215609329674174756620479)
      ·
        refine ⟨6323413994511262134930719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215609329674174756620479 6323413994511262134930719)
        ·
          refine ⟨9485120991766893202396079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323413994511262134930719 9485120991766893202396079)
          ·
            refine ⟨14227681487650339803594119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485120991766893202396079 14227681487650339803594119)
            ·
              refine ⟨21341522231475509705391179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14227681487650339803594119 21341522231475509705391179)
              ·
                refine ⟨32012283347213264558086769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21341522231475509705391179 32012283347213264558086769)
                ·
                  refine ⟨24009212510409948418565077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32012283347213264558086769 24009212510409948418565077)
                  ·
                    refine ⟨562715918212733166060119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24009212510409948418565077 562715918212733166060119)
                    ·
                      rfl

theorem cell22_1643828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1643828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643828 prefixEnd_1643828 := by exact prefixLift 1643828
  have htrace : WordTrace (prefixWord ++ tailWord_1643828) baseStart_1643828 baseEnd_1643828 := by
    simpa [prefixWord, tailWord_1643828, baseEnd_1643828] using wordTrace_append hprefix tailTrace_1643828
  have hstable : (prefixWord ++ tailWord_1643828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643828).length < 2 ^ (prefixWord ++ tailWord_1643828).sum := by decide
  have hdescent : baseEnd_1643828 < baseStart_1643828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643858 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1643858 : Nat := 118140960795 + 1643858 * 2 ^ 59
def prefixEnd_1643858 : Nat := 4983230072969 + 3 ^ 40 * 1643858 * 2
def baseEnd_1643858 : Nat := 187575395941941029270009

theorem tailTrace_1643858 : CollatzResearch.WordTrace tailWord_1643858 prefixEnd_1643858 187575395941941029270009 := by
  unfold tailWord_1643858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14989106719647672359993057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39970951252393792959981485 14989106719647672359993057)
  ·
    refine ⟨11241830039735754269994793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14989106719647672359993057 11241830039735754269994793)
    ·
      refine ⟨8431372529801815702496095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11241830039735754269994793 8431372529801815702496095)
      ·
        refine ⟨12647058794702723553744143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431372529801815702496095 12647058794702723553744143)
        ·
          refine ⟨18970588192054085330616215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647058794702723553744143 18970588192054085330616215)
          ·
            refine ⟨28455882288081127995924323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18970588192054085330616215 28455882288081127995924323)
            ·
              refine ⟨42683823432121691993886485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28455882288081127995924323 42683823432121691993886485)
              ·
                refine ⟨2000804223380704312213429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42683823432121691993886485 2000804223380704312213429)
                ·
                  refine ⟨187575395941941029270009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2000804223380704312213429 187575395941941029270009)
                  ·
                    rfl

theorem cell22_1643858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1643858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643858 prefixEnd_1643858 := by exact prefixLift 1643858
  have htrace : WordTrace (prefixWord ++ tailWord_1643858) baseStart_1643858 baseEnd_1643858 := by
    simpa [prefixWord, tailWord_1643858, baseEnd_1643858] using wordTrace_append hprefix tailTrace_1643858
  have hstable : (prefixWord ++ tailWord_1643858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643858).length < 2 ^ (prefixWord ++ tailWord_1643858).sum := by decide
  have hdescent : baseEnd_1643858 < baseStart_1643858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643871 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1643871 : Nat := 118140960795 + 1643871 * 2 ^ 59
def prefixEnd_1643871 : Nat := 4983230072969 + 3 ^ 40 * 1643871 * 2
def baseEnd_1643871 : Nat := 562730637991495387234987

theorem tailTrace_1643871 : CollatzResearch.WordTrace tailWord_1643871 prefixEnd_1643871 562730637991495387234987 := by
  unfold tailWord_1643871
  simp only [CollatzResearch.WordTrace]
  refine ⟨59956901027543592660195467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39971267351695728440130311 59956901027543592660195467)
  ·
    refine ⟨89935351541315388990293201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59956901027543592660195467 89935351541315388990293201)
    ·
      refine ⟨67451513655986541742719901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89935351541315388990293201 67451513655986541742719901)
      ·
        refine ⟨25294317620994953153519963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67451513655986541742719901 25294317620994953153519963)
        ·
          refine ⟨37941476431492429730279945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25294317620994953153519963 37941476431492429730279945)
          ·
            refine ⟨28456107323619322297709959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37941476431492429730279945 28456107323619322297709959)
            ·
              refine ⟨42684160985428983446564939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28456107323619322297709959 42684160985428983446564939)
              ·
                refine ⟨64026241478143475169847409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42684160985428983446564939 64026241478143475169847409)
                ·
                  refine ⟨48019681108607606377385557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64026241478143475169847409 48019681108607606377385557)
                  ·
                    refine ⟨562730637991495387234987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48019681108607606377385557 562730637991495387234987)
                    ·
                      rfl

theorem cell22_1643871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1643871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643871 prefixEnd_1643871 := by exact prefixLift 1643871
  have htrace : WordTrace (prefixWord ++ tailWord_1643871) baseStart_1643871 baseEnd_1643871 := by
    simpa [prefixWord, tailWord_1643871, baseEnd_1643871] using wordTrace_append hprefix tailTrace_1643871
  have hstable : (prefixWord ++ tailWord_1643871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643871).length < 2 ^ (prefixWord ++ tailWord_1643871).sum := by decide
  have hdescent : baseEnd_1643871 < baseStart_1643871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643875 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 5]
def baseStart_1643875 : Nat := 118140960795 + 1643875 * 2 ^ 59
def prefixEnd_1643875 : Nat := 4983230072969 + 3 ^ 40 * 1643875 * 2
def baseEnd_1643875 : Nat := 187577335757746903378325

theorem tailTrace_1643875 : CollatzResearch.WordTrace tailWord_1643875 prefixEnd_1643875 187577335757746903378325 := by
  unfold tailWord_1643875
  simp only [CollatzResearch.WordTrace]
  refine ⟨59957046919529101343341079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39971364613019400895560719 59957046919529101343341079)
  ·
    refine ⟨89935570379293652015011619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59957046919529101343341079 89935570379293652015011619)
    ·
      refine ⟨134903355568940478022517429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89935570379293652015011619 134903355568940478022517429)
      ·
        refine ⟨12647189584588169814611009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134903355568940478022517429 12647189584588169814611009)
        ·
          refine ⟨9485392188441127360958257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12647189584588169814611009 9485392188441127360958257)
          ·
            refine ⟨7114044141330845520718693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9485392188441127360958257 7114044141330845520718693)
            ·
              refine ⟨1333883276499533535134755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7114044141330845520718693 1333883276499533535134755)
              ·
                refine ⟨2000824914749300302702133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333883276499533535134755 2000824914749300302702133)
                ·
                  refine ⟨187577335757746903378325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2000824914749300302702133 187577335757746903378325)
                  ·
                    rfl

theorem cell22_1643875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 5].length) (baseStart_1643875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643875 prefixEnd_1643875 := by exact prefixLift 1643875
  have htrace : WordTrace (prefixWord ++ tailWord_1643875) baseStart_1643875 baseEnd_1643875 := by
    simpa [prefixWord, tailWord_1643875, baseEnd_1643875] using wordTrace_append hprefix tailTrace_1643875
  have hstable : (prefixWord ++ tailWord_1643875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643875).length < 2 ^ (prefixWord ++ tailWord_1643875).sum := by decide
  have hdescent : baseEnd_1643875 < baseStart_1643875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643888 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_1643888 : Nat := 118140960795 + 1643888 * 2 ^ 59
def prefixEnd_1643888 : Nat := 4983230072969 + 3 ^ 40 * 1643888 * 2
def baseEnd_1643888 : Nat := 562736457438913009559935

theorem tailTrace_1643888 : CollatzResearch.WordTrace tailWord_1643888 prefixEnd_1643888 562736457438913009559935 := by
  unfold tailWord_1643888
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978760534241002281782159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39971680712321336375709545 29978760534241002281782159)
  ·
    refine ⟨44968140801361503422673239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29978760534241002281782159 44968140801361503422673239)
    ·
      refine ⟨67452211202042255134009859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44968140801361503422673239 67452211202042255134009859)
      ·
        refine ⟨101178316803063382701014789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67452211202042255134009859 101178316803063382701014789)
        ·
          refine ⟨18970934400574384256440273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101178316803063382701014789 18970934400574384256440273)
          ·
            refine ⟨14228200800430788192330205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18970934400574384256440273 14228200800430788192330205)
            ·
              refine ⟨5335575300161545572123827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14228200800430788192330205 5335575300161545572123827)
              ·
                refine ⟨8003362950242318358185741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335575300161545572123827 8003362950242318358185741)
                ·
                  refine ⟨3001261106340869384319653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8003362950242318358185741 3001261106340869384319653)
                  ·
                    refine ⟨562736457438913009559935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001261106340869384319653 562736457438913009559935)
                    ·
                      rfl

theorem cell22_1643888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_1643888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643888 prefixEnd_1643888 := by exact prefixLift 1643888
  have htrace : WordTrace (prefixWord ++ tailWord_1643888) baseStart_1643888 baseEnd_1643888 := by
    simpa [prefixWord, tailWord_1643888, baseEnd_1643888] using wordTrace_append hprefix tailTrace_1643888
  have hstable : (prefixWord ++ tailWord_1643888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643888).length < 2 ^ (prefixWord ++ tailWord_1643888).sum := by decide
  have hdescent : baseEnd_1643888 < baseStart_1643888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643935 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 1, 5]
def baseStart_1643935 : Nat := 118140960795 + 1643935 * 2 ^ 59
def prefixEnd_1643935 : Nat := 4983230072969 + 3 ^ 40 * 1643935 * 2
def baseEnd_1643935 : Nat := 562752546499420553634791

theorem tailTrace_1643935 : CollatzResearch.WordTrace tailWord_1643935 prefixEnd_1643935 562752546499420553634791 := by
  unfold tailWord_1643935
  simp only [CollatzResearch.WordTrace]
  refine ⟨59959235299311731590525259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39972823532874487727016839 59959235299311731590525259)
  ·
    refine ⟨89938852948967597385787889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59959235299311731590525259 89938852948967597385787889)
    ·
      refine ⟨67454139711725698039340917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89938852948967597385787889 67454139711725698039340917)
      ·
        refine ⟨6323825597974284191188211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67454139711725698039340917 6323825597974284191188211)
        ·
          refine ⟨9485738396961426286782317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323825597974284191188211 9485738396961426286782317)
          ·
            refine ⟨3557151898860534857543369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9485738396961426286782317 3557151898860534857543369)
            ·
              refine ⟨2667863924145401143157527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557151898860534857543369 2667863924145401143157527)
              ·
                refine ⟨4001795886218101714736291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667863924145401143157527 4001795886218101714736291)
                ·
                  refine ⟨6002693829327152572104437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001795886218101714736291 6002693829327152572104437)
                  ·
                    refine ⟨562752546499420553634791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6002693829327152572104437 562752546499420553634791)
                    ·
                      rfl

theorem cell22_1643935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_1643935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643935 prefixEnd_1643935 := by exact prefixLift 1643935
  have htrace : WordTrace (prefixWord ++ tailWord_1643935) baseStart_1643935 baseEnd_1643935 := by
    simpa [prefixWord, tailWord_1643935, baseEnd_1643935] using wordTrace_append hprefix tailTrace_1643935
  have hstable : (prefixWord ++ tailWord_1643935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643935).length < 2 ^ (prefixWord ++ tailWord_1643935).sum := by decide
  have hdescent : baseEnd_1643935 < baseStart_1643935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643997 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1643997 : Nat := 118140960795 + 1643997 * 2 ^ 59
def prefixEnd_1643997 : Nat := 4983230072969 + 3 ^ 40 * 1643997 * 2
def baseEnd_1643997 : Nat := 562773770366473058584601

theorem tailTrace_1643997 : CollatzResearch.WordTrace tailWord_1643997 prefixEnd_1643997 562773770366473058584601 := by
  unfold tailWord_1643997
  simp only [CollatzResearch.WordTrace]
  refine ⟨59961496625087116179282245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39974331083391410786188163 59961496625087116179282245)
  ·
    refine ⟨11242780617203834283615421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59961496625087116179282245 11242780617203834283615421)
    ·
      refine ⟨4216042731451437856355783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11242780617203834283615421 4216042731451437856355783)
      ·
        refine ⟨6324064097177156784533675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216042731451437856355783 6324064097177156784533675)
        ·
          refine ⟨9486096145765735176800513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324064097177156784533675 9486096145765735176800513)
          ·
            refine ⟨7114572109324301382600385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9486096145765735176800513 7114572109324301382600385)
            ·
              refine ⟨5335929081993226036950289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114572109324301382600385 5335929081993226036950289)
              ·
                refine ⟨4001946811494919527712717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335929081993226036950289 4001946811494919527712717)
                ·
                  refine ⟨1500730054310594822892269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4001946811494919527712717 1500730054310594822892269)
                  ·
                    refine ⟨562773770366473058584601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500730054310594822892269 562773770366473058584601)
                    ·
                      rfl

theorem cell22_1643997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1643997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1643997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1643997 prefixEnd_1643997 := by exact prefixLift 1643997
  have htrace : WordTrace (prefixWord ++ tailWord_1643997) baseStart_1643997 baseEnd_1643997 := by
    simpa [prefixWord, tailWord_1643997, baseEnd_1643997] using wordTrace_append hprefix tailTrace_1643997
  have hstable : (prefixWord ++ tailWord_1643997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643997).length < 2 ^ (prefixWord ++ tailWord_1643997).sum := by decide
  have hdescent : baseEnd_1643997 < baseStart_1643997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644044 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1644044 : Nat := 118140960795 + 1644044 * 2 ^ 59
def prefixEnd_1644044 : Nat := 4983230072969 + 3 ^ 40 * 1644044 * 2
def baseEnd_1644044 : Nat := 187596619808993534219819

theorem tailTrace_1644044 : CollatzResearch.WordTrace tailWord_1644044 prefixEnd_1644044 187596619808993534219819 := by
  unfold tailWord_1644044
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981605427958421603121593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39975473903944562137495457 29981605427958421603121593)
  ·
    refine ⟨22486204070968816202341195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29981605427958421603121593 22486204070968816202341195)
    ·
      refine ⟨33729306106453224303511793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22486204070968816202341195 33729306106453224303511793)
      ·
        refine ⟨25296979579839918227633845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33729306106453224303511793 25296979579839918227633845)
        ·
          refine ⟨2371591835609992333840673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25296979579839918227633845 2371591835609992333840673)
          ·
            refine ⟨1778693876707494250380505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371591835609992333840673 1778693876707494250380505)
            ·
              refine ⟨1334020407530620687785379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778693876707494250380505 1334020407530620687785379)
              ·
                refine ⟨2001030611295931031678069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334020407530620687785379 2001030611295931031678069)
                ·
                  refine ⟨187596619808993534219819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2001030611295931031678069 187596619808993534219819)
                  ·
                    rfl

theorem cell22_1644044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1644044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644044 prefixEnd_1644044 := by exact prefixLift 1644044
  have htrace : WordTrace (prefixWord ++ tailWord_1644044) baseStart_1644044 baseEnd_1644044 := by
    simpa [prefixWord, tailWord_1644044, baseEnd_1644044] using wordTrace_append hprefix tailTrace_1644044
  have hstable : (prefixWord ++ tailWord_1644044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644044).length < 2 ^ (prefixWord ++ tailWord_1644044).sum := by decide
  have hdescent : baseEnd_1644044 < baseStart_1644044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644074 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1644074 : Nat := 118140960795 + 1644074 * 2 ^ 59
def prefixEnd_1644074 : Nat := 4983230072969 + 3 ^ 40 * 1644074 * 2
def baseEnd_1644074 : Nat := 562800129040070524409365

theorem tailTrace_1644074 : CollatzResearch.WordTrace tailWord_1644074 prefixEnd_1644074 562800129040070524409365 := by
  unfold tailWord_1644074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14991076261452039582458819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39976203363872105553223517 14991076261452039582458819)
  ·
    refine ⟨22486614392178059373688229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14991076261452039582458819 22486614392178059373688229)
    ·
      refine ⟨4216240198533386132566543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22486614392178059373688229 4216240198533386132566543)
      ·
        refine ⟨6324360297800079198849815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216240198533386132566543 6324360297800079198849815)
        ·
          refine ⟨9486540446700118798274723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324360297800079198849815 9486540446700118798274723)
          ·
            refine ⟨14229810670050178197412085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486540446700118798274723 14229810670050178197412085)
            ·
              refine ⟨1334044750317204206007383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14229810670050178197412085 1334044750317204206007383)
              ·
                refine ⟨2001067125475806309011075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334044750317204206007383 2001067125475806309011075)
                ·
                  refine ⟨3001600688213709463516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001067125475806309011075 3001600688213709463516613)
                  ·
                    refine ⟨562800129040070524409365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001600688213709463516613 562800129040070524409365)
                    ·
                      rfl

theorem cell22_1644074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1644074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644074 prefixEnd_1644074 := by exact prefixLift 1644074
  have htrace : WordTrace (prefixWord ++ tailWord_1644074) baseStart_1644074 baseEnd_1644074 := by
    simpa [prefixWord, tailWord_1644074, baseEnd_1644074] using wordTrace_append hprefix tailTrace_1644074
  have hstable : (prefixWord ++ tailWord_1644074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644074).length < 2 ^ (prefixWord ++ tailWord_1644074).sum := by decide
  have hdescent : baseEnd_1644074 < baseStart_1644074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644083 : List Nat := [1, 1, 1, 2, 4, 13]
def baseStart_1644083 : Nat := 118140960795 + 1644083 * 2 ^ 59
def prefixEnd_1644083 : Nat := 4983230072969 + 3 ^ 40 * 1644083 * 2
def baseEnd_1644083 : Nat := 6948187776839475320177

theorem tailTrace_1644083 : CollatzResearch.WordTrace tailWord_1644083 prefixEnd_1644083 6948187776839475320177 := by
  unfold tailWord_1644083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59964633302775552866912903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39976422201850368577941935 59964633302775552866912903)
  ·
    refine ⟨89946949954163329300369355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59964633302775552866912903 89946949954163329300369355)
    ·
      refine ⟨134920424931244993950554033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89946949954163329300369355 134920424931244993950554033)
      ·
        refine ⟨101190318698433745462915525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134920424931244993950554033 101190318698433745462915525)
        ·
          refine ⟨18973184755956327274296661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101190318698433745462915525 18973184755956327274296661)
          ·
            refine ⟨6948187776839475320177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 18973184755956327274296661 6948187776839475320177)
            ·
              rfl

theorem cell22_1644083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 13].length) (baseStart_1644083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644083 prefixEnd_1644083 := by exact prefixLift 1644083
  have htrace : WordTrace (prefixWord ++ tailWord_1644083) baseStart_1644083 baseEnd_1644083 := by
    simpa [prefixWord, tailWord_1644083, baseEnd_1644083] using wordTrace_append hprefix tailTrace_1644083
  have hstable : (prefixWord ++ tailWord_1644083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644083).length < 2 ^ (prefixWord ++ tailWord_1644083).sum := by decide
  have hdescent : baseEnd_1644083 < baseStart_1644083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644087 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 2, 3]
def baseStart_1644087 : Nat := 118140960795 + 1644087 * 2 ^ 59
def prefixEnd_1644087 : Nat := 4983230072969 + 3 ^ 40 * 1644087 * 2
def baseEnd_1644087 : Nat := 562804579205742823834325

theorem tailTrace_1644087 : CollatzResearch.WordTrace tailWord_1644087 prefixEnd_1644087 562804579205742823834325 := by
  unfold tailWord_1644087
  simp only [CollatzResearch.WordTrace]
  refine ⟨59964779194761061550058515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39976519463174041033372343 59964779194761061550058515)
  ·
    refine ⟨89947168792141592325087773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59964779194761061550058515 89947168792141592325087773)
    ·
      refine ⟨33730188297053097121907915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89947168792141592325087773 33730188297053097121907915)
      ·
        refine ⟨50595282445579645682861873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33730188297053097121907915 50595282445579645682861873)
        ·
          refine ⟨37946461834184734262146405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50595282445579645682861873 37946461834184734262146405)
          ·
            refine ⟨7114961593909637674152451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37946461834184734262146405 7114961593909637674152451)
            ·
              refine ⟨10672442390864456511228677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7114961593909637674152451 10672442390864456511228677)
              ·
                refine ⟨2001082948287085595855377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10672442390864456511228677 2001082948287085595855377)
                ·
                  refine ⟨1500812211215314196891533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001082948287085595855377 1500812211215314196891533)
                  ·
                    refine ⟨562804579205742823834325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500812211215314196891533 562804579205742823834325)
                    ·
                      rfl

theorem cell22_1644087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_1644087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644087 prefixEnd_1644087 := by exact prefixLift 1644087
  have htrace : WordTrace (prefixWord ++ tailWord_1644087) baseStart_1644087 baseEnd_1644087 := by
    simpa [prefixWord, tailWord_1644087, baseEnd_1644087] using wordTrace_append hprefix tailTrace_1644087
  have hstable : (prefixWord ++ tailWord_1644087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644087).length < 2 ^ (prefixWord ++ tailWord_1644087).sum := by decide
  have hdescent : baseEnd_1644087 < baseStart_1644087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644089 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 4]
def baseStart_1644089 : Nat := 118140960795 + 1644089 * 2 ^ 59
def prefixEnd_1644089 : Nat := 4983230072969 + 3 ^ 40 * 1644089 * 2
def baseEnd_1644089 : Nat := 187601754615538495094773

theorem tailTrace_1644089 : CollatzResearch.WordTrace tailWord_1644089 prefixEnd_1644089 187601754615538495094773 := by
  unfold tailWord_1644089
  simp only [CollatzResearch.WordTrace]
  refine ⟨59964852140753815891631321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39976568093835877261087547 59964852140753815891631321)
  ·
    refine ⟨44973639105565361918723491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59964852140753815891631321 44973639105565361918723491)
    ·
      refine ⟨67460458658348042878085237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44973639105565361918723491 67460458658348042878085237)
      ·
        refine ⟨6324417999220129019820491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67460458658348042878085237 6324417999220129019820491)
        ·
          refine ⟨9486626998830193529730737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324417999220129019820491 9486626998830193529730737)
          ·
            refine ⟨7114970249122645147298053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9486626998830193529730737 7114970249122645147298053)
            ·
              refine ⟨1334056921710495965118385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7114970249122645147298053 1334056921710495965118385)
              ·
                refine ⟨1000542691282871973838789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334056921710495965118385 1000542691282871973838789)
                ·
                  refine ⟨187601754615538495094773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000542691282871973838789 187601754615538495094773)
                  ·
                    rfl

theorem cell22_1644089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_1644089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644089 prefixEnd_1644089 := by exact prefixLift 1644089
  have htrace : WordTrace (prefixWord ++ tailWord_1644089) baseStart_1644089 baseEnd_1644089 := by
    simpa [prefixWord, tailWord_1644089, baseEnd_1644089] using wordTrace_append hprefix tailTrace_1644089
  have hstable : (prefixWord ++ tailWord_1644089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644089).length < 2 ^ (prefixWord ++ tailWord_1644089).sum := by decide
  have hdescent : baseEnd_1644089 < baseStart_1644089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644125 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1644125 : Nat := 118140960795 + 1644125 * 2 ^ 59
def prefixEnd_1644125 : Nat := 4983230072969 + 3 ^ 40 * 1644125 * 2
def baseEnd_1644125 : Nat := 562817587382323391384209

theorem tailTrace_1644125 : CollatzResearch.WordTrace tailWord_1644125 prefixEnd_1644125 562817587382323391384209 := by
  unfold tailWord_1644125
  simp only [CollatzResearch.WordTrace]
  refine ⟨59966165168623394039941829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39977443445748929359961219 59966165168623394039941829)
  ·
    refine ⟨11243655969116886382489093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59966165168623394039941829 11243655969116886382489093)
    ·
      refine ⟨2108185494209416196716705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11243655969116886382489093 2108185494209416196716705)
      ·
        refine ⟨1581139120657062147537529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108185494209416196716705 1581139120657062147537529)
        ·
          refine ⟨1185854340492796610653147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581139120657062147537529 1185854340492796610653147)
          ·
            refine ⟨1778781510739194915979721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185854340492796610653147 1778781510739194915979721)
            ·
              refine ⟨1334086133054396186984791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778781510739194915979721 1334086133054396186984791)
              ·
                refine ⟨2001129199581594280477187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334086133054396186984791 2001129199581594280477187)
                ·
                  refine ⟨3001693799372391420715781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001129199581594280477187 3001693799372391420715781)
                  ·
                    refine ⟨562817587382323391384209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3001693799372391420715781 562817587382323391384209)
                    ·
                      rfl

theorem cell22_1644125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1644125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644125 prefixEnd_1644125 := by exact prefixLift 1644125
  have htrace : WordTrace (prefixWord ++ tailWord_1644125) baseStart_1644125 baseEnd_1644125 := by
    simpa [prefixWord, tailWord_1644125, baseEnd_1644125] using wordTrace_append hprefix tailTrace_1644125
  have hstable : (prefixWord ++ tailWord_1644125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644125).length < 2 ^ (prefixWord ++ tailWord_1644125).sum := by decide
  have hdescent : baseEnd_1644125 < baseStart_1644125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644149 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1644149 : Nat := 118140960795 + 1644149 * 2 ^ 59
def prefixEnd_1644149 : Nat := 4983230072969 + 3 ^ 40 * 1644149 * 2
def baseEnd_1644149 : Nat := 562825803072795328784135

theorem tailTrace_1644149 : CollatzResearch.WordTrace tailWord_1644149 prefixEnd_1644149 562825803072795328784135 := by
  unfold tailWord_1644149
  simp only [CollatzResearch.WordTrace]
  refine ⟨59967040520536446138815501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39978027013690964092543667 59967040520536446138815501)
  ·
    refine ⟨22487640195201167302055813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59967040520536446138815501 22487640195201167302055813)
    ·
      refine ⟨4216432536600218869135465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22487640195201167302055813 4216432536600218869135465)
      ·
        refine ⟨3162324402450164151851599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4216432536600218869135465 3162324402450164151851599)
        ·
          refine ⟨4743486603675246227777399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162324402450164151851599 4743486603675246227777399)
          ·
            refine ⟨7115229905512869341666099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743486603675246227777399 7115229905512869341666099)
            ·
              refine ⟨10672844858269304012499149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115229905512869341666099 10672844858269304012499149)
              ·
                refine ⟨4002316821850989004687181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10672844858269304012499149 4002316821850989004687181)
                ·
                  refine ⟨1500868808194120876757693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4002316821850989004687181 1500868808194120876757693)
                  ·
                    refine ⟨562825803072795328784135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500868808194120876757693 562825803072795328784135)
                    ·
                      rfl

theorem cell22_1644149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1644149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644149 prefixEnd_1644149 := by exact prefixLift 1644149
  have htrace : WordTrace (prefixWord ++ tailWord_1644149) baseStart_1644149 baseEnd_1644149 := by
    simpa [prefixWord, tailWord_1644149, baseEnd_1644149] using wordTrace_append hprefix tailTrace_1644149
  have hstable : (prefixWord ++ tailWord_1644149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644149).length < 2 ^ (prefixWord ++ tailWord_1644149).sum := by decide
  have hdescent : baseEnd_1644149 < baseStart_1644149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644160 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_1644160 : Nat := 118140960795 + 1644160 * 2 ^ 59
def prefixEnd_1644160 : Nat := 4983230072969 + 3 ^ 40 * 1644160 * 2
def baseEnd_1644160 : Nat := 562829568597594966759101

theorem tailTrace_1644160 : CollatzResearch.WordTrace tailWord_1644160 prefixEnd_1644160 562829568597594966759101 := by
  unfold tailWord_1644160
  simp only [CollatzResearch.WordTrace]
  refine ⟨29983720861748297508732967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39978294482331063344977289 29983720861748297508732967)
  ·
    refine ⟨44975581292622446263099451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29983720861748297508732967 44975581292622446263099451)
    ·
      refine ⟨67463371938933669394649177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44975581292622446263099451 67463371938933669394649177)
      ·
        refine ⟨50597528954200252045986883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67463371938933669394649177 50597528954200252045986883)
        ·
          refine ⟨75896293431300378068980325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50597528954200252045986883 75896293431300378068980325)
          ·
            refine ⟨14230555018368820887933811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75896293431300378068980325 14230555018368820887933811)
            ·
              refine ⟨21345832527553231331900717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14230555018368820887933811 21345832527553231331900717)
              ·
                refine ⟨8004687197832461749462769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21345832527553231331900717 8004687197832461749462769)
                ·
                  refine ⟨6003515398374346312097077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8004687197832461749462769 6003515398374346312097077)
                  ·
                    refine ⟨562829568597594966759101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6003515398374346312097077 562829568597594966759101)
                    ·
                      rfl

theorem cell22_1644160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_1644160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644160 prefixEnd_1644160 := by exact prefixLift 1644160
  have htrace : WordTrace (prefixWord ++ tailWord_1644160) baseStart_1644160 baseEnd_1644160 := by
    simpa [prefixWord, tailWord_1644160, baseEnd_1644160] using wordTrace_append hprefix tailTrace_1644160
  have hstable : (prefixWord ++ tailWord_1644160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644160).length < 2 ^ (prefixWord ++ tailWord_1644160).sum := by decide
  have hdescent : baseEnd_1644160 < baseStart_1644160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644200 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1644200 : Nat := 118140960795 + 1644200 * 2 ^ 59
def prefixEnd_1644200 : Nat := 4983230072969 + 3 ^ 40 * 1644200 * 2
def baseEnd_1644200 : Nat := 562843261415048195758979

theorem tailTrace_1644200 : CollatzResearch.WordTrace tailWord_1644200 prefixEnd_1644200 562843261415048195758979 := by
  unfold tailWord_1644200
  simp only [CollatzResearch.WordTrace]
  refine ⟨29984450321675840924461027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39979267095567787899281369 29984450321675840924461027)
  ·
    refine ⟨44976675482513761386691541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29984450321675840924461027 44976675482513761386691541)
    ·
      refine ⟨1054140831621416282500583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44976675482513761386691541 1054140831621416282500583)
      ·
        refine ⟨1581211247432124423750875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054140831621416282500583 1581211247432124423750875)
        ·
          refine ⟨2371816871148186635626313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581211247432124423750875 2371816871148186635626313)
          ·
            refine ⟨1778862653361139976719735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371816871148186635626313 1778862653361139976719735)
            ·
              refine ⟨2668293980041709965079603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778862653361139976719735 2668293980041709965079603)
              ·
                refine ⟨4002440970062564947619405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668293980041709965079603 4002440970062564947619405)
                ·
                  refine ⟨1500915363773461855357277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4002440970062564947619405 1500915363773461855357277)
                  ·
                    refine ⟨562843261415048195758979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500915363773461855357277 562843261415048195758979)
                    ·
                      rfl

theorem cell22_1644200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1644200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644200 prefixEnd_1644200 := by exact prefixLift 1644200
  have htrace : WordTrace (prefixWord ++ tailWord_1644200) baseStart_1644200 baseEnd_1644200 := by
    simpa [prefixWord, tailWord_1644200, baseEnd_1644200] using wordTrace_append hprefix tailTrace_1644200
  have hstable : (prefixWord ++ tailWord_1644200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644200).length < 2 ^ (prefixWord ++ tailWord_1644200).sum := by decide
  have hdescent : baseEnd_1644200 < baseStart_1644200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644213 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 5]
def baseStart_1644213 : Nat := 118140960795 + 1644213 * 2 ^ 59
def prefixEnd_1644213 : Nat := 4983230072969 + 3 ^ 40 * 1644213 * 2
def baseEnd_1644213 : Nat := 187615903860240165061313

theorem tailTrace_1644213 : CollatzResearch.WordTrace tailWord_1644213 prefixEnd_1644213 187615903860240165061313 := by
  unfold tailWord_1644213
  simp only [CollatzResearch.WordTrace]
  refine ⟨59969374792304585069145293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39979583194869723379430195 59969374792304585069145293)
  ·
    refine ⟨22488515547114219400929485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59969374792304585069145293 22488515547114219400929485)
    ·
      refine ⟨8433193330167832275348557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22488515547114219400929485 8433193330167832275348557)
      ·
        refine ⟨3162447498812937103255709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8433193330167832275348557 3162447498812937103255709)
        ·
          refine ⟨1185917812054851413720891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3162447498812937103255709 1185917812054851413720891)
          ·
            refine ⟨1778876718082277120581337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185917812054851413720891 1778876718082277120581337)
            ·
              refine ⟨1334157538561707840436003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778876718082277120581337 1334157538561707840436003)
              ·
                refine ⟨2001236307842561760654005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334157538561707840436003 2001236307842561760654005)
                ·
                  refine ⟨187615903860240165061313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2001236307842561760654005 187615903860240165061313)
                  ·
                    rfl

theorem cell22_1644213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_1644213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644213 prefixEnd_1644213 := by exact prefixLift 1644213
  have htrace : WordTrace (prefixWord ++ tailWord_1644213) baseStart_1644213 baseEnd_1644213 := by
    simpa [prefixWord, tailWord_1644213, baseEnd_1644213] using wordTrace_append hprefix tailTrace_1644213
  have hstable : (prefixWord ++ tailWord_1644213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644213).length < 2 ^ (prefixWord ++ tailWord_1644213).sum := by decide
  have hdescent : baseEnd_1644213 < baseStart_1644213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644252 : List Nat := [2, 2, 5, 1, 12]
def baseStart_1644252 : Nat := 118140960795 + 1644252 * 2 ^ 59
def prefixEnd_1644252 : Nat := 4983230072969 + 3 ^ 40 * 1644252 * 2
def baseEnd_1644252 : Nat := 2316300666986573635633

theorem tailTrace_1644252 : CollatzResearch.WordTrace tailWord_1644252 prefixEnd_1644252 2316300666986573635633 := by
  unfold tailWord_1644252
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985398619581647364907505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39980531492775529819876673 29985398619581647364907505)
  ·
    refine ⟨22489048964686235523680629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29985398619581647364907505 22489048964686235523680629)
    ·
      refine ⟨2108348340439334580345059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22489048964686235523680629 2108348340439334580345059)
      ·
        refine ⟨3162522510659001870517589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108348340439334580345059 3162522510659001870517589)
        ·
          refine ⟨2316300666986573635633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3162522510659001870517589 2316300666986573635633)
          ·
            rfl

theorem cell22_1644252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 12].length) (baseStart_1644252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644252 prefixEnd_1644252 := by exact prefixLift 1644252
  have htrace : WordTrace (prefixWord ++ tailWord_1644252) baseStart_1644252 baseEnd_1644252 := by
    simpa [prefixWord, tailWord_1644252, baseEnd_1644252] using wordTrace_append hprefix tailTrace_1644252
  have hstable : (prefixWord ++ tailWord_1644252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644252).length < 2 ^ (prefixWord ++ tailWord_1644252).sum := by decide
  have hdescent : baseEnd_1644252 < baseStart_1644252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644269 : List Nat := [1, 5, 1, 2, 1, 4, 1, 7]
def baseStart_1644269 : Nat := 118140960795 + 1644269 * 2 ^ 59
def prefixEnd_1644269 : Nat := 4983230072969 + 3 ^ 40 * 1644269 * 2
def baseEnd_1644269 : Nat := 62540764613906112864863

theorem tailTrace_1644269 : CollatzResearch.WordTrace tailWord_1644269 prefixEnd_1644269 62540764613906112864863 := by
  unfold tailWord_1644269
  simp only [CollatzResearch.WordTrace]
  refine ⟨59971417280101706633183861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39980944853401137755455907 59971417280101706633183861)
  ·
    refine ⟨5622320370009534996860987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59971417280101706633183861 5622320370009534996860987)
    ·
      refine ⟨8433480555014302495291481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622320370009534996860987 8433480555014302495291481)
      ·
        refine ⟨6325110416260726871468611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8433480555014302495291481 6325110416260726871468611)
        ·
          refine ⟨9487665624391090307202917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6325110416260726871468611 9487665624391090307202917)
          ·
            refine ⟨1778937304573329432600547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9487665624391090307202917 1778937304573329432600547)
            ·
              refine ⟨2668405956859994148900821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778937304573329432600547 2668405956859994148900821)
              ·
                refine ⟨62540764613906112864863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2668405956859994148900821 62540764613906112864863)
                ·
                  rfl

theorem cell22_1644269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 7].length) (baseStart_1644269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644269 prefixEnd_1644269 := by exact prefixLift 1644269
  have htrace : WordTrace (prefixWord ++ tailWord_1644269) baseStart_1644269 baseEnd_1644269 := by
    simpa [prefixWord, tailWord_1644269, baseEnd_1644269] using wordTrace_append hprefix tailTrace_1644269
  have hstable : (prefixWord ++ tailWord_1644269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644269).length < 2 ^ (prefixWord ++ tailWord_1644269).sum := by decide
  have hdescent : baseEnd_1644269 < baseStart_1644269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644284 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_1644284 : Nat := 118140960795 + 1644284 * 2 ^ 59
def prefixEnd_1644284 : Nat := 4983230072969 + 3 ^ 40 * 1644284 * 2
def baseEnd_1644284 : Nat := 562872016331699976658721

theorem tailTrace_1644284 : CollatzResearch.WordTrace tailWord_1644284 prefixEnd_1644284 562872016331699976658721 := by
  unfold tailWord_1644284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985982187523682097489953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39981309583364909463319937 29985982187523682097489953)
  ·
    refine ⟨22489486640642761573117465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29985982187523682097489953 22489486640642761573117465)
    ·
      refine ⟨16867114980482071179838099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22489486640642761573117465 16867114980482071179838099)
      ·
        refine ⟨25300672470723106769757149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16867114980482071179838099 25300672470723106769757149)
        ·
          refine ⟨9487752176521165038658931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25300672470723106769757149 9487752176521165038658931)
          ·
            refine ⟨14231628264781747557988397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9487752176521165038658931 14231628264781747557988397)
            ·
              refine ⟨5336860599293155334245649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14231628264781747557988397 5336860599293155334245649)
              ·
                refine ⟨4002645449469866500684237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336860599293155334245649 4002645449469866500684237)
                ·
                  refine ⟨1500992043551199937756589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4002645449469866500684237 1500992043551199937756589)
                  ·
                    refine ⟨562872016331699976658721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500992043551199937756589 562872016331699976658721)
                    ·
                      rfl

theorem cell22_1644284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_1644284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644284 prefixEnd_1644284 := by exact prefixLift 1644284
  have htrace : WordTrace (prefixWord ++ tailWord_1644284) baseStart_1644284 baseEnd_1644284 := by
    simpa [prefixWord, tailWord_1644284, baseEnd_1644284] using wordTrace_append hprefix tailTrace_1644284
  have hstable : (prefixWord ++ tailWord_1644284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644284).length < 2 ^ (prefixWord ++ tailWord_1644284).sum := by decide
  have hdescent : baseEnd_1644284 < baseStart_1644284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644286 : List Nat := [4, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1644286 : Nat := 118140960795 + 1644286 * 2 ^ 59
def prefixEnd_1644286 : Nat := 4983230072969 + 3 ^ 40 * 1644286 * 2
def baseEnd_1644286 : Nat := 62541411219174737567635

theorem tailTrace_1644286 : CollatzResearch.WordTrace tailWord_1644286 prefixEnd_1644286 62541411219174737567635 := by
  unfold tailWord_1644286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7496504665130014817069089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39981358214026745691035141 7496504665130014817069089)
  ·
    refine ⟨5622378498847511112801817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7496504665130014817069089 5622378498847511112801817)
    ·
      refine ⟨4216783874135633334601363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5622378498847511112801817 4216783874135633334601363)
      ·
        refine ⟨6325175811203450001902045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216783874135633334601363 6325175811203450001902045)
        ·
          refine ⟨2371940929201293750713267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6325175811203450001902045 2371940929201293750713267)
          ·
            refine ⟨3557911393801940626069901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371940929201293750713267 3557911393801940626069901)
            ·
              refine ⟨1334216772675727734776213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3557911393801940626069901 1334216772675727734776213)
              ·
                refine ⟨62541411219174737567635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1334216772675727734776213 62541411219174737567635)
                ·
                  rfl

theorem cell22_1644286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1644286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644286 prefixEnd_1644286 := by exact prefixLift 1644286
  have htrace : WordTrace (prefixWord ++ tailWord_1644286) baseStart_1644286 baseEnd_1644286 := by
    simpa [prefixWord, tailWord_1644286, baseEnd_1644286] using wordTrace_append hprefix tailTrace_1644286
  have hstable : (prefixWord ++ tailWord_1644286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644286).length < 2 ^ (prefixWord ++ tailWord_1644286).sum := by decide
  have hdescent : baseEnd_1644286 < baseStart_1644286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644312 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_1644312 : Nat := 118140960795 + 1644312 * 2 ^ 59
def prefixEnd_1644312 : Nat := 4983230072969 + 3 ^ 40 * 1644312 * 2
def baseEnd_1644312 : Nat := 562881601303917236958635

theorem tailTrace_1644312 : CollatzResearch.WordTrace tailWord_1644312 prefixEnd_1644312 562881601303917236958635 := by
  unfold tailWord_1644312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29986492809472962488499595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39981990412630616651332793 29986492809472962488499595)
  ·
    refine ⟨44979739214209443732749393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29986492809472962488499595 44979739214209443732749393)
    ·
      refine ⟨33734804410657082799562045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44979739214209443732749393 33734804410657082799562045)
      ·
        refine ⟨12650551653996406049835767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33734804410657082799562045 12650551653996406049835767)
        ·
          refine ⟨18975827480994609074753651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650551653996406049835767 18975827480994609074753651)
          ·
            refine ⟨28463741221491913612130477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18975827480994609074753651 28463741221491913612130477)
            ·
              refine ⟨10673902958059467604548929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28463741221491913612130477 10673902958059467604548929)
              ·
                refine ⟨8005427218544600703411697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10673902958059467604548929 8005427218544600703411697)
                ·
                  refine ⟨6004070413908450527558773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005427218544600703411697 6004070413908450527558773)
                  ·
                    refine ⟨562881601303917236958635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6004070413908450527558773 562881601303917236958635)
                    ·
                      rfl

theorem cell22_1644312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_1644312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644312 prefixEnd_1644312 := by exact prefixLift 1644312
  have htrace : WordTrace (prefixWord ++ tailWord_1644312) baseStart_1644312 baseEnd_1644312 := by
    simpa [prefixWord, tailWord_1644312, baseEnd_1644312] using wordTrace_append hprefix tailTrace_1644312
  have hstable : (prefixWord ++ tailWord_1644312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644312).length < 2 ^ (prefixWord ++ tailWord_1644312).sum := by decide
  have hdescent : baseEnd_1644312 < baseStart_1644312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644314 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_1644314 : Nat := 118140960795 + 1644314 * 2 ^ 59
def prefixEnd_1644314 : Nat := 4983230072969 + 3 ^ 40 * 1644314 * 2
def baseEnd_1644314 : Nat := 187627428648263299469543

theorem tailTrace_1644314 : CollatzResearch.WordTrace tailWord_1644314 prefixEnd_1644314 187627428648263299469543 := by
  unfold tailWord_1644314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993264641234669829642999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39982039043292452879047997 14993264641234669829642999)
  ·
    refine ⟨22489896961852004744464499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14993264641234669829642999 22489896961852004744464499)
    ·
      refine ⟨33734845442778007116696749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22489896961852004744464499 33734845442778007116696749)
      ·
        refine ⟨12650567041041752668761281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33734845442778007116696749 12650567041041752668761281)
        ·
          refine ⟨9487925280781314501570961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12650567041041752668761281 9487925280781314501570961)
          ·
            refine ⟨7115943960585985876178221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9487925280781314501570961 7115943960585985876178221)
            ·
              refine ⟨2668478985219744703566833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7115943960585985876178221 2668478985219744703566833)
              ·
                refine ⟨2001359238914808527675125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668478985219744703566833 2001359238914808527675125)
                ·
                  refine ⟨187627428648263299469543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2001359238914808527675125 187627428648263299469543)
                  ·
                    rfl

theorem cell22_1644314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_1644314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644314 prefixEnd_1644314 := by exact prefixLift 1644314
  have htrace : WordTrace (prefixWord ++ tailWord_1644314) baseStart_1644314 baseEnd_1644314 := by
    simpa [prefixWord, tailWord_1644314, baseEnd_1644314] using wordTrace_append hprefix tailTrace_1644314
  have hstable : (prefixWord ++ tailWord_1644314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644314).length < 2 ^ (prefixWord ++ tailWord_1644314).sum := by decide
  have hdescent : baseEnd_1644314 < baseStart_1644314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644344 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_1644344 : Nat := 118140960795 + 1644344 * 2 ^ 59
def prefixEnd_1644344 : Nat := 4983230072969 + 3 ^ 40 * 1644344 * 2
def baseEnd_1644344 : Nat := 562892555557879820158537

theorem tailTrace_1644344 : CollatzResearch.WordTrace tailWord_1644344 prefixEnd_1644344 562892555557879820158537 := by
  unfold tailWord_1644344
  simp only [CollatzResearch.WordTrace]
  refine ⟨29987076377414997221082043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39982768503219996294776057 29987076377414997221082043)
  ·
    refine ⟨44980614566122495831623065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29987076377414997221082043 44980614566122495831623065)
    ·
      refine ⟨33735460924591871873717299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44980614566122495831623065 33735460924591871873717299)
      ·
        refine ⟨50603191386887807810575949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33735460924591871873717299 50603191386887807810575949)
        ·
          refine ⟨18976196770082927928965981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50603191386887807810575949 18976196770082927928965981)
          ·
            refine ⟨7116073788781097973362243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18976196770082927928965981 7116073788781097973362243)
            ·
              refine ⟨10674110683171646960043365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116073788781097973362243 10674110683171646960043365)
              ·
                refine ⟨2001395753094683805008131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10674110683171646960043365 2001395753094683805008131)
                ·
                  refine ⟨3002093629642025707512197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001395753094683805008131 3002093629642025707512197)
                  ·
                    refine ⟨562892555557879820158537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002093629642025707512197 562892555557879820158537)
                    ·
                      rfl

theorem cell22_1644344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_1644344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644344 prefixEnd_1644344 := by exact prefixLift 1644344
  have htrace : WordTrace (prefixWord ++ tailWord_1644344) baseStart_1644344 baseEnd_1644344 := by
    simpa [prefixWord, tailWord_1644344, baseEnd_1644344] using wordTrace_append hprefix tailTrace_1644344
  have hstable : (prefixWord ++ tailWord_1644344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644344).length < 2 ^ (prefixWord ++ tailWord_1644344).sum := by decide
  have hdescent : baseEnd_1644344 < baseStart_1644344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644357 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_1644357 : Nat := 118140960795 + 1644357 * 2 ^ 59
def prefixEnd_1644357 : Nat := 4983230072969 + 3 ^ 40 * 1644357 * 2
def baseEnd_1644357 : Nat := 562897005723552119583497

theorem tailTrace_1644357 : CollatzResearch.WordTrace tailWord_1644357 prefixEnd_1644357 562897005723552119583497 := by
  unfold tailWord_1644357
  simp only [CollatzResearch.WordTrace]
  refine ⟨59974626903782897662387325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39983084602521931774924883 59974626903782897662387325)
  ·
    refine ⟨22490485088918586623395247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59974626903782897662387325 22490485088918586623395247)
    ·
      refine ⟨33735727633377879935092871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22490485088918586623395247 33735727633377879935092871)
      ·
        refine ⟨50603591450066819902639307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33735727633377879935092871 50603591450066819902639307)
        ·
          refine ⟨75905387175100229853958961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50603591450066819902639307 75905387175100229853958961)
          ·
            refine ⟨56929040381325172390469221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75905387175100229853958961 56929040381325172390469221)
            ·
              refine ⟨10674195071498469823212979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56929040381325172390469221 10674195071498469823212979)
              ·
                refine ⟨16011292607247704734819469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674195071498469823212979 16011292607247704734819469)
                ·
                  refine ⟨6004234727717889275557301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16011292607247704734819469 6004234727717889275557301)
                  ·
                    refine ⟨562897005723552119583497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6004234727717889275557301 562897005723552119583497)
                    ·
                      rfl

theorem cell22_1644357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_1644357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644357 prefixEnd_1644357 := by exact prefixLift 1644357
  have htrace : WordTrace (prefixWord ++ tailWord_1644357) baseStart_1644357 baseEnd_1644357 := by
    simpa [prefixWord, tailWord_1644357, baseEnd_1644357] using wordTrace_append hprefix tailTrace_1644357
  have hstable : (prefixWord ++ tailWord_1644357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644357).length < 2 ^ (prefixWord ++ tailWord_1644357).sum := by decide
  have hdescent : baseEnd_1644357 < baseStart_1644357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644391 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1644391 : Nat := 118140960795 + 1644391 * 2 ^ 59
def prefixEnd_1644391 : Nat := 4983230072969 + 3 ^ 40 * 1644391 * 2
def baseEnd_1644391 : Nat := 562908644618387364233393

theorem tailTrace_1644391 : CollatzResearch.WordTrace tailWord_1644391 prefixEnd_1644391 562908644618387364233393 := by
  unfold tailWord_1644391
  simp only [CollatzResearch.WordTrace]
  refine ⟨59975866985659721469125027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39983911323773147646083351 59975866985659721469125027)
  ·
    refine ⟨89963800478489582203687541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59975866985659721469125027 89963800478489582203687541)
    ·
      refine ⟨8434106294858398331595707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89963800478489582203687541 8434106294858398331595707)
      ·
        refine ⟨12651159442287597497393561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434106294858398331595707 12651159442287597497393561)
        ·
          refine ⟨9488369581715698123045171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12651159442287597497393561 9488369581715698123045171)
          ·
            refine ⟨14232554372573547184567757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488369581715698123045171 14232554372573547184567757)
            ·
              refine ⟨5337207889715080194212909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14232554372573547184567757 5337207889715080194212909)
              ·
                refine ⟨2001452958643155072829841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5337207889715080194212909 2001452958643155072829841)
                ·
                  refine ⟨1501089718982366304622381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001452958643155072829841 1501089718982366304622381)
                  ·
                    refine ⟨562908644618387364233393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501089718982366304622381 562908644618387364233393)
                    ·
                      rfl

theorem cell22_1644391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1644391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644391 prefixEnd_1644391 := by exact prefixLift 1644391
  have htrace : WordTrace (prefixWord ++ tailWord_1644391) baseStart_1644391 baseEnd_1644391 := by
    simpa [prefixWord, tailWord_1644391, baseEnd_1644391] using wordTrace_append hprefix tailTrace_1644391
  have hstable : (prefixWord ++ tailWord_1644391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644391).length < 2 ^ (prefixWord ++ tailWord_1644391).sum := by decide
  have hdescent : baseEnd_1644391 < baseStart_1644391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644524 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_1644524 : Nat := 118140960795 + 1644524 * 2 ^ 59
def prefixEnd_1644524 : Nat := 4983230072969 + 3 ^ 40 * 1644524 * 2
def baseEnd_1644524 : Nat := 562954173236419350657985

theorem tailTrace_1644524 : CollatzResearch.WordTrace tailWord_1644524 prefixEnd_1644524 562954173236419350657985 := by
  unfold tailWord_1644524
  simp only [CollatzResearch.WordTrace]
  refine ⟨29990358947088942591858313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39987145262785256789144417 29990358947088942591858313)
  ·
    refine ⟨22492769210316706943893735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29990358947088942591858313 22492769210316706943893735)
    ·
      refine ⟨33739153815475060415840603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22492769210316706943893735 33739153815475060415840603)
      ·
        refine ⟨50608730723212590623760905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33739153815475060415840603 50608730723212590623760905)
        ·
          refine ⟨37956548042409442967820679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50608730723212590623760905 37956548042409442967820679)
          ·
            refine ⟨56934822063614164451731019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37956548042409442967820679 56934822063614164451731019)
            ·
              refine ⟨85402233095421246677596529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56934822063614164451731019 85402233095421246677596529)
              ·
                refine ⟨64051674821565935008197397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85402233095421246677596529 64051674821565935008197397)
                ·
                  refine ⟨3002422257260903203509253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64051674821565935008197397 3002422257260903203509253)
                  ·
                    refine ⟨562954173236419350657985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002422257260903203509253 562954173236419350657985)
                    ·
                      rfl

theorem cell22_1644524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_1644524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644524 prefixEnd_1644524 := by exact prefixLift 1644524
  have htrace : WordTrace (prefixWord ++ tailWord_1644524) baseStart_1644524 baseEnd_1644524 := by
    simpa [prefixWord, tailWord_1644524, baseEnd_1644524] using wordTrace_append hprefix tailTrace_1644524
  have hstable : (prefixWord ++ tailWord_1644524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644524).length < 2 ^ (prefixWord ++ tailWord_1644524).sum := by decide
  have hdescent : baseEnd_1644524 < baseStart_1644524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644564 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1644564 : Nat := 118140960795 + 1644564 * 2 ^ 59
def prefixEnd_1644564 : Nat := 4983230072969 + 3 ^ 40 * 1644564 * 2
def baseEnd_1644564 : Nat := 562967866053872579657863

theorem tailTrace_1644564 : CollatzResearch.WordTrace tailWord_1644564 prefixEnd_1644564 562967866053872579657863 := by
  unfold tailWord_1644564
  simp only [CollatzResearch.WordTrace]
  refine ⟨29991088407016486007586373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39988117876021981343448497 29991088407016486007586373)
  ·
    refine ⟨5623329076315591126422445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29991088407016486007586373 5623329076315591126422445)
    ·
      refine ⟨2108748403618346672408417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5623329076315591126422445 2108748403618346672408417)
      ·
        refine ⟨1581561302713760004306313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108748403618346672408417 1581561302713760004306313)
        ·
          refine ⟨1186170977035320003229735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581561302713760004306313 1186170977035320003229735)
          ·
            refine ⟨1779256465552980004844603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186170977035320003229735 1779256465552980004844603)
            ·
              refine ⟨2668884698329470007266905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779256465552980004844603 2668884698329470007266905)
              ·
                refine ⟨2001663523747102505450179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668884698329470007266905 2001663523747102505450179)
                ·
                  refine ⟨3002495285620653758175269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001663523747102505450179 3002495285620653758175269)
                  ·
                    refine ⟨562967866053872579657863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002495285620653758175269 562967866053872579657863)
                    ·
                      rfl

theorem cell22_1644564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1644564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644564 prefixEnd_1644564 := by exact prefixLift 1644564
  have htrace : WordTrace (prefixWord ++ tailWord_1644564) baseStart_1644564 baseEnd_1644564 := by
    simpa [prefixWord, tailWord_1644564, baseEnd_1644564] using wordTrace_append hprefix tailTrace_1644564
  have hstable : (prefixWord ++ tailWord_1644564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644564).length < 2 ^ (prefixWord ++ tailWord_1644564).sum := by decide
  have hdescent : baseEnd_1644564 < baseStart_1644564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644605 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_1644605 : Nat := 118140960795 + 1644605 * 2 ^ 59
def prefixEnd_1644605 : Nat := 4983230072969 + 3 ^ 40 * 1644605 * 2
def baseEnd_1644605 : Nat := 562981901191762139382737

theorem tailTrace_1644605 : CollatzResearch.WordTrace tailWord_1644605 prefixEnd_1644605 562981901191762139382737 := by
  unfold tailWord_1644605
  simp only [CollatzResearch.WordTrace]
  refine ⟨59983672206884436017415269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39989114804589624011610179 59983672206884436017415269)
  ·
    refine ⟨11246938538790831753265363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59983672206884436017415269 11246938538790831753265363)
    ·
      refine ⟨16870407808186247629898045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246938538790831753265363 16870407808186247629898045)
      ·
        refine ⟨6326402928069842861211767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16870407808186247629898045 6326402928069842861211767)
        ·
          refine ⟨9489604392104764291817651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6326402928069842861211767 9489604392104764291817651)
          ·
            refine ⟨14234406588157146437726477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489604392104764291817651 14234406588157146437726477)
            ·
              refine ⟨5337902470558929914147429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14234406588157146437726477 5337902470558929914147429)
              ·
                refine ⟨1000856713229799358902643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5337902470558929914147429 1000856713229799358902643)
                ·
                  refine ⟨1501285069844699038353965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000856713229799358902643 1501285069844699038353965)
                  ·
                    refine ⟨562981901191762139382737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501285069844699038353965 562981901191762139382737)
                    ·
                      rfl

theorem cell22_1644605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_1644605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644605 prefixEnd_1644605 := by exact prefixLift 1644605
  have htrace : WordTrace (prefixWord ++ tailWord_1644605) baseStart_1644605 baseEnd_1644605 := by
    simpa [prefixWord, tailWord_1644605, baseEnd_1644605] using wordTrace_append hprefix tailTrace_1644605
  have hstable : (prefixWord ++ tailWord_1644605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644605).length < 2 ^ (prefixWord ++ tailWord_1644605).sum := by decide
  have hdescent : baseEnd_1644605 < baseStart_1644605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644631 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1644631 : Nat := 118140960795 + 1644631 * 2 ^ 59
def prefixEnd_1644631 : Nat := 4983230072969 + 3 ^ 40 * 1644631 * 2
def baseEnd_1644631 : Nat := 562990801523106738232657

theorem tailTrace_1644631 : CollatzResearch.WordTrace tailWord_1644631 prefixEnd_1644631 562990801523106738232657 := by
  unfold tailWord_1644631
  simp only [CollatzResearch.WordTrace]
  refine ⟨59984620504790242457861747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39989747003193494971907831 59984620504790242457861747)
  ·
    refine ⟨89976930757185363686792621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59984620504790242457861747 89976930757185363686792621)
    ·
      refine ⟨33741349033944511382547233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89976930757185363686792621 33741349033944511382547233)
      ·
        refine ⟨25306011775458383536910425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33741349033944511382547233 25306011775458383536910425)
        ·
          refine ⟨18979508831593787652682819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25306011775458383536910425 18979508831593787652682819)
          ·
            refine ⟨28469263247390681479024229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18979508831593787652682819 28469263247390681479024229)
            ·
              refine ⟨5337986858885752777317043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28469263247390681479024229 5337986858885752777317043)
              ·
                refine ⟨8006980288328629165975565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337986858885752777317043 8006980288328629165975565)
                ·
                  refine ⟨3002617608123235937240837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8006980288328629165975565 3002617608123235937240837)
                  ·
                    refine ⟨562990801523106738232657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002617608123235937240837 562990801523106738232657)
                    ·
                      rfl

theorem cell22_1644631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1644631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644631 prefixEnd_1644631 := by exact prefixLift 1644631
  have htrace : WordTrace (prefixWord ++ tailWord_1644631) baseStart_1644631 baseEnd_1644631 := by
    simpa [prefixWord, tailWord_1644631, baseEnd_1644631] using wordTrace_append hprefix tailTrace_1644631
  have hstable : (prefixWord ++ tailWord_1644631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644631).length < 2 ^ (prefixWord ++ tailWord_1644631).sum := by decide
  have hdescent : baseEnd_1644631 < baseStart_1644631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644663 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 4]
def baseStart_1644663 : Nat := 118140960795 + 1644663 * 2 ^ 59
def prefixEnd_1644663 : Nat := 4983230072969 + 3 ^ 40 * 1644663 * 2
def baseEnd_1644663 : Nat := 187667251925689773810853

theorem tailTrace_1644663 : CollatzResearch.WordTrace tailWord_1644663 prefixEnd_1644663 187667251925689773810853 := by
  unfold tailWord_1644663
  simp only [CollatzResearch.WordTrace]
  refine ⟨59985787640674311923026643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39990525093782874615351095 59985787640674311923026643)
  ·
    refine ⟨89978681461011467884539965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59985787640674311923026643 89978681461011467884539965)
    ·
      refine ⟨33742005547879300456702487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89978681461011467884539965 33742005547879300456702487)
      ·
        refine ⟨50613008321818950685053731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33742005547879300456702487 50613008321818950685053731)
        ·
          refine ⟨75919512482728426027580597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50613008321818950685053731 75919512482728426027580597)
          ·
            refine ⟨7117454295255789940085681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75919512482728426027580597 7117454295255789940085681)
            ·
              refine ⟨5338090721441842455064261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7117454295255789940085681 5338090721441842455064261)
              ·
                refine ⟨1000892010270345460324549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5338090721441842455064261 1000892010270345460324549)
                ·
                  refine ⟨187667251925689773810853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000892010270345460324549 187667251925689773810853)
                  ·
                    rfl

theorem cell22_1644663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 4].length) (baseStart_1644663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644663 prefixEnd_1644663 := by exact prefixLift 1644663
  have htrace : WordTrace (prefixWord ++ tailWord_1644663) baseStart_1644663 baseEnd_1644663 := by
    simpa [prefixWord, tailWord_1644663, baseEnd_1644663] using wordTrace_append hprefix tailTrace_1644663
  have hstable : (prefixWord ++ tailWord_1644663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644663).length < 2 ^ (prefixWord ++ tailWord_1644663).sum := by decide
  have hdescent : baseEnd_1644663 < baseStart_1644663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644676 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1644676 : Nat := 118140960795 + 1644676 * 2 ^ 59
def prefixEnd_1644676 : Nat := 4983230072969 + 3 ^ 40 * 1644676 * 2
def baseEnd_1644676 : Nat := 563006205942741620857519

theorem tailTrace_1644676 : CollatzResearch.WordTrace tailWord_1644676 prefixEnd_1644676 563006205942741620857519 := by
  unfold tailWord_1644676
  simp only [CollatzResearch.WordTrace]
  refine ⟨29993130894813607571624941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39990841193084810095499921 29993130894813607571624941)
  ·
    refine ⟨11247424085555102839359353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29993130894813607571624941 11247424085555102839359353)
    ·
      refine ⟨8435568064166327129519515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11247424085555102839359353 8435568064166327129519515)
      ·
        refine ⟨12653352096249490694279273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435568064166327129519515 12653352096249490694279273)
        ·
          refine ⟨9490014072187118020709455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12653352096249490694279273 9490014072187118020709455)
          ·
            refine ⟨14235021108280677031064183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490014072187118020709455 14235021108280677031064183)
            ·
              refine ⟨21352531662421015546596275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14235021108280677031064183 21352531662421015546596275)
              ·
                refine ⟨32028797493631523319894413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21352531662421015546596275 32028797493631523319894413)
                ·
                  refine ⟨12010799060111821244960405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32028797493631523319894413 12010799060111821244960405)
                  ·
                    refine ⟨563006205942741620857519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12010799060111821244960405 563006205942741620857519)
                    ·
                      rfl

theorem cell22_1644676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1644676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644676 prefixEnd_1644676 := by exact prefixLift 1644676
  have htrace : WordTrace (prefixWord ++ tailWord_1644676) baseStart_1644676 baseEnd_1644676 := by
    simpa [prefixWord, tailWord_1644676, baseEnd_1644676] using wordTrace_append hprefix tailTrace_1644676
  have hstable : (prefixWord ++ tailWord_1644676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644676).length < 2 ^ (prefixWord ++ tailWord_1644676).sum := by decide
  have hdescent : baseEnd_1644676 < baseStart_1644676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644708 : List Nat := [2, 3, 1, 2, 4, 2, 8]
def baseStart_1644708 : Nat := 118140960795 + 1644708 * 2 ^ 59
def prefixEnd_1644708 : Nat := 4983230072969 + 3 ^ 40 * 1644708 * 2
def baseEnd_1644708 : Nat := 20852487414692748298423

theorem tailTrace_1644708 : CollatzResearch.WordTrace tailWord_1644708 prefixEnd_1644708 20852487414692748298423 := by
  unfold tailWord_1644708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29993714462755642304207389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39991619283674189738943185 29993714462755642304207389)
  ·
    refine ⟨11247642923533365864077771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29993714462755642304207389 11247642923533365864077771)
    ·
      refine ⟨16871464385300048796116657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11247642923533365864077771 16871464385300048796116657)
      ·
        refine ⟨12653598288975036597087493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16871464385300048796116657 12653598288975036597087493)
        ·
          refine ⟨2372549679182819361953905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12653598288975036597087493 2372549679182819361953905)
          ·
            refine ⟨1779412259387114521465429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372549679182819361953905 1779412259387114521465429)
            ·
              refine ⟨20852487414692748298423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1779412259387114521465429 20852487414692748298423)
              ·
                rfl

theorem cell22_1644708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 8].length) (baseStart_1644708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644708 prefixEnd_1644708 := by exact prefixLift 1644708
  have htrace : WordTrace (prefixWord ++ tailWord_1644708) baseStart_1644708 baseEnd_1644708 := by
    simpa [prefixWord, tailWord_1644708, baseEnd_1644708] using wordTrace_append hprefix tailTrace_1644708
  have hstable : (prefixWord ++ tailWord_1644708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644708).length < 2 ^ (prefixWord ++ tailWord_1644708).sum := by decide
  have hdescent : baseEnd_1644708 < baseStart_1644708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644714 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_1644714 : Nat := 118140960795 + 1644714 * 2 ^ 59
def prefixEnd_1644714 : Nat := 4983230072969 + 3 ^ 40 * 1644714 * 2
def baseEnd_1644714 : Nat := 187673071373107396135801

theorem tailTrace_1644714 : CollatzResearch.WordTrace tailWord_1644714 prefixEnd_1644714 187673071373107396135801 := by
  unfold tailWord_1644714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14996911940872386908283299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39991765175659698422088797 14996911940872386908283299)
  ·
    refine ⟨22495367911308580362424949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14996911940872386908283299 22495367911308580362424949)
    ·
      refine ⟨2108940741685179408977339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22495367911308580362424949 2108940741685179408977339)
      ·
        refine ⟨3163411112527769113466009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108940741685179408977339 3163411112527769113466009)
        ·
          refine ⟨2372558334395826835099507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3163411112527769113466009 2372558334395826835099507)
          ·
            refine ⟨3558837501593740252649261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372558334395826835099507 3558837501593740252649261)
            ·
              refine ⟨1334564063097652594743473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558837501593740252649261 1334564063097652594743473)
              ·
                refine ⟨1000923047323239446057605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334564063097652594743473 1000923047323239446057605)
                ·
                  refine ⟨187673071373107396135801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000923047323239446057605 187673071373107396135801)
                  ·
                    rfl

theorem cell22_1644714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_1644714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644714 prefixEnd_1644714 := by exact prefixLift 1644714
  have htrace : WordTrace (prefixWord ++ tailWord_1644714) baseStart_1644714 baseEnd_1644714 := by
    simpa [prefixWord, tailWord_1644714, baseEnd_1644714] using wordTrace_append hprefix tailTrace_1644714
  have hstable : (prefixWord ++ tailWord_1644714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644714).length < 2 ^ (prefixWord ++ tailWord_1644714).sum := by decide
  have hdescent : baseEnd_1644714 < baseStart_1644714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644725 : List Nat := [1, 3, 3, 4, 1, 1, 2, 7]
def baseStart_1644725 : Nat := 118140960795 + 1644725 * 2 ^ 59
def prefixEnd_1644725 : Nat := 4983230072969 + 3 ^ 40 * 1644725 * 2
def baseEnd_1644725 : Nat := 62558108849346869598041

theorem tailTrace_1644725 : CollatzResearch.WordTrace tailWord_1644725 prefixEnd_1644725 62558108849346869598041 := by
  unfold tailWord_1644725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59988048966449696511783629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39992032644299797674522419 59988048966449696511783629)
  ·
    refine ⟨22495518362418636191918861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59988048966449696511783629 22495518362418636191918861)
    ·
      refine ⟨8435819385906988571969573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22495518362418636191918861 8435819385906988571969573)
      ·
        refine ⟨1581716134857560357244295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8435819385906988571969573 1581716134857560357244295)
        ·
          refine ⟨2372574202286340535866443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581716134857560357244295 2372574202286340535866443)
          ·
            refine ⟨3558861303429510803799665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372574202286340535866443 3558861303429510803799665)
            ·
              refine ⟨2669145977572133102849749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3558861303429510803799665 2669145977572133102849749)
              ·
                refine ⟨62558108849346869598041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2669145977572133102849749 62558108849346869598041)
                ·
                  rfl

theorem cell22_1644725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 7].length) (baseStart_1644725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644725 prefixEnd_1644725 := by exact prefixLift 1644725
  have htrace : WordTrace (prefixWord ++ tailWord_1644725) baseStart_1644725 baseEnd_1644725 := by
    simpa [prefixWord, tailWord_1644725, baseEnd_1644725] using wordTrace_append hprefix tailTrace_1644725
  have hstable : (prefixWord ++ tailWord_1644725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644725).length < 2 ^ (prefixWord ++ tailWord_1644725).sum := by decide
  have hdescent : baseEnd_1644725 < baseStart_1644725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644783 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_1644783 : Nat := 118140960795 + 1644783 * 2 ^ 59
def prefixEnd_1644783 : Nat := 4983230072969 + 3 ^ 40 * 1644783 * 2
def baseEnd_1644783 : Nat := 563042834229429008432191

theorem tailTrace_1644783 : CollatzResearch.WordTrace tailWord_1644783 prefixEnd_1644783 563042834229429008432191 := by
  unfold tailWord_1644783
  simp only [CollatzResearch.WordTrace]
  refine ⟨59990164400239572417395003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39993442933493048278263335 59990164400239572417395003)
  ·
    refine ⟨89985246600359358626092505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59990164400239572417395003 89985246600359358626092505)
    ·
      refine ⟨67488934950269518969569379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89985246600359358626092505 67488934950269518969569379)
      ·
        refine ⟨101233402425404278454354069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67488934950269518969569379 101233402425404278454354069)
        ·
          refine ⟨4745315738690825552547847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101233402425404278454354069 4745315738690825552547847)
          ·
            refine ⟨7117973608036238328821771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745315738690825552547847 7117973608036238328821771)
            ·
              refine ⟨10676960412054357493232657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117973608036238328821771 10676960412054357493232657)
              ·
                refine ⟨8007720309040768119924493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10676960412054357493232657 8007720309040768119924493)
                ·
                  refine ⟨3002895115890288044971685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8007720309040768119924493 3002895115890288044971685)
                  ·
                    refine ⟨563042834229429008432191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002895115890288044971685 563042834229429008432191)
                    ·
                      rfl

theorem cell22_1644783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_1644783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644783 prefixEnd_1644783 := by exact prefixLift 1644783
  have htrace : WordTrace (prefixWord ++ tailWord_1644783) baseStart_1644783 baseEnd_1644783 := by
    simpa [prefixWord, tailWord_1644783, baseEnd_1644783] using wordTrace_append hprefix tailTrace_1644783
  have hstable : (prefixWord ++ tailWord_1644783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644783).length < 2 ^ (prefixWord ++ tailWord_1644783).sum := by decide
  have hdescent : baseEnd_1644783 < baseStart_1644783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644817 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_1644817 : Nat := 118140960795 + 1644817 * 2 ^ 59
def prefixEnd_1644817 : Nat := 4983230072969 + 3 ^ 40 * 1644817 * 2
def baseEnd_1644817 : Nat := 563054473124264253082087

theorem tailTrace_1644817 : CollatzResearch.WordTrace tailWord_1644817 prefixEnd_1644817 563054473124264253082087 := by
  unfold tailWord_1644817
  simp only [CollatzResearch.WordTrace]
  refine ⟨59991404482116396224132705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39994269654744264149421803 59991404482116396224132705)
  ·
    refine ⟨44993553361587297168099529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59991404482116396224132705 44993553361587297168099529)
    ·
      refine ⟨33745165021190472876074647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44993553361587297168099529 33745165021190472876074647)
      ·
        refine ⟨50617747531785709314111971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33745165021190472876074647 50617747531785709314111971)
        ·
          refine ⟨75926621297678563971167957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50617747531785709314111971 75926621297678563971167957)
          ·
            refine ⟨1779530186664341343074249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75926621297678563971167957 1779530186664341343074249)
            ·
              refine ⟨1334647639998256007305687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779530186664341343074249 1334647639998256007305687)
              ·
                refine ⟨2001971459997384010958531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334647639998256007305687 2001971459997384010958531)
                ·
                  refine ⟨3002957189996076016437797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001971459997384010958531 3002957189996076016437797)
                  ·
                    refine ⟨563054473124264253082087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002957189996076016437797 563054473124264253082087)
                    ·
                      rfl

theorem cell22_1644817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_1644817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644817 prefixEnd_1644817 := by exact prefixLift 1644817
  have htrace : WordTrace (prefixWord ++ tailWord_1644817) baseStart_1644817 baseEnd_1644817 := by
    simpa [prefixWord, tailWord_1644817, baseEnd_1644817] using wordTrace_append hprefix tailTrace_1644817
  have hstable : (prefixWord ++ tailWord_1644817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644817).length < 2 ^ (prefixWord ++ tailWord_1644817).sum := by decide
  have hdescent : baseEnd_1644817 < baseStart_1644817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644828 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1644828 : Nat := 118140960795 + 1644828 * 2 ^ 59
def prefixEnd_1644828 : Nat := 4983230072969 + 3 ^ 40 * 1644828 * 2
def baseEnd_1644828 : Nat := 563058238649063891057053

theorem tailTrace_1644828 : CollatzResearch.WordTrace tailWord_1644828 prefixEnd_1644828 563058238649063891057053 := by
  unfold tailWord_1644828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29995902842538272551391569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39994537123384363401855425 29995902842538272551391569)
  ·
    refine ⟨22496927131903704413543677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29995902842538272551391569 22496927131903704413543677)
    ·
      refine ⟨8436347674463889155078879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22496927131903704413543677 8436347674463889155078879)
      ·
        refine ⟨12654521511695833732618319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436347674463889155078879 12654521511695833732618319)
        ·
          refine ⟨18981782267543750598927479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12654521511695833732618319 18981782267543750598927479)
          ·
            refine ⟨28472673401315625898391219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18981782267543750598927479 28472673401315625898391219)
            ·
              refine ⟨42709010101973438847586829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28472673401315625898391219 42709010101973438847586829)
              ·
                refine ⟨16015878788240039567845061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42709010101973438847586829 16015878788240039567845061)
                ·
                  refine ⟨3002977272795007418970949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16015878788240039567845061 3002977272795007418970949)
                  ·
                    refine ⟨563058238649063891057053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3002977272795007418970949 563058238649063891057053)
                    ·
                      rfl

theorem cell22_1644828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1644828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644828 prefixEnd_1644828 := by exact prefixLift 1644828
  have htrace : WordTrace (prefixWord ++ tailWord_1644828) baseStart_1644828 baseEnd_1644828 := by
    simpa [prefixWord, tailWord_1644828, baseEnd_1644828] using wordTrace_append hprefix tailTrace_1644828
  have hstable : (prefixWord ++ tailWord_1644828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644828).length < 2 ^ (prefixWord ++ tailWord_1644828).sum := by decide
  have hdescent : baseEnd_1644828 < baseStart_1644828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644965 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_1644965 : Nat := 118140960795 + 1644965 * 2 ^ 59
def prefixEnd_1644965 : Nat := 4983230072969 + 3 ^ 40 * 1644965 * 2
def baseEnd_1644965 : Nat := 563105136548841200381633

theorem tailTrace_1644965 : CollatzResearch.WordTrace tailWord_1644965 prefixEnd_1644965 563105136548841200381633 := by
  unfold tailWord_1644965
  simp only [CollatzResearch.WordTrace]
  refine ⟨59996802485580217500520349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39997868323720145000346899 59996802485580217500520349)
  ·
    refine ⟨22498800932092581562695131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59996802485580217500520349 22498800932092581562695131)
    ·
      refine ⟨33748201398138872344042697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22498800932092581562695131 33748201398138872344042697)
      ·
        refine ⟨25311151048604154258032023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33748201398138872344042697 25311151048604154258032023)
        ·
          refine ⟨37966726572906231387048035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25311151048604154258032023 37966726572906231387048035)
          ·
            refine ⟨56950089859359347080572053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37966726572906231387048035 56950089859359347080572053)
            ·
              refine ⟨2669535462157469394401815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56950089859359347080572053 2669535462157469394401815)
              ·
                refine ⟨4004303193236204091602723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2669535462157469394401815 4004303193236204091602723)
                ·
                  refine ⟨6006454789854306137404085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004303193236204091602723 6006454789854306137404085)
                  ·
                    refine ⟨563105136548841200381633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6006454789854306137404085 563105136548841200381633)
                    ·
                      rfl

theorem cell22_1644965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_1644965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644965 prefixEnd_1644965 := by exact prefixLift 1644965
  have htrace : WordTrace (prefixWord ++ tailWord_1644965) baseStart_1644965 baseEnd_1644965 := by
    simpa [prefixWord, tailWord_1644965, baseEnd_1644965] using wordTrace_append hprefix tailTrace_1644965
  have hstable : (prefixWord ++ tailWord_1644965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644965).length < 2 ^ (prefixWord ++ tailWord_1644965).sum := by decide
  have hdescent : baseEnd_1644965 < baseStart_1644965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644999 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1644999 : Nat := 118140960795 + 1644999 * 2 ^ 59
def prefixEnd_1644999 : Nat := 4983230072969 + 3 ^ 40 * 1644999 * 2
def baseEnd_1644999 : Nat := 563116775443676445031529

theorem tailTrace_1644999 : CollatzResearch.WordTrace tailWord_1644999 prefixEnd_1644999 563116775443676445031529 := by
  unfold tailWord_1644999
  simp only [CollatzResearch.WordTrace]
  refine ⟨59998042567457041307258051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39998695044971360871505367 59998042567457041307258051)
  ·
    refine ⟨89997063851185561960887077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59998042567457041307258051 89997063851185561960887077)
    ·
      refine ⟨16874449472097292867666327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89997063851185561960887077 16874449472097292867666327)
      ·
        refine ⟨25311674208145939301499491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16874449472097292867666327 25311674208145939301499491)
        ·
          refine ⟨37967511312218908952249237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25311674208145939301499491 37967511312218908952249237)
          ·
            refine ⟨1779727092760261357136683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37967511312218908952249237 1779727092760261357136683)
            ·
              refine ⟨2669590639140392035705025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779727092760261357136683 2669590639140392035705025)
              ·
                refine ⟨2002192979355294026778769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669590639140392035705025 2002192979355294026778769)
                ·
                  refine ⟨1501644734516470520084077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002192979355294026778769 1501644734516470520084077)
                  ·
                    refine ⟨563116775443676445031529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501644734516470520084077 563116775443676445031529)
                    ·
                      rfl

theorem cell22_1644999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1644999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1644999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1644999 prefixEnd_1644999 := by exact prefixLift 1644999
  have htrace : WordTrace (prefixWord ++ tailWord_1644999) baseStart_1644999 baseEnd_1644999 := by
    simpa [prefixWord, tailWord_1644999, baseEnd_1644999] using wordTrace_append hprefix tailTrace_1644999
  have hstable : (prefixWord ++ tailWord_1644999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644999).length < 2 ^ (prefixWord ++ tailWord_1644999).sum := by decide
  have hdescent : baseEnd_1644999 < baseStart_1644999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645029 : List Nat := [1, 3, 1, 5, 2, 2, 2, 6]
def baseStart_1645029 : Nat := 118140960795 + 1645029 * 2 ^ 59
def prefixEnd_1645029 : Nat := 4983230072969 + 3 ^ 40 * 1645029 * 2
def baseEnd_1645029 : Nat := 62569671672974040753493

theorem tailTrace_1645029 : CollatzResearch.WordTrace tailWord_1645029 prefixEnd_1645029 62569671672974040753493 := by
  unfold tailWord_1645029
  simp only [CollatzResearch.WordTrace]
  refine ⟨59999136757348356430850141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39999424504898904287233427 59999136757348356430850141)
  ·
    refine ⟨22499676284005633661568803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59999136757348356430850141 22499676284005633661568803)
    ·
      refine ⟨33749514426008450492353205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22499676284005633661568803 33749514426008450492353205)
      ·
        refine ⟨3164016977438292233658113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33749514426008450492353205 3164016977438292233658113)
        ·
          refine ⟨2373012733078719175243585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164016977438292233658113 2373012733078719175243585)
          ·
            refine ⟨1779759549809039381432689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373012733078719175243585 1779759549809039381432689)
            ·
              refine ⟨1334819662356779536074517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779759549809039381432689 1334819662356779536074517)
              ·
                refine ⟨62569671672974040753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1334819662356779536074517 62569671672974040753493)
                ·
                  rfl

theorem cell22_1645029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 6].length) (baseStart_1645029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645029 prefixEnd_1645029 := by exact prefixLift 1645029
  have htrace : WordTrace (prefixWord ++ tailWord_1645029) baseStart_1645029 baseEnd_1645029 := by
    simpa [prefixWord, tailWord_1645029, baseEnd_1645029] using wordTrace_append hprefix tailTrace_1645029
  have hstable : (prefixWord ++ tailWord_1645029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645029).length < 2 ^ (prefixWord ++ tailWord_1645029).sum := by decide
  have hdescent : baseEnd_1645029 < baseStart_1645029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645115 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_1645115 : Nat := 118140960795 + 1645115 * 2 ^ 59
def prefixEnd_1645115 : Nat := 4983230072969 + 3 ^ 40 * 1645115 * 2
def baseEnd_1645115 : Nat := 563156484614290809131173

theorem tailTrace_1645115 : CollatzResearch.WordTrace tailWord_1645115 prefixEnd_1645115 563156484614290809131173 := by
  unfold tailWord_1645115
  simp only [CollatzResearch.WordTrace]
  refine ⟨60002273435036793118480799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40001515623357862078987199 60002273435036793118480799)
  ·
    refine ⟨90003410152555189677721199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60002273435036793118480799 90003410152555189677721199)
    ·
      refine ⟨135005115228832784516581799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90003410152555189677721199 135005115228832784516581799)
      ·
        refine ⟨202507672843249176774872699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135005115228832784516581799 202507672843249176774872699)
        ·
          refine ⟨303761509264873765162309049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202507672843249176774872699 303761509264873765162309049)
          ·
            refine ⟨227821131948655323871731787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303761509264873765162309049 227821131948655323871731787)
            ·
              refine ⟨341731697922982985807597681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227821131948655323871731787 341731697922982985807597681)
              ·
                refine ⟨256298773442237239355698261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341731697922982985807597681 256298773442237239355698261)
                ·
                  refine ⟨3003501251276217648699589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 256298773442237239355698261 3003501251276217648699589)
                  ·
                    refine ⟨563156484614290809131173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3003501251276217648699589 563156484614290809131173)
                    ·
                      rfl

theorem cell22_1645115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_1645115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645115 prefixEnd_1645115 := by exact prefixLift 1645115
  have htrace : WordTrace (prefixWord ++ tailWord_1645115) baseStart_1645115 baseEnd_1645115 := by
    simpa [prefixWord, tailWord_1645115, baseEnd_1645115] using wordTrace_append hprefix tailTrace_1645115
  have hstable : (prefixWord ++ tailWord_1645115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645115).length < 2 ^ (prefixWord ++ tailWord_1645115).sum := by decide
  have hdescent : baseEnd_1645115 < baseStart_1645115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645134 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1645134 : Nat := 118140960795 + 1645134 * 2 ^ 59
def prefixEnd_1645134 : Nat := 4983230072969 + 3 ^ 40 * 1645134 * 2
def baseEnd_1645134 : Nat := 563162988702581092906115

theorem tailTrace_1645134 : CollatzResearch.WordTrace tailWord_1645134 prefixEnd_1645134 563162988702581092906115 := by
  unfold tailWord_1645134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500370802745994920427807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40001977614645306242281637 7500370802745994920427807)
  ·
    refine ⟨11250556204118992380641711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7500370802745994920427807 11250556204118992380641711)
    ·
      refine ⟨16875834306178488570962567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11250556204118992380641711 16875834306178488570962567)
      ·
        refine ⟨25313751459267732856443851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16875834306178488570962567 25313751459267732856443851)
        ·
          refine ⟨37970627188901599284665777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25313751459267732856443851 37970627188901599284665777)
          ·
            refine ⟨28477970391676199463499333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37970627188901599284665777 28477970391676199463499333)
            ·
              refine ⟨5339619448439287399406125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28477970391676199463499333 5339619448439287399406125)
              ·
                refine ⟨2002357293164732774777297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5339619448439287399406125 2002357293164732774777297)
                ·
                  refine ⟨1501767969873549581082973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002357293164732774777297 1501767969873549581082973)
                  ·
                    refine ⟨563162988702581092906115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501767969873549581082973 563162988702581092906115)
                    ·
                      rfl

theorem cell22_1645134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1645134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645134 prefixEnd_1645134 := by exact prefixLift 1645134
  have htrace : WordTrace (prefixWord ++ tailWord_1645134) baseStart_1645134 baseEnd_1645134 := by
    simpa [prefixWord, tailWord_1645134, baseEnd_1645134] using wordTrace_append hprefix tailTrace_1645134
  have hstable : (prefixWord ++ tailWord_1645134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645134).length < 2 ^ (prefixWord ++ tailWord_1645134).sum := by decide
  have hdescent : baseEnd_1645134 < baseStart_1645134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645168 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_1645168 : Nat := 118140960795 + 1645168 * 2 ^ 59
def prefixEnd_1645168 : Nat := 4983230072969 + 3 ^ 40 * 1645168 * 2
def baseEnd_1645168 : Nat := 563174627597416337556011

theorem tailTrace_1645168 : CollatzResearch.WordTrace tailWord_1645168 prefixEnd_1645168 563174627597416337556011 := by
  unfold tailWord_1645168
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002103251922391585080079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40002804335896522113440105 30002103251922391585080079)
  ·
    refine ⟨45003154877883587377620119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30002103251922391585080079 45003154877883587377620119)
    ·
      refine ⟨67504732316825381066430179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45003154877883587377620119 67504732316825381066430179)
      ·
        refine ⟨101257098475238071599645269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67504732316825381066430179 101257098475238071599645269)
        ·
          refine ⟨1186606622756696151558343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 101257098475238071599645269 1186606622756696151558343)
          ·
            refine ⟨1779909934135044227337515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186606622756696151558343 1779909934135044227337515)
            ·
              refine ⟨2669864901202566341006273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779909934135044227337515 2669864901202566341006273)
              ·
                refine ⟨2002398675901924755754705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669864901202566341006273 2002398675901924755754705)
                ·
                  refine ⟨1501799006926443566816029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002398675901924755754705 1501799006926443566816029)
                  ·
                    refine ⟨563174627597416337556011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501799006926443566816029 563174627597416337556011)
                    ·
                      rfl

theorem cell22_1645168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_1645168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645168 prefixEnd_1645168 := by exact prefixLift 1645168
  have htrace : WordTrace (prefixWord ++ tailWord_1645168) baseStart_1645168 baseEnd_1645168 := by
    simpa [prefixWord, tailWord_1645168, baseEnd_1645168] using wordTrace_append hprefix tailTrace_1645168
  have hstable : (prefixWord ++ tailWord_1645168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645168).length < 2 ^ (prefixWord ++ tailWord_1645168).sum := by decide
  have hdescent : baseEnd_1645168 < baseStart_1645168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645256 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1645256 : Nat := 118140960795 + 1645256 * 2 ^ 59
def prefixEnd_1645256 : Nat := 4983230072969 + 3 ^ 40 * 1645256 * 2
def baseEnd_1645256 : Nat := 563204751795813441355741

theorem tailTrace_1645256 : CollatzResearch.WordTrace tailWord_1645256 prefixEnd_1645256 563204751795813441355741 := by
  unfold tailWord_1645256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30003708063762987099681811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40004944085017316132909081 30003708063762987099681811)
  ·
    refine ⟨45005562095644480649522717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30003708063762987099681811 45005562095644480649522717)
    ·
      refine ⟨16877085785866680243571019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45005562095644480649522717 16877085785866680243571019)
      ·
        refine ⟨25315628678800020365356529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16877085785866680243571019 25315628678800020365356529)
        ·
          refine ⟨18986721509100015274017397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25315628678800020365356529 18986721509100015274017397)
          ·
            refine ⟨1780005141478126431939131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18986721509100015274017397 1780005141478126431939131)
            ·
              refine ⟨2670007712217189647908697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780005141478126431939131 2670007712217189647908697)
              ·
                refine ⟨2002505784162892235931523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670007712217189647908697 2002505784162892235931523)
                ·
                  refine ⟨3003758676244338353897285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002505784162892235931523 3003758676244338353897285)
                  ·
                    refine ⟨563204751795813441355741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3003758676244338353897285 563204751795813441355741)
                    ·
                      rfl

theorem cell22_1645256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1645256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645256 prefixEnd_1645256 := by exact prefixLift 1645256
  have htrace : WordTrace (prefixWord ++ tailWord_1645256) baseStart_1645256 baseEnd_1645256 := by
    simpa [prefixWord, tailWord_1645256, baseEnd_1645256] using wordTrace_append hprefix tailTrace_1645256
  have hstable : (prefixWord ++ tailWord_1645256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645256).length < 2 ^ (prefixWord ++ tailWord_1645256).sum := by decide
  have hdescent : baseEnd_1645256 < baseStart_1645256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645284 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1645284 : Nat := 118140960795 + 1645284 * 2 ^ 59
def prefixEnd_1645284 : Nat := 4983230072969 + 3 ^ 40 * 1645284 * 2
def baseEnd_1645284 : Nat := 563214336768030701655655

theorem tailTrace_1645284 : CollatzResearch.WordTrace tailWord_1645284 prefixEnd_1645284 563214336768030701655655 := by
  unfold tailWord_1645284
  simp only [CollatzResearch.WordTrace]
  refine ⟨30004218685712267490691453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40005624914283023320921937 30004218685712267490691453)
  ·
    refine ⟨11251582007142100309009295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30004218685712267490691453 11251582007142100309009295)
    ·
      refine ⟨16877373010713150463513943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11251582007142100309009295 16877373010713150463513943)
      ·
        refine ⟨25316059516069725695270915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16877373010713150463513943 25316059516069725695270915)
        ·
          refine ⟨37974089274104588542906373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25316059516069725695270915 37974089274104588542906373)
          ·
            refine ⟨7120141738894610351794945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37974089274104588542906373 7120141738894610351794945)
            ·
              refine ⟨5340106304170957763846209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7120141738894610351794945 5340106304170957763846209)
              ·
                refine ⟨4005079728128218322884657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340106304170957763846209 4005079728128218322884657)
                ·
                  refine ⟨3003809796096163742163493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4005079728128218322884657 3003809796096163742163493)
                  ·
                    refine ⟨563214336768030701655655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3003809796096163742163493 563214336768030701655655)
                    ·
                      rfl

theorem cell22_1645284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1645284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645284 prefixEnd_1645284 := by exact prefixLift 1645284
  have htrace : WordTrace (prefixWord ++ tailWord_1645284) baseStart_1645284 baseEnd_1645284 := by
    simpa [prefixWord, tailWord_1645284, baseEnd_1645284] using wordTrace_append hprefix tailTrace_1645284
  have hstable : (prefixWord ++ tailWord_1645284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645284).length < 2 ^ (prefixWord ++ tailWord_1645284).sum := by decide
  have hdescent : baseEnd_1645284 < baseStart_1645284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645327 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 7]
def baseStart_1645327 : Nat := 118140960795 + 1645327 * 2 ^ 59
def prefixEnd_1645327 : Nat := 4983230072969 + 3 ^ 40 * 1645327 * 2
def baseEnd_1645327 : Nat := 187743018848930974276841

theorem tailTrace_1645327 : CollatzResearch.WordTrace tailWord_1645327 prefixEnd_1645327 187743018848930974276841 := by
  unfold tailWord_1645327
  simp only [CollatzResearch.WordTrace]
  refine ⟨60010005710268753325198235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40006670473512502216798823 60010005710268753325198235)
  ·
    refine ⟨90015008565403129987797353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60010005710268753325198235 90015008565403129987797353)
    ·
      refine ⟨67511256424052347490848015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90015008565403129987797353 67511256424052347490848015)
      ·
        refine ⟨101266884636078521236272023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67511256424052347490848015 101266884636078521236272023)
        ·
          refine ⟨151900326954117781854408035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101266884636078521236272023 151900326954117781854408035)
          ·
            refine ⟨227850490431176672781612053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151900326954117781854408035 227850490431176672781612053)
            ·
              refine ⟨10680491738961406536638065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 227850490431176672781612053 10680491738961406536638065)
              ·
                refine ⟨8010368804221054902478549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10680491738961406536638065 8010368804221054902478549)
                ·
                  refine ⟨187743018848930974276841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8010368804221054902478549 187743018848930974276841)
                  ·
                    rfl

theorem cell22_1645327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_1645327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645327 prefixEnd_1645327 := by exact prefixLift 1645327
  have htrace : WordTrace (prefixWord ++ tailWord_1645327) baseStart_1645327 baseEnd_1645327 := by
    simpa [prefixWord, tailWord_1645327, baseEnd_1645327] using wordTrace_append hprefix tailTrace_1645327
  have hstable : (prefixWord ++ tailWord_1645327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645327).length < 2 ^ (prefixWord ++ tailWord_1645327).sum := by decide
  have hdescent : baseEnd_1645327 < baseStart_1645327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645344 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_1645344 : Nat := 118140960795 + 1645344 * 2 ^ 59
def prefixEnd_1645344 : Nat := 4983230072969 + 3 ^ 40 * 1645344 * 2
def baseEnd_1645344 : Nat := 187744958664736848385157

theorem tailTrace_1645344 : CollatzResearch.WordTrace tailWord_1645344 prefixEnd_1645344 187744958664736848385157 := by
  unfold tailWord_1645344
  simp only [CollatzResearch.WordTrace]
  refine ⟨30005312875603582614283543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40007083834138110152378057 30005312875603582614283543)
  ·
    refine ⟨45007969313405373921425315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30005312875603582614283543 45007969313405373921425315)
    ·
      refine ⟨67511953970108060882137973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45007969313405373921425315 67511953970108060882137973)
      ·
        refine ⟨6329245684697630707700435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67511953970108060882137973 6329245684697630707700435)
        ·
          refine ⟨9493868527046446061550653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6329245684697630707700435 9493868527046446061550653)
          ·
            refine ⟨3560200697642417273081495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9493868527046446061550653 3560200697642417273081495)
            ·
              refine ⟨5340301046463625909622243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560200697642417273081495 5340301046463625909622243)
              ·
                refine ⟨8010451569695438864433365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340301046463625909622243 8010451569695438864433365)
                ·
                  refine ⟨187744958664736848385157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8010451569695438864433365 187744958664736848385157)
                  ·
                    rfl

theorem cell22_1645344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_1645344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645344 prefixEnd_1645344 := by exact prefixLift 1645344
  have htrace : WordTrace (prefixWord ++ tailWord_1645344) baseStart_1645344 baseEnd_1645344 := by
    simpa [prefixWord, tailWord_1645344, baseEnd_1645344] using wordTrace_append hprefix tailTrace_1645344
  have hstable : (prefixWord ++ tailWord_1645344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645344).length < 2 ^ (prefixWord ++ tailWord_1645344).sum := by decide
  have hdescent : baseEnd_1645344 < baseStart_1645344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645348 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_1645348 : Nat := 118140960795 + 1645348 * 2 ^ 59
def prefixEnd_1645348 : Nat := 4983230072969 + 3 ^ 40 * 1645348 * 2
def baseEnd_1645348 : Nat := 563236245275955868055459

theorem tailTrace_1645348 : CollatzResearch.WordTrace tailWord_1645348 prefixEnd_1645348 563236245275955868055459 := by
  unfold tailWord_1645348
  simp only [CollatzResearch.WordTrace]
  refine ⟨30005385821596336955856349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40007181095461782607808465 30005385821596336955856349)
  ·
    refine ⟨11252019683098626358446131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30005385821596336955856349 11252019683098626358446131)
    ·
      refine ⟨16878029524647939537669197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11252019683098626358446131 16878029524647939537669197)
      ·
        refine ⟨6329261071742977326625949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16878029524647939537669197 6329261071742977326625949)
        ·
          refine ⟨2373472901903616497484731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6329261071742977326625949 2373472901903616497484731)
          ·
            refine ⟨3560209352855424746227097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373472901903616497484731 3560209352855424746227097)
            ·
              refine ⟨2670157014641568559670323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560209352855424746227097 2670157014641568559670323)
              ·
                refine ⟨4005235521962352839505485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670157014641568559670323 4005235521962352839505485)
                ·
                  refine ⟨1501963320735882314814557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4005235521962352839505485 1501963320735882314814557)
                  ·
                    refine ⟨563236245275955868055459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1501963320735882314814557 563236245275955868055459)
                    ·
                      rfl

theorem cell22_1645348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_1645348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645348 prefixEnd_1645348 := by exact prefixLift 1645348
  have htrace : WordTrace (prefixWord ++ tailWord_1645348) baseStart_1645348 baseEnd_1645348 := by
    simpa [prefixWord, tailWord_1645348, baseEnd_1645348] using wordTrace_append hprefix tailTrace_1645348
  have hstable : (prefixWord ++ tailWord_1645348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645348).length < 2 ^ (prefixWord ++ tailWord_1645348).sum := by decide
  have hdescent : baseEnd_1645348 < baseStart_1645348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645361 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 5]
def baseStart_1645361 : Nat := 118140960795 + 1645361 * 2 ^ 59
def prefixEnd_1645361 : Nat := 4983230072969 + 3 ^ 40 * 1645361 * 2
def baseEnd_1645361 : Nat := 187746898480542722493473

theorem tailTrace_1645361 : CollatzResearch.WordTrace tailWord_1645361 prefixEnd_1645361 187746898480542722493473 := by
  unfold tailWord_1645361
  simp only [CollatzResearch.WordTrace]
  refine ⟨60011245792145577131935937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40007497194763718087957291 60011245792145577131935937)
  ·
    refine ⟨45008434344109182848951953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60011245792145577131935937 45008434344109182848951953)
    ·
      refine ⟨33756325758081887136713965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45008434344109182848951953 33756325758081887136713965)
      ·
        refine ⟨12658622159280707676267737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33756325758081887136713965 12658622159280707676267737)
        ·
          refine ⟨9493966619460530757200803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12658622159280707676267737 9493966619460530757200803)
          ·
            refine ⟨14240949929190796135801205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9493966619460530757200803 14240949929190796135801205)
            ·
              refine ⟨1335089055861637137731363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14240949929190796135801205 1335089055861637137731363)
              ·
                refine ⟨2002633583792455706597045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335089055861637137731363 2002633583792455706597045)
                ·
                  refine ⟨187746898480542722493473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2002633583792455706597045 187746898480542722493473)
                  ·
                    rfl

theorem cell22_1645361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_1645361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645361 prefixEnd_1645361 := by exact prefixLift 1645361
  have htrace : WordTrace (prefixWord ++ tailWord_1645361) baseStart_1645361 baseEnd_1645361 := by
    simpa [prefixWord, tailWord_1645361, baseEnd_1645361] using wordTrace_append hprefix tailTrace_1645361
  have hstable : (prefixWord ++ tailWord_1645361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645361).length < 2 ^ (prefixWord ++ tailWord_1645361).sum := by decide
  have hdescent : baseEnd_1645361 < baseStart_1645361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645468 : List Nat := [2, 2, 3, 3, 2, 2, 1, 7]
def baseStart_1645468 : Nat := 118140960795 + 1645468 * 2 ^ 59
def prefixEnd_1645468 : Nat := 4983230072969 + 3 ^ 40 * 1645468 * 2
def baseEnd_1645468 : Nat := 62586369303146172783899

theorem tailTrace_1645468 : CollatzResearch.WordTrace tailWord_1645468 prefixEnd_1645468 62586369303146172783899 := by
  unfold tailWord_1645468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30007574201378967203040529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40010098935171956270720705 30007574201378967203040529)
  ·
    refine ⟨22505680651034225402280397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30007574201378967203040529 22505680651034225402280397)
    ·
      refine ⟨8439630244137834525855149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22505680651034225402280397 8439630244137834525855149)
      ·
        refine ⟨3164861341551687947195681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8439630244137834525855149 3164861341551687947195681)
        ·
          refine ⟨2373646006163765960396761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164861341551687947195681 2373646006163765960396761)
          ·
            refine ⟨1780234504622824470297571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373646006163765960396761 1780234504622824470297571)
            ·
              refine ⟨2670351756934236705446357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780234504622824470297571 2670351756934236705446357)
              ·
                refine ⟨62586369303146172783899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2670351756934236705446357 62586369303146172783899)
                ·
                  rfl

theorem cell22_1645468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 7].length) (baseStart_1645468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645468 prefixEnd_1645468 := by exact prefixLift 1645468
  have htrace : WordTrace (prefixWord ++ tailWord_1645468) baseStart_1645468 baseEnd_1645468 := by
    simpa [prefixWord, tailWord_1645468, baseEnd_1645468] using wordTrace_append hprefix tailTrace_1645468
  have hstable : (prefixWord ++ tailWord_1645468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645468).length < 2 ^ (prefixWord ++ tailWord_1645468).sum := by decide
  have hdescent : baseEnd_1645468 < baseStart_1645468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645485 : List Nat := [1, 5, 2, 3, 1, 1, 3, 6]
def baseStart_1645485 : Nat := 118140960795 + 1645485 * 2 ^ 59
def prefixEnd_1645485 : Nat := 4983230072969 + 3 ^ 40 * 1645485 * 2
def baseEnd_1645485 : Nat := 62587015908414797486671

theorem tailTrace_1645485 : CollatzResearch.WordTrace tailWord_1645485 prefixEnd_1645485 62587015908414797486671 := by
  unfold tailWord_1645485
  simp only [CollatzResearch.WordTrace]
  refine ⟨60015768443696346309449909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40010512295797564206299939 60015768443696346309449909)
  ·
    refine ⟨5626478291596532466510929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60015768443696346309449909 5626478291596532466510929)
    ·
      refine ⟨4219858718697399349883197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5626478291596532466510929 4219858718697399349883197)
      ·
        refine ⟨1582447019511524756206199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4219858718697399349883197 1582447019511524756206199)
        ·
          refine ⟨2373670529267287134309299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582447019511524756206199 2373670529267287134309299)
          ·
            refine ⟨3560505793900930701463949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373670529267287134309299 3560505793900930701463949)
            ·
              refine ⟨1335189672712849013048981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3560505793900930701463949 1335189672712849013048981)
              ·
                refine ⟨62587015908414797486671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1335189672712849013048981 62587015908414797486671)
                ·
                  rfl

theorem cell22_1645485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 6].length) (baseStart_1645485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645485 prefixEnd_1645485 := by exact prefixLift 1645485
  have htrace : WordTrace (prefixWord ++ tailWord_1645485) baseStart_1645485 baseEnd_1645485 := by
    simpa [prefixWord, tailWord_1645485, baseEnd_1645485] using wordTrace_append hprefix tailTrace_1645485
  have hstable : (prefixWord ++ tailWord_1645485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645485).length < 2 ^ (prefixWord ++ tailWord_1645485).sum := by decide
  have hdescent : baseEnd_1645485 < baseStart_1645485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645543 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1645543 : Nat := 118140960795 + 1645543 * 2 ^ 59
def prefixEnd_1645543 : Nat := 4983230072969 + 3 ^ 40 * 1645543 * 2
def baseEnd_1645543 : Nat := 563302997761040359429861

theorem tailTrace_1645543 : CollatzResearch.WordTrace tailWord_1645543 prefixEnd_1645543 563302997761040359429861 := by
  unfold tailWord_1645543
  simp only [CollatzResearch.WordTrace]
  refine ⟨60017883877486222215061283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40011922584990814810040855 60017883877486222215061283)
  ·
    refine ⟨90026825816229333322591925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60017883877486222215061283 90026825816229333322591925)
    ·
      refine ⟨8440014920271499998992993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90026825816229333322591925 8440014920271499998992993)
      ·
        refine ⟨6330011190203624999244745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8440014920271499998992993 6330011190203624999244745)
        ·
          refine ⟨4747508392652718749433559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6330011190203624999244745 4747508392652718749433559)
          ·
            refine ⟨7121262588979078124150339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747508392652718749433559 7121262588979078124150339)
            ·
              refine ⟨10681893883468617186225509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121262588979078124150339 10681893883468617186225509)
              ·
                refine ⟨2002855103150365722417283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10681893883468617186225509 2002855103150365722417283)
                ·
                  refine ⟨3004282654725548583625925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002855103150365722417283 3004282654725548583625925)
                  ·
                    refine ⟨563302997761040359429861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3004282654725548583625925 563302997761040359429861)
                    ·
                      rfl

theorem cell22_1645543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1645543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645543 prefixEnd_1645543 := by exact prefixLift 1645543
  have htrace : WordTrace (prefixWord ++ tailWord_1645543) baseStart_1645543 baseEnd_1645543 := by
    simpa [prefixWord, tailWord_1645543, baseEnd_1645543] using wordTrace_append hprefix tailTrace_1645543
  have hstable : (prefixWord ++ tailWord_1645543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645543).length < 2 ^ (prefixWord ++ tailWord_1645543).sum := by decide
  have hdescent : baseEnd_1645543 < baseStart_1645543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645573 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_1645573 : Nat := 118140960795 + 1645573 * 2 ^ 59
def prefixEnd_1645573 : Nat := 4983230072969 + 3 ^ 40 * 1645573 * 2
def baseEnd_1645573 : Nat := 563313267374130281179769

theorem tailTrace_1645573 : CollatzResearch.WordTrace tailWord_1645573 prefixEnd_1645573 563313267374130281179769 := by
  unfold tailWord_1645573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60018978067377537338653373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40012652044918358225768915 60018978067377537338653373)
  ·
    refine ⟨22507116775266576501995015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60018978067377537338653373 22507116775266576501995015)
    ·
      refine ⟨33760675162899864752992523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22507116775266576501995015 33760675162899864752992523)
      ·
        refine ⟨50641012744349797129488785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33760675162899864752992523 50641012744349797129488785)
        ·
          refine ⟨37980759558262347847116589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50641012744349797129488785 37980759558262347847116589)
          ·
            refine ⟨14242784834348380442668721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37980759558262347847116589 14242784834348380442668721)
            ·
              refine ⟨10682088625761285332001541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14242784834348380442668721 10682088625761285332001541)
              ·
                refine ⟨2002891617330240999750289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10682088625761285332001541 2002891617330240999750289)
                ·
                  refine ⟨1502168712997680749812717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002891617330240999750289 1502168712997680749812717)
                  ·
                    refine ⟨563313267374130281179769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502168712997680749812717 563313267374130281179769)
                    ·
                      rfl

theorem cell22_1645573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_1645573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645573 prefixEnd_1645573 := by exact prefixLift 1645573
  have htrace : WordTrace (prefixWord ++ tailWord_1645573) baseStart_1645573 baseEnd_1645573 := by
    simpa [prefixWord, tailWord_1645573, baseEnd_1645573] using wordTrace_append hprefix tailTrace_1645573
  have hstable : (prefixWord ++ tailWord_1645573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645573).length < 2 ^ (prefixWord ++ tailWord_1645573).sum := by decide
  have hdescent : baseEnd_1645573 < baseStart_1645573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645575 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 4]
def baseStart_1645575 : Nat := 118140960795 + 1645575 * 2 ^ 59
def prefixEnd_1645575 : Nat := 4983230072969 + 3 ^ 40 * 1645575 * 2
def baseEnd_1645575 : Nat := 187771317338334314209921

theorem tailTrace_1645575 : CollatzResearch.WordTrace tailWord_1645575 prefixEnd_1645575 187771317338334314209921 := by
  unfold tailWord_1645575
  simp only [CollatzResearch.WordTrace]
  refine ⟨60019051013370291680226179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40012700675580194453484119 60019051013370291680226179)
  ·
    refine ⟨90028576520055437520339269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60019051013370291680226179 90028576520055437520339269)
    ·
      refine ⟨16880358097510394535063613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90028576520055437520339269 16880358097510394535063613)
      ·
        refine ⟨6330134286566397950648855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16880358097510394535063613 6330134286566397950648855)
        ·
          refine ⟨9495201429849596925973283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330134286566397950648855 9495201429849596925973283)
          ·
            refine ⟨14242802144774395388959925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495201429849596925973283 14242802144774395388959925)
            ·
              refine ⟨1335262701072599567714993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14242802144774395388959925 1335262701072599567714993)
              ·
                refine ⟨1001447025804449675786245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335262701072599567714993 1001447025804449675786245)
                ·
                  refine ⟨187771317338334314209921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001447025804449675786245 187771317338334314209921)
                  ·
                    rfl

theorem cell22_1645575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 4].length) (baseStart_1645575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645575 prefixEnd_1645575 := by exact prefixLift 1645575
  have htrace : WordTrace (prefixWord ++ tailWord_1645575) baseStart_1645575 baseEnd_1645575 := by
    simpa [prefixWord, tailWord_1645575, baseEnd_1645575] using wordTrace_append hprefix tailTrace_1645575
  have hstable : (prefixWord ++ tailWord_1645575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645575).length < 2 ^ (prefixWord ++ tailWord_1645575).sum := by decide
  have hdescent : baseEnd_1645575 < baseStart_1645575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645635 : List Nat := [1, 1, 1, 3, 1, 2, 5, 4, 1, 3]
def baseStart_1645635 : Nat := 118140960795 + 1645635 * 2 ^ 59
def prefixEnd_1645635 : Nat := 4983230072969 + 3 ^ 40 * 1645635 * 2
def baseEnd_1645635 : Nat := 563334491241182786129579

theorem tailTrace_1645635 : CollatzResearch.WordTrace tailWord_1645635 prefixEnd_1645635 563334491241182786129579 := by
  unfold tailWord_1645635
  simp only [CollatzResearch.WordTrace]
  refine ⟨60021239393152921927410359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40014159595435281284940239 60021239393152921927410359)
  ·
    refine ⟨90031859089729382891115539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60021239393152921927410359 90031859089729382891115539)
    ·
      refine ⟨135047788634594074336673309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90031859089729382891115539 135047788634594074336673309)
      ·
        refine ⟨50642920737972777876252491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135047788634594074336673309 50642920737972777876252491)
        ·
          refine ⟨75964381106959166814378737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50642920737972777876252491 75964381106959166814378737)
          ·
            refine ⟨56973285830219375110784053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75964381106959166814378737 56973285830219375110784053)
            ·
              refine ⟨5341245546583066416636005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56973285830219375110784053 5341245546583066416636005)
              ·
                refine ⟨1001483539984324953119251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5341245546583066416636005 1001483539984324953119251)
                ·
                  refine ⟨1502225309976487429678877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001483539984324953119251 1502225309976487429678877)
                  ·
                    refine ⟨563334491241182786129579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502225309976487429678877 563334491241182786129579)
                    ·
                      rfl

theorem cell22_1645635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 3].length) (baseStart_1645635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645635 prefixEnd_1645635 := by exact prefixLift 1645635
  have htrace : WordTrace (prefixWord ++ tailWord_1645635) baseStart_1645635 baseEnd_1645635 := by
    simpa [prefixWord, tailWord_1645635, baseEnd_1645635] using wordTrace_append hprefix tailTrace_1645635
  have hstable : (prefixWord ++ tailWord_1645635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645635).length < 2 ^ (prefixWord ++ tailWord_1645635).sum := by decide
  have hdescent : baseEnd_1645635 < baseStart_1645635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645676 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1645676 : Nat := 118140960795 + 1645676 * 2 ^ 59
def prefixEnd_1645676 : Nat := 4983230072969 + 3 ^ 40 * 1645676 * 2
def baseEnd_1645676 : Nat := 187782842126357448618151

theorem tailTrace_1645676 : CollatzResearch.WordTrace tailWord_1645676 prefixEnd_1645676 187782842126357448618151 := by
  unfold tailWord_1645676
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011367393002192964826441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40015156524002923953101921 30011367393002192964826441)
  ·
    refine ⟨22508525544751644723619831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30011367393002192964826441 22508525544751644723619831)
    ·
      refine ⟨33762788317127467085429747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22508525544751644723619831 33762788317127467085429747)
      ·
        refine ⟨50644182475691200628144621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33762788317127467085429747 50644182475691200628144621)
        ·
          refine ⟨18991568428384200235554233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50644182475691200628144621 18991568428384200235554233)
          ·
            refine ⟨14243676321288150176665675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18991568428384200235554233 14243676321288150176665675)
            ·
              refine ⟨21365514481932225264998513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243676321288150176665675 21365514481932225264998513)
              ·
                refine ⟨16024135861449168948748885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21365514481932225264998513 16024135861449168948748885)
                ·
                  refine ⟨187782842126357448618151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16024135861449168948748885 187782842126357448618151)
                  ·
                    rfl

theorem cell22_1645676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1645676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645676 prefixEnd_1645676 := by exact prefixLift 1645676
  have htrace : WordTrace (prefixWord ++ tailWord_1645676) baseStart_1645676 baseEnd_1645676 := by
    simpa [prefixWord, tailWord_1645676, baseEnd_1645676] using wordTrace_append hprefix tailTrace_1645676
  have hstable : (prefixWord ++ tailWord_1645676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645676).length < 2 ^ (prefixWord ++ tailWord_1645676).sum := by decide
  have hdescent : baseEnd_1645676 < baseStart_1645676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645691 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_1645691 : Nat := 118140960795 + 1645691 * 2 ^ 59
def prefixEnd_1645691 : Nat := 4983230072969 + 3 ^ 40 * 1645691 * 2
def baseEnd_1645691 : Nat := 563353661185617306729407

theorem tailTrace_1645691 : CollatzResearch.WordTrace tailWord_1645691 prefixEnd_1645691 563353661185617306729407 := by
  unfold tailWord_1645691
  simp only [CollatzResearch.WordTrace]
  refine ⟨60023281880950043491448927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40015521253966695660965951 60023281880950043491448927)
  ·
    refine ⟨90034922821425065237173391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60023281880950043491448927 90034922821425065237173391)
    ·
      refine ⟨135052384232137597855760087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90034922821425065237173391 135052384232137597855760087)
      ·
        refine ⟨202578576348206396783640131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135052384232137597855760087 202578576348206396783640131)
        ·
          refine ⟨303867864522309595175460197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202578576348206396783640131 303867864522309595175460197)
          ·
            refine ⟨56975224597933049095398787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303867864522309595175460197 56975224597933049095398787)
            ·
              refine ⟨85462836896899573643098181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56975224597933049095398787 85462836896899573643098181)
              ·
                refine ⟨16024281918168670058080909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85462836896899573643098181 16024281918168670058080909)
                ·
                  refine ⟨6009105719313251271780341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16024281918168670058080909 6009105719313251271780341)
                  ·
                    refine ⟨563353661185617306729407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6009105719313251271780341 563353661185617306729407)
                    ·
                      rfl

theorem cell22_1645691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_1645691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645691 prefixEnd_1645691 := by exact prefixLift 1645691
  have htrace : WordTrace (prefixWord ++ tailWord_1645691) baseStart_1645691 baseEnd_1645691 := by
    simpa [prefixWord, tailWord_1645691, baseEnd_1645691] using wordTrace_append hprefix tailTrace_1645691
  have hstable : (prefixWord ++ tailWord_1645691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645691).length < 2 ^ (prefixWord ++ tailWord_1645691).sum := by decide
  have hdescent : baseEnd_1645691 < baseStart_1645691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645693 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1645693 : Nat := 118140960795 + 1645693 * 2 ^ 59
def prefixEnd_1645693 : Nat := 4983230072969 + 3 ^ 40 * 1645693 * 2
def baseEnd_1645693 : Nat := 187784781942163322726467

theorem tailTrace_1645693 : CollatzResearch.WordTrace tailWord_1645693 prefixEnd_1645693 187784781942163322726467 := by
  unfold tailWord_1645693
  simp only [CollatzResearch.WordTrace]
  refine ⟨60023354826942797833021733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40015569884628531888681155 60023354826942797833021733)
  ·
    refine ⟨11254379030051774593691575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60023354826942797833021733 11254379030051774593691575)
    ·
      refine ⟨16881568545077661890537363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11254379030051774593691575 16881568545077661890537363)
      ·
        refine ⟨25322352817616492835806045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16881568545077661890537363 25322352817616492835806045)
        ·
          refine ⟨9495882306606184813427267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25322352817616492835806045 9495882306606184813427267)
          ·
            refine ⟨14243823459909277220140901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495882306606184813427267 14243823459909277220140901)
            ·
              refine ⟨2670716898732989478776419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14243823459909277220140901 2670716898732989478776419)
              ·
                refine ⟨4006075348099484218164629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670716898732989478776419 4006075348099484218164629)
                ·
                  refine ⟨187784781942163322726467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4006075348099484218164629 187784781942163322726467)
                  ·
                    rfl

theorem cell22_1645693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1645693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645693 prefixEnd_1645693 := by exact prefixLift 1645693
  have htrace : WordTrace (prefixWord ++ tailWord_1645693) baseStart_1645693 baseEnd_1645693 := by
    simpa [prefixWord, tailWord_1645693, baseEnd_1645693] using wordTrace_append hprefix tailTrace_1645693
  have hstable : (prefixWord ++ tailWord_1645693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645693).length < 2 ^ (prefixWord ++ tailWord_1645693).sum := by decide
  have hdescent : baseEnd_1645693 < baseStart_1645693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645800 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_1645800 : Nat := 118140960795 + 1645800 * 2 ^ 59
def prefixEnd_1645800 : Nat := 4983230072969 + 3 ^ 40 * 1645800 * 2
def baseEnd_1645800 : Nat := 187796991371059118584691

theorem tailTrace_1645800 : CollatzResearch.WordTrace tailWord_1645800 prefixEnd_1645800 187796991371059118584691 := by
  unfold tailWord_1645800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013628718777577553583427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40018171625036770071444569 30013628718777577553583427)
  ·
    refine ⟨45020443078166366330375141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30013628718777577553583427 45020443078166366330375141)
    ·
      refine ⟨8441333077156193686945339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45020443078166366330375141 8441333077156193686945339)
      ·
        refine ⟨12661999615734290530418009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441333077156193686945339 12661999615734290530418009)
        ·
          refine ⟨9496499711800717897813507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12661999615734290530418009 9496499711800717897813507)
          ·
            refine ⟨14244749567701076846720261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9496499711800717897813507 14244749567701076846720261)
            ·
              refine ⟨2670890543943951908760049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14244749567701076846720261 2670890543943951908760049)
              ·
                refine ⟨2003167907957963931570037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670890543943951908760049 2003167907957963931570037)
                ·
                  refine ⟨187796991371059118584691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2003167907957963931570037 187796991371059118584691)
                  ·
                    rfl

theorem cell22_1645800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_1645800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645800 prefixEnd_1645800 := by exact prefixLift 1645800
  have htrace : WordTrace (prefixWord ++ tailWord_1645800) baseStart_1645800 baseEnd_1645800 := by
    simpa [prefixWord, tailWord_1645800, baseEnd_1645800] using wordTrace_append hprefix tailTrace_1645800
  have hstable : (prefixWord ++ tailWord_1645800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645800).length < 2 ^ (prefixWord ++ tailWord_1645800).sum := by decide
  have hdescent : baseEnd_1645800 < baseStart_1645800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645804 : List Nat := [2, 2, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_1645804 : Nat := 118140960795 + 1645804 * 2 ^ 59
def prefixEnd_1645804 : Nat := 4983230072969 + 3 ^ 40 * 1645804 * 2
def baseEnd_1645804 : Nat := 563392343394922678654061

theorem tailTrace_1645804 : CollatzResearch.WordTrace tailWord_1645804 prefixEnd_1645804 563392343394922678654061 := by
  unfold tailWord_1645804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013701664770331895156233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40018268886360442526874977 30013701664770331895156233)
  ·
    refine ⟨22510276248577748921367175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30013701664770331895156233 22510276248577748921367175)
    ·
      refine ⟨33765414372866623382050763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22510276248577748921367175 33765414372866623382050763)
      ·
        refine ⟨50648121559299935073076145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33765414372866623382050763 50648121559299935073076145)
        ·
          refine ⟨37986091169474951304807109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50648121559299935073076145 37986091169474951304807109)
          ·
            refine ⟨7122392094276553369651333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37986091169474951304807109 7122392094276553369651333)
            ·
              refine ⟨1335448517676853756809625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7122392094276553369651333 1335448517676853756809625)
              ·
                refine ⟨1001586388257640317607219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335448517676853756809625 1001586388257640317607219)
                ·
                  refine ⟨1502379582386460476410829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001586388257640317607219 1502379582386460476410829)
                  ·
                    refine ⟨563392343394922678654061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502379582386460476410829 563392343394922678654061)
                    ·
                      rfl

theorem cell22_1645804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_1645804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645804 prefixEnd_1645804 := by exact prefixLift 1645804
  have htrace : WordTrace (prefixWord ++ tailWord_1645804) baseStart_1645804 baseEnd_1645804 := by
    simpa [prefixWord, tailWord_1645804, baseEnd_1645804] using wordTrace_append hprefix tailTrace_1645804
  have hstable : (prefixWord ++ tailWord_1645804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645804).length < 2 ^ (prefixWord ++ tailWord_1645804).sum := by decide
  have hdescent : baseEnd_1645804 < baseStart_1645804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645877 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1645877 : Nat := 118140960795 + 1645877 * 2 ^ 59
def prefixEnd_1645877 : Nat := 4983230072969 + 3 ^ 40 * 1645877 * 2
def baseEnd_1645877 : Nat := 563417332786774821578837

theorem tailTrace_1645877 : CollatzResearch.WordTrace tailWord_1645877 prefixEnd_1645877 563417332786774821578837 := by
  unfold tailWord_1645877
  simp only [CollatzResearch.WordTrace]
  refine ⟨60030065858276197257719885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40020043905517464838479923 60030065858276197257719885)
  ·
    refine ⟨22511274696853573971644957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60030065858276197257719885 22511274696853573971644957)
    ·
      refine ⟨8441728011320090239366859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22511274696853573971644957 8441728011320090239366859)
      ·
        refine ⟨12662592016980135359050289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441728011320090239366859 12662592016980135359050289)
        ·
          refine ⟨9496944012735101519287717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12662592016980135359050289 9496944012735101519287717)
          ·
            refine ⟨1780677002387831534866447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9496944012735101519287717 1780677002387831534866447)
            ·
              refine ⟨2671015503581747302299671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780677002387831534866447 2671015503581747302299671)
              ·
                refine ⟨4006523255372620953449507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671015503581747302299671 4006523255372620953449507)
                ·
                  refine ⟨6009784883058931430174261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006523255372620953449507 6009784883058931430174261)
                  ·
                    refine ⟨563417332786774821578837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6009784883058931430174261 563417332786774821578837)
                    ·
                      rfl

theorem cell22_1645877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1645877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645877 prefixEnd_1645877 := by exact prefixLift 1645877
  have htrace : WordTrace (prefixWord ++ tailWord_1645877) baseStart_1645877 baseEnd_1645877 := by
    simpa [prefixWord, tailWord_1645877, baseEnd_1645877] using wordTrace_append hprefix tailTrace_1645877
  have hstable : (prefixWord ++ tailWord_1645877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645877).length < 2 ^ (prefixWord ++ tailWord_1645877).sum := by decide
  have hdescent : baseEnd_1645877 < baseStart_1645877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645888 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_1645888 : Nat := 118140960795 + 1645888 * 2 ^ 59
def prefixEnd_1645888 : Nat := 4983230072969 + 3 ^ 40 * 1645888 * 2
def baseEnd_1645888 : Nat := 563421098311574459553803

theorem tailTrace_1645888 : CollatzResearch.WordTrace tailWord_1645888 prefixEnd_1645888 563421098311574459553803 := by
  unfold tailWord_1645888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015233530618173068185159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40020311374157564090913545 30015233530618173068185159)
  ·
    refine ⟨45022850295927259602277739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30015233530618173068185159 45022850295927259602277739)
    ·
      refine ⟨67534275443890889403416609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45022850295927259602277739 67534275443890889403416609)
      ·
        refine ⟨50650706582918167052562457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67534275443890889403416609 50650706582918167052562457)
        ·
          refine ⟨37988029937188625289421843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50650706582918167052562457 37988029937188625289421843)
          ·
            refine ⟨56982044905782937934132765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37988029937188625289421843 56982044905782937934132765)
            ·
              refine ⟨21368266839668601725299787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56982044905782937934132765 21368266839668601725299787)
              ·
                refine ⟨32052400259502902587949681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21368266839668601725299787 32052400259502902587949681)
                ·
                  refine ⟨24039300194627176940962261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32052400259502902587949681 24039300194627176940962261)
                  ·
                    refine ⟨563421098311574459553803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24039300194627176940962261 563421098311574459553803)
                    ·
                      rfl

theorem cell22_1645888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_1645888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645888 prefixEnd_1645888 := by exact prefixLift 1645888
  have htrace : WordTrace (prefixWord ++ tailWord_1645888) baseStart_1645888 baseEnd_1645888 := by
    simpa [prefixWord, tailWord_1645888, baseEnd_1645888] using wordTrace_append hprefix tailTrace_1645888
  have hstable : (prefixWord ++ tailWord_1645888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645888).length < 2 ^ (prefixWord ++ tailWord_1645888).sum := by decide
  have hdescent : baseEnd_1645888 < baseStart_1645888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645892 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1645892 : Nat := 118140960795 + 1645892 * 2 ^ 59
def prefixEnd_1645892 : Nat := 4983230072969 + 3 ^ 40 * 1645892 * 2
def baseEnd_1645892 : Nat := 563422467593319782453791

theorem tailTrace_1645892 : CollatzResearch.WordTrace tailWord_1645892 prefixEnd_1645892 563422467593319782453791 := by
  unfold tailWord_1645892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015306476610927409757965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40020408635481236546343953 30015306476610927409757965)
  ·
    refine ⟨11255739928729097778659237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30015306476610927409757965 11255739928729097778659237)
    ·
      refine ⟨2110451236636705833498607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11255739928729097778659237 2110451236636705833498607)
      ·
        refine ⟨3165676854955058750247911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110451236636705833498607 3165676854955058750247911)
        ·
          refine ⟨4748515282432588125371867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165676854955058750247911 4748515282432588125371867)
          ·
            refine ⟨7122772923648882188057801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748515282432588125371867 7122772923648882188057801)
            ·
              refine ⟨5342079692736661641043351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7122772923648882188057801 5342079692736661641043351)
              ·
                refine ⟨8013119539104992461565027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342079692736661641043351 8013119539104992461565027)
                ·
                  refine ⟨12019679308657488692347541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013119539104992461565027 12019679308657488692347541)
                  ·
                    refine ⟨563422467593319782453791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12019679308657488692347541 563422467593319782453791)
                    ·
                      rfl

theorem cell22_1645892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1645892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645892 prefixEnd_1645892 := by exact prefixLift 1645892
  have htrace : WordTrace (prefixWord ++ tailWord_1645892) baseStart_1645892 baseEnd_1645892 := by
    simpa [prefixWord, tailWord_1645892, baseEnd_1645892] using wordTrace_append hprefix tailTrace_1645892
  have hstable : (prefixWord ++ tailWord_1645892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645892).length < 2 ^ (prefixWord ++ tailWord_1645892).sum := by decide
  have hdescent : baseEnd_1645892 < baseStart_1645892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645928 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1645928 : Nat := 118140960795 + 1645928 * 2 ^ 59
def prefixEnd_1645928 : Nat := 4983230072969 + 3 ^ 40 * 1645928 * 2
def baseEnd_1645928 : Nat := 563434791129027688553681

theorem tailTrace_1645928 : CollatzResearch.WordTrace tailWord_1645928 prefixEnd_1645928 563434791129027688553681 := by
  unfold tailWord_1645928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015962990545716483913219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40021283987394288645217625 30015962990545716483913219)
  ·
    refine ⟨45023944485818574725869829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30015962990545716483913219 45023944485818574725869829)
    ·
      refine ⟨8441989591090982761100593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45023944485818574725869829 8441989591090982761100593)
      ·
        refine ⟨6331492193318237070825445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8441989591090982761100593 6331492193318237070825445)
        ·
          refine ⟨1187154786247169450779771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6331492193318237070825445 1187154786247169450779771)
          ·
            refine ⟨1780732179370754176169657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187154786247169450779771 1780732179370754176169657)
            ·
              refine ⟨1335549134528065632127243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780732179370754176169657 1335549134528065632127243)
              ·
                refine ⟨2003323701792098448190865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335549134528065632127243 2003323701792098448190865)
                ·
                  refine ⟨1502492776344073836143149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003323701792098448190865 1502492776344073836143149)
                  ·
                    refine ⟨563434791129027688553681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502492776344073836143149 563434791129027688553681)
                    ·
                      rfl

theorem cell22_1645928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1645928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645928 prefixEnd_1645928 := by exact prefixLift 1645928
  have htrace : WordTrace (prefixWord ++ tailWord_1645928) baseStart_1645928 baseEnd_1645928 := by
    simpa [prefixWord, tailWord_1645928, baseEnd_1645928] using wordTrace_append hprefix tailTrace_1645928
  have hstable : (prefixWord ++ tailWord_1645928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645928).length < 2 ^ (prefixWord ++ tailWord_1645928).sum := by decide
  have hdescent : baseEnd_1645928 < baseStart_1645928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645935 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 5]
def baseStart_1645935 : Nat := 118140960795 + 1645935 * 2 ^ 59
def prefixEnd_1645935 : Nat := 4983230072969 + 3 ^ 40 * 1645935 * 2
def baseEnd_1645935 : Nat := 187812395790694001209553

theorem tailTrace_1645935 : CollatzResearch.WordTrace tailWord_1645935 prefixEnd_1645935 187812395790694001209553 := by
  unfold tailWord_1645935
  simp only [CollatzResearch.WordTrace]
  refine ⟨60032181292066073163331259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40021454194710715442220839 60032181292066073163331259)
  ·
    refine ⟨90048271938099109744996889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60032181292066073163331259 90048271938099109744996889)
    ·
      refine ⟨67536203953574332308747667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90048271938099109744996889 67536203953574332308747667)
      ·
        refine ⟨101304305930361498463121501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67536203953574332308747667 101304305930361498463121501)
        ·
          refine ⟨37989114723885561923670563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101304305930361498463121501 37989114723885561923670563)
          ·
            refine ⟨56983672085828342885505845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37989114723885561923670563 56983672085828342885505845)
            ·
              refine ⟨5342219258046407145516173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56983672085828342885505845 5342219258046407145516173)
              ·
                refine ⟨2003332221767402679568565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5342219258046407145516173 2003332221767402679568565)
                ·
                  refine ⟨187812395790694001209553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2003332221767402679568565 187812395790694001209553)
                  ·
                    rfl

theorem cell22_1645935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 5].length) (baseStart_1645935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645935 prefixEnd_1645935 := by exact prefixLift 1645935
  have htrace : WordTrace (prefixWord ++ tailWord_1645935) baseStart_1645935 baseEnd_1645935 := by
    simpa [prefixWord, tailWord_1645935, baseEnd_1645935] using wordTrace_append hprefix tailTrace_1645935
  have hstable : (prefixWord ++ tailWord_1645935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645935).length < 2 ^ (prefixWord ++ tailWord_1645935).sum := by decide
  have hdescent : baseEnd_1645935 < baseStart_1645935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645997 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1645997 : Nat := 118140960795 + 1645997 * 2 ^ 59
def prefixEnd_1645997 : Nat := 4983230072969 + 3 ^ 40 * 1645997 * 2
def baseEnd_1645997 : Nat := 187819470413044836192823

theorem tailTrace_1645997 : CollatzResearch.WordTrace tailWord_1645997 prefixEnd_1645997 187819470413044836192823 := by
  unfold tailWord_1645997
  simp only [CollatzResearch.WordTrace]
  refine ⟨60034442617841457752088245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40022961745227638501392163 60034442617841457752088245)
  ·
    refine ⟨5628228995422636664258273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60034442617841457752088245 5628228995422636664258273)
    ·
      refine ⟨4221171746566977498193705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5628228995422636664258273 4221171746566977498193705)
      ·
        refine ⟨3165878809925233123645279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4221171746566977498193705 3165878809925233123645279)
        ·
          refine ⟨4748818214887849685467919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165878809925233123645279 4748818214887849685467919)
          ·
            refine ⟨7123227322331774528201879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748818214887849685467919 7123227322331774528201879)
            ·
              refine ⟨10684840983497661792302819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123227322331774528201879 10684840983497661792302819)
              ·
                refine ⟨16027261475246492688454229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10684840983497661792302819 16027261475246492688454229)
                ·
                  refine ⟨187819470413044836192823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16027261475246492688454229 187819470413044836192823)
                  ·
                    rfl

theorem cell22_1645997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1645997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1645997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1645997 prefixEnd_1645997 := by exact prefixLift 1645997
  have htrace : WordTrace (prefixWord ++ tailWord_1645997) baseStart_1645997 baseEnd_1645997 := by
    simpa [prefixWord, tailWord_1645997, baseEnd_1645997] using wordTrace_append hprefix tailTrace_1645997
  have hstable : (prefixWord ++ tailWord_1645997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645997).length < 2 ^ (prefixWord ++ tailWord_1645997).sum := by decide
  have hdescent : baseEnd_1645997 < baseStart_1645997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646087 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 7]
def baseStart_1646087 : Nat := 118140960795 + 1646087 * 2 ^ 59
def prefixEnd_1646087 : Nat := 4983230072969 + 3 ^ 40 * 1646087 * 2
def baseEnd_1646087 : Nat := 187829740026134757942731

theorem tailTrace_1646087 : CollatzResearch.WordTrace tailWord_1646087 prefixEnd_1646087 187829740026134757942731 := by
  unfold tailWord_1646087
  simp only [CollatzResearch.WordTrace]
  refine ⟨60037725187515403122864515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40025150125010268748576343 60037725187515403122864515)
  ·
    refine ⟨90056587781273104684296773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60037725187515403122864515 90056587781273104684296773)
    ·
      refine ⟨16885610208988707128305645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90056587781273104684296773 16885610208988707128305645)
      ·
        refine ⟨6332103828370765173114617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16885610208988707128305645 6332103828370765173114617)
        ·
          refine ⟨4749077871278073879835963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6332103828370765173114617 4749077871278073879835963)
          ·
            refine ⟨7123616806917110819753945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749077871278073879835963 7123616806917110819753945)
            ·
              refine ⟨5342712605187833114815459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123616806917110819753945 5342712605187833114815459)
              ·
                refine ⟨8014068907781749672223189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342712605187833114815459 8014068907781749672223189)
                ·
                  refine ⟨187829740026134757942731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8014068907781749672223189 187829740026134757942731)
                  ·
                    rfl

theorem cell22_1646087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_1646087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646087 prefixEnd_1646087 := by exact prefixLift 1646087
  have htrace : WordTrace (prefixWord ++ tailWord_1646087) baseStart_1646087 baseEnd_1646087 := by
    simpa [prefixWord, tailWord_1646087, baseEnd_1646087] using wordTrace_append hprefix tailTrace_1646087
  have hstable : (prefixWord ++ tailWord_1646087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646087).length < 2 ^ (prefixWord ++ tailWord_1646087).sum := by decide
  have hdescent : baseEnd_1646087 < baseStart_1646087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646091 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 3, 3]
def baseStart_1646091 : Nat := 118140960795 + 1646091 * 2 ^ 59
def prefixEnd_1646091 : Nat := 4983230072969 + 3 ^ 40 * 1646091 * 2
def baseEnd_1646091 : Nat := 563490589360149596728181

theorem tailTrace_1646091 : CollatzResearch.WordTrace tailWord_1646091 prefixEnd_1646091 563490589360149596728181 := by
  unfold tailWord_1646091
  simp only [CollatzResearch.WordTrace]
  refine ⟨60037871079500911806010127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40025247386333941204006751 60037871079500911806010127)
  ·
    refine ⟨90056806619251367709015191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60037871079500911806010127 90056806619251367709015191)
    ·
      refine ⟨135085209928877051563522787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90056806619251367709015191 135085209928877051563522787)
      ·
        refine ⟨202627814893315577345284181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135085209928877051563522787 202627814893315577345284181)
        ·
          refine ⟨2374544705781041922015049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 202627814893315577345284181 2374544705781041922015049)
          ·
            refine ⟨1780908529335781441511287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374544705781041922015049 1780908529335781441511287)
            ·
              refine ⟨2671362794003672162266931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780908529335781441511287 2671362794003672162266931)
              ·
                refine ⟨4007044191005508243400397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671362794003672162266931 4007044191005508243400397)
                ·
                  refine ⟨1502641571627065591275149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4007044191005508243400397 1502641571627065591275149)
                  ·
                    refine ⟨563490589360149596728181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502641571627065591275149 563490589360149596728181)
                    ·
                      rfl

theorem cell22_1646091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3].length) (baseStart_1646091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646091 prefixEnd_1646091 := by exact prefixLift 1646091
  have htrace : WordTrace (prefixWord ++ tailWord_1646091) baseStart_1646091 baseEnd_1646091 := by
    simpa [prefixWord, tailWord_1646091, baseEnd_1646091] using wordTrace_append hprefix tailTrace_1646091
  have hstable : (prefixWord ++ tailWord_1646091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646091).length < 2 ^ (prefixWord ++ tailWord_1646091).sum := by decide
  have hdescent : baseEnd_1646091 < baseStart_1646091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646104 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 5]
def baseStart_1646104 : Nat := 118140960795 + 1646104 * 2 ^ 59
def prefixEnd_1646104 : Nat := 4983230072969 + 3 ^ 40 * 1646104 * 2
def baseEnd_1646104 : Nat := 187831679841940632051047

theorem tailTrace_1646104 : CollatzResearch.WordTrace tailWord_1646104 prefixEnd_1646104 187831679841940632051047 := by
  unfold tailWord_1646104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019172614226907513116683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40025563485635876684155577 30019172614226907513116683)
  ·
    refine ⟨45028758921340361269675025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30019172614226907513116683 45028758921340361269675025)
    ·
      refine ⟨33771569191005270952256269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45028758921340361269675025 33771569191005270952256269)
      ·
        refine ⟨12664338446626976607096101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33771569191005270952256269 12664338446626976607096101)
        ·
          refine ⟨2374563458742558113830519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12664338446626976607096101 2374563458742558113830519)
          ·
            refine ⟨3561845188113837170745779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374563458742558113830519 3561845188113837170745779)
            ·
              refine ⟨5342767782170755756118669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561845188113837170745779 5342767782170755756118669)
              ·
                refine ⟨2003537918314033408544501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5342767782170755756118669 2003537918314033408544501)
                ·
                  refine ⟨187831679841940632051047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2003537918314033408544501 187831679841940632051047)
                  ·
                    rfl

theorem cell22_1646104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_1646104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646104 prefixEnd_1646104 := by exact prefixLift 1646104
  have htrace : WordTrace (prefixWord ++ tailWord_1646104) baseStart_1646104 baseEnd_1646104 := by
    simpa [prefixWord, tailWord_1646104, baseEnd_1646104] using wordTrace_append hprefix tailTrace_1646104
  have hstable : (prefixWord ++ tailWord_1646104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646104).length < 2 ^ (prefixWord ++ tailWord_1646104).sum := by decide
  have hdescent : baseEnd_1646104 < baseStart_1646104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646149 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 4]
def baseStart_1646149 : Nat := 118140960795 + 1646149 * 2 ^ 59
def prefixEnd_1646149 : Nat := 4983230072969 + 3 ^ 40 * 1646149 * 2
def baseEnd_1646149 : Nat := 187836814648485592926001

theorem tailTrace_1646149 : CollatzResearch.WordTrace tailWord_1646149 prefixEnd_1646149 187836814648485592926001 := by
  unfold tailWord_1646149
  simp only [CollatzResearch.WordTrace]
  refine ⟨60039986513290787711621501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40026657675527191807747667 60039986513290787711621501)
  ·
    refine ⟨22514994942484045391858063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60039986513290787711621501 22514994942484045391858063)
    ·
      refine ⟨33772492413726068087787095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22514994942484045391858063 33772492413726068087787095)
      ·
        refine ⟨50658738620589102131680643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33772492413726068087787095 50658738620589102131680643)
        ·
          refine ⟨75988107930883653197520965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50658738620589102131680643 75988107930883653197520965)
          ·
            refine ⟨14247770237040684974535181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75988107930883653197520965 14247770237040684974535181)
            ·
              refine ⟨5342913838890256865450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14247770237040684974535181 5342913838890256865450693)
              ·
                refine ⟨1001796344791923162272005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5342913838890256865450693 1001796344791923162272005)
                ·
                  refine ⟨187836814648485592926001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001796344791923162272005 187836814648485592926001)
                  ·
                    rfl

theorem cell22_1646149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_1646149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646149 prefixEnd_1646149 := by exact prefixLift 1646149
  have htrace : WordTrace (prefixWord ++ tailWord_1646149) baseStart_1646149 baseEnd_1646149 := by
    simpa [prefixWord, tailWord_1646149, baseEnd_1646149] using wordTrace_append hprefix tailTrace_1646149
  have hstable : (prefixWord ++ tailWord_1646149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646149).length < 2 ^ (prefixWord ++ tailWord_1646149).sum := by decide
  have hdescent : baseEnd_1646149 < baseStart_1646149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646164 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1646164 : Nat := 118140960795 + 1646164 * 2 ^ 59
def prefixEnd_1646164 : Nat := 4983230072969 + 3 ^ 40 * 1646164 * 2
def baseEnd_1646164 : Nat := 563515578752001739652957

theorem tailTrace_1646164 : CollatzResearch.WordTrace tailWord_1646164 prefixEnd_1646164 563515578752001739652957 := by
  unfold tailWord_1646164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30020266804118222636708773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40027022405490963515611697 30020266804118222636708773)
  ·
    refine ⟨5628800025772166744382895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30020266804118222636708773 5628800025772166744382895)
    ·
      refine ⟨8443200038658250116574343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628800025772166744382895 8443200038658250116574343)
      ·
        refine ⟨12664800057987375174861515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443200038658250116574343 12664800057987375174861515)
        ·
          refine ⟨18997200086981062762292273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664800057987375174861515 18997200086981062762292273)
          ·
            refine ⟨14247900065235797071719205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18997200086981062762292273 14247900065235797071719205)
            ·
              refine ⟨2671481262231711950947351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14247900065235797071719205 2671481262231711950947351)
              ·
                refine ⟨4007221893347567926421027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671481262231711950947351 4007221893347567926421027)
                ·
                  refine ⟨6010832840021351889631541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007221893347567926421027 6010832840021351889631541)
                  ·
                    refine ⟨563515578752001739652957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6010832840021351889631541 563515578752001739652957)
                    ·
                      rfl

theorem cell22_1646164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1646164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646164 prefixEnd_1646164 := by exact prefixLift 1646164
  have htrace : WordTrace (prefixWord ++ tailWord_1646164) baseStart_1646164 baseEnd_1646164 := by
    simpa [prefixWord, tailWord_1646164, baseEnd_1646164] using wordTrace_append hprefix tailTrace_1646164
  have hstable : (prefixWord ++ tailWord_1646164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646164).length < 2 ^ (prefixWord ++ tailWord_1646164).sum := by decide
  have hdescent : baseEnd_1646164 < baseStart_1646164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646179 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 2, 4]
def baseStart_1646179 : Nat := 118140960795 + 1646179 * 2 ^ 59
def prefixEnd_1646179 : Nat := 4983230072969 + 3 ^ 40 * 1646179 * 2
def baseEnd_1646179 : Nat := 563520713558546700527911

theorem tailTrace_1646179 : CollatzResearch.WordTrace tailWord_1646179 prefixEnd_1646179 563520713558546700527911 := by
  unfold tailWord_1646179
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041080703182102835213591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40027387135454735223475727 60041080703182102835213591)
  ·
    refine ⟨90061621054773154252820387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60041080703182102835213591 90061621054773154252820387)
    ·
      refine ⟨135092431582159731379230581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90061621054773154252820387 135092431582159731379230581)
      ·
        refine ⟨12664915460827474816802867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135092431582159731379230581 12664915460827474816802867)
        ·
          refine ⟨18997373191241212225204301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664915460827474816802867 18997373191241212225204301)
          ·
            refine ⟨7124014946715454584451613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18997373191241212225204301 7124014946715454584451613)
            ·
              refine ⟨2671505605018295469169355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124014946715454584451613 2671505605018295469169355)
              ·
                refine ⟨4007258407527443203754033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671505605018295469169355 4007258407527443203754033)
                ·
                  refine ⟨3005443805645582402815525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007258407527443203754033 3005443805645582402815525)
                  ·
                    refine ⟨563520713558546700527911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005443805645582402815525 563520713558546700527911)
                    ·
                      rfl

theorem cell22_1646179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_1646179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646179 prefixEnd_1646179 := by exact prefixLift 1646179
  have htrace : WordTrace (prefixWord ++ tailWord_1646179) baseStart_1646179 baseEnd_1646179 := by
    simpa [prefixWord, tailWord_1646179, baseEnd_1646179] using wordTrace_append hprefix tailTrace_1646179
  have hstable : (prefixWord ++ tailWord_1646179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646179).length < 2 ^ (prefixWord ++ tailWord_1646179).sum := by decide
  have hdescent : baseEnd_1646179 < baseStart_1646179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646198 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1646198 : Nat := 118140960795 + 1646198 * 2 ^ 59
def prefixEnd_1646198 : Nat := 4983230072969 + 3 ^ 40 * 1646198 * 2
def baseEnd_1646198 : Nat := 563527217646836984302853

theorem tailTrace_1646198 : CollatzResearch.WordTrace tailWord_1646198 prefixEnd_1646198 563527217646836984302853 := by
  unfold tailWord_1646198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752610855632079317509703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40027849126742179386770165 3752610855632079317509703)
  ·
    refine ⟨5628916283448118976264555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3752610855632079317509703 5628916283448118976264555)
    ·
      refine ⟨8443374425172178464396833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628916283448118976264555 8443374425172178464396833)
      ·
        refine ⟨6332530818879133848297625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8443374425172178464396833 6332530818879133848297625)
        ·
          refine ⟨4749398114159350386223219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6332530818879133848297625 4749398114159350386223219)
          ·
            refine ⟨7124097171239025579334829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749398114159350386223219 7124097171239025579334829)
            ·
              refine ⟨2671536439214634592250561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124097171239025579334829 2671536439214634592250561)
              ·
                refine ⟨2003652329410975944187921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671536439214634592250561 2003652329410975944187921)
                ·
                  refine ⟨1502739247058231958140941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003652329410975944187921 1502739247058231958140941)
                  ·
                    refine ⟨563527217646836984302853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502739247058231958140941 563527217646836984302853)
                    ·
                      rfl

theorem cell22_1646198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1646198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646198 prefixEnd_1646198 := by exact prefixLift 1646198
  have htrace : WordTrace (prefixWord ++ tailWord_1646198) baseStart_1646198 baseEnd_1646198 := by
    simpa [prefixWord, tailWord_1646198, baseEnd_1646198] using wordTrace_append hprefix tailTrace_1646198
  have hstable : (prefixWord ++ tailWord_1646198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646198).length < 2 ^ (prefixWord ++ tailWord_1646198).sum := by decide
  have hdescent : baseEnd_1646198 < baseStart_1646198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646228 : List Nat := [2, 4, 2, 2, 2, 2, 2, 6]
def baseStart_1646228 : Nat := 118140960795 + 1646228 * 2 ^ 59
def prefixEnd_1646228 : Nat := 4983230072969 + 3 ^ 40 * 1646228 * 2
def baseEnd_1646228 : Nat := 62615276362214100672529

theorem tailTrace_1646228 : CollatzResearch.WordTrace tailWord_1646228 prefixEnd_1646228 62615276362214100672529 := by
  unfold tailWord_1646228
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021433940002292101873669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40028578586669722802498225 30021433940002292101873669)
  ·
    refine ⟨5629018863750429769101313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30021433940002292101873669 5629018863750429769101313)
    ·
      refine ⟨4221764147812822326825985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5629018863750429769101313 4221764147812822326825985)
      ·
        refine ⟨3166323110859616745119489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4221764147812822326825985 3166323110859616745119489)
        ·
          refine ⟨2374742333144712558839617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3166323110859616745119489 2374742333144712558839617)
          ·
            refine ⟨1781056749858534419129713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374742333144712558839617 1781056749858534419129713)
            ·
              refine ⟨1335792562393900814347285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781056749858534419129713 1335792562393900814347285)
              ·
                refine ⟨62615276362214100672529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1335792562393900814347285 62615276362214100672529)
                ·
                  rfl

theorem cell22_1646228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_1646228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646228 prefixEnd_1646228 := by exact prefixLift 1646228
  have htrace : WordTrace (prefixWord ++ tailWord_1646228) baseStart_1646228 baseEnd_1646228 := by
    simpa [prefixWord, tailWord_1646228, baseEnd_1646228] using wordTrace_append hprefix tailTrace_1646228
  have hstable : (prefixWord ++ tailWord_1646228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646228).length < 2 ^ (prefixWord ++ tailWord_1646228).sum := by decide
  have hdescent : baseEnd_1646228 < baseStart_1646228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646269 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1646269 : Nat := 118140960795 + 1646269 * 2 ^ 59
def prefixEnd_1646269 : Nat := 4983230072969 + 3 ^ 40 * 1646269 * 2
def baseEnd_1646269 : Nat := 563551522397816465777635

theorem tailTrace_1646269 : CollatzResearch.WordTrace tailWord_1646269 prefixEnd_1646269 563551522397816465777635 := by
  unfold tailWord_1646269
  simp only [CollatzResearch.WordTrace]
  refine ⟨60044363272856048205989861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40029575515237365470659907 60044363272856048205989861)
  ·
    refine ⟨11258318113660509038623099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60044363272856048205989861 11258318113660509038623099)
    ·
      refine ⟨16887477170490763557934649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11258318113660509038623099 16887477170490763557934649)
      ·
        refine ⟨12665607877868072668450987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16887477170490763557934649 12665607877868072668450987)
        ·
          refine ⟨18998411816802109002676481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12665607877868072668450987 18998411816802109002676481)
          ·
            refine ⟨14248808862601581752007361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18998411816802109002676481 14248808862601581752007361)
            ·
              refine ⟨10686606646951186314005521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248808862601581752007361 10686606646951186314005521)
              ·
                refine ⟨8014954985213389735504141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10686606646951186314005521 8014954985213389735504141)
                ·
                  refine ⟨3005608119455021150814053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8014954985213389735504141 3005608119455021150814053)
                  ·
                    refine ⟨563551522397816465777635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3005608119455021150814053 563551522397816465777635)
                    ·
                      rfl

theorem cell22_1646269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1646269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646269 prefixEnd_1646269 := by exact prefixLift 1646269
  have htrace : WordTrace (prefixWord ++ tailWord_1646269) baseStart_1646269 baseEnd_1646269 := by
    simpa [prefixWord, tailWord_1646269, baseEnd_1646269] using wordTrace_append hprefix tailTrace_1646269
  have hstable : (prefixWord ++ tailWord_1646269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646269).length < 2 ^ (prefixWord ++ tailWord_1646269).sum := by decide
  have hdescent : baseEnd_1646269 < baseStart_1646269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646316 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1646316 : Nat := 118140960795 + 1646316 * 2 ^ 59
def prefixEnd_1646316 : Nat := 4983230072969 + 3 ^ 40 * 1646316 * 2
def baseEnd_1646316 : Nat := 563567611458324009852491

theorem tailTrace_1646316 : CollatzResearch.WordTrace tailWord_1646316 prefixEnd_1646316 563567611458324009852491 := by
  unfold tailWord_1646316
  simp only [CollatzResearch.WordTrace]
  refine ⟨30023038751842887616475401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40030718335790516821967201 30023038751842887616475401)
  ·
    refine ⟨22517279063882165712356551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30023038751842887616475401 22517279063882165712356551)
    ·
      refine ⟨33775918595823248568534827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22517279063882165712356551 33775918595823248568534827)
      ·
        refine ⟨50663877893734872852802241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33775918595823248568534827 50663877893734872852802241)
        ·
          refine ⟨37997908420301154639601681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50663877893734872852802241 37997908420301154639601681)
          ·
            refine ⟨28498431315225865979701261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37997908420301154639601681 28498431315225865979701261)
            ·
              refine ⟨10686911743209699742387973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28498431315225865979701261 10686911743209699742387973)
              ·
                refine ⟨2003795951851818701697745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10686911743209699742387973 2003795951851818701697745)
                ·
                  refine ⟨1502846963888864026273309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003795951851818701697745 1502846963888864026273309)
                  ·
                    refine ⟨563567611458324009852491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502846963888864026273309 563567611458324009852491)
                    ·
                      rfl

theorem cell22_1646316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1646316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646316 prefixEnd_1646316 := by exact prefixLift 1646316
  have htrace : WordTrace (prefixWord ++ tailWord_1646316) baseStart_1646316 baseEnd_1646316 := by
    simpa [prefixWord, tailWord_1646316, baseEnd_1646316] using wordTrace_append hprefix tailTrace_1646316
  have hstable : (prefixWord ++ tailWord_1646316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646316).length < 2 ^ (prefixWord ++ tailWord_1646316).sum := by decide
  have hdescent : baseEnd_1646316 < baseStart_1646316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646346 : List Nat := [3, 1, 2, 2, 1, 4, 3, 6]
def baseStart_1646346 : Nat := 118140960795 + 1646346 * 2 ^ 59
def prefixEnd_1646346 : Nat := 4983230072969 + 3 ^ 40 * 1646346 * 2
def baseEnd_1646346 : Nat := 62619764563490436844711

theorem tailTrace_1646346 : CollatzResearch.WordTrace tailWord_1646346 prefixEnd_1646346 62619764563490436844711 := by
  unfold tailWord_1646346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15011792923394272589135723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40031447795718060237695261 15011792923394272589135723)
  ·
    refine ⟨22517689385091408883703585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15011792923394272589135723 22517689385091408883703585)
    ·
      refine ⟨16888267038818556662777689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22517689385091408883703585 16888267038818556662777689)
      ·
        refine ⟨12666200279113917497083267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16888267038818556662777689 12666200279113917497083267)
        ·
          refine ⟨18999300418670876245624901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12666200279113917497083267 18999300418670876245624901)
          ·
            refine ⟨3562368828500789296054669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18999300418670876245624901 3562368828500789296054669)
            ·
              refine ⟨1335888310687795986020501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3562368828500789296054669 1335888310687795986020501)
              ·
                refine ⟨62619764563490436844711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1335888310687795986020501 62619764563490436844711)
                ·
                  rfl

theorem cell22_1646346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_1646346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646346 prefixEnd_1646346 := by exact prefixLift 1646346
  have htrace : WordTrace (prefixWord ++ tailWord_1646346) baseStart_1646346 baseEnd_1646346 := by
    simpa [prefixWord, tailWord_1646346, baseEnd_1646346] using wordTrace_append hprefix tailTrace_1646346
  have hstable : (prefixWord ++ tailWord_1646346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646346).length < 2 ^ (prefixWord ++ tailWord_1646346).sum := by decide
  have hdescent : baseEnd_1646346 < baseStart_1646346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646412 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_1646412 : Nat := 118140960795 + 1646412 * 2 ^ 59
def prefixEnd_1646412 : Nat := 4983230072969 + 3 ^ 40 * 1646412 * 2
def baseEnd_1646412 : Nat := 563600474220211759452197

theorem tailTrace_1646412 : CollatzResearch.WordTrace tailWord_1646412 prefixEnd_1646412 563600474220211759452197 := by
  unfold tailWord_1646412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30024789455668991814222745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40033052607558655752296993 30024789455668991814222745)
  ·
    refine ⟨22518592091751743860667059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30024789455668991814222745 22518592091751743860667059)
    ·
      refine ⟨33777888137627615791000589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22518592091751743860667059 33777888137627615791000589)
      ·
        refine ⟨12666708051610355921625221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33777888137627615791000589 12666708051610355921625221)
        ·
          refine ⟨2375007759676941735304729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12666708051610355921625221 2375007759676941735304729)
          ·
            refine ⟨1781255819757706301478547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375007759676941735304729 1781255819757706301478547)
            ·
              refine ⟨2671883729636559452217821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781255819757706301478547 2671883729636559452217821)
              ·
                refine ⟨1001956398613709794581683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2671883729636559452217821 1001956398613709794581683)
                ·
                  refine ⟨1502934597920564691872525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001956398613709794581683 1502934597920564691872525)
                  ·
                    refine ⟨563600474220211759452197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502934597920564691872525 563600474220211759452197)
                    ·
                      rfl

theorem cell22_1646412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_1646412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646412 prefixEnd_1646412 := by exact prefixLift 1646412
  have htrace : WordTrace (prefixWord ++ tailWord_1646412) baseStart_1646412 baseEnd_1646412 := by
    simpa [prefixWord, tailWord_1646412, baseEnd_1646412] using wordTrace_append hprefix tailTrace_1646412
  have hstable : (prefixWord ++ tailWord_1646412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646412).length < 2 ^ (prefixWord ++ tailWord_1646412).sum := by decide
  have hdescent : baseEnd_1646412 < baseStart_1646412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646442 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_1646442 : Nat := 118140960795 + 1646442 * 2 ^ 59
def prefixEnd_1646442 : Nat := 4983230072969 + 3 ^ 40 * 1646442 * 2
def baseEnd_1646442 : Nat := 187870247944433893734035

theorem tailTrace_1646442 : CollatzResearch.WordTrace tailWord_1646442 prefixEnd_1646442 187870247944433893734035 := by
  unfold tailWord_1646442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012668275307324688009395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40033782067486199168025053 15012668275307324688009395)
  ·
    refine ⟨22519002412960987032014093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15012668275307324688009395 22519002412960987032014093)
    ·
      refine ⟨8444625904860370137005285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22519002412960987032014093 8444625904860370137005285)
      ·
        refine ⟨1583367357161319400688491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8444625904860370137005285 1583367357161319400688491)
        ·
          refine ⟨2375051035741979101032737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583367357161319400688491 2375051035741979101032737)
          ·
            refine ⟨1781288276806484325774553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375051035741979101032737 1781288276806484325774553)
            ·
              refine ⟨1335966207604863244330915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781288276806484325774553 1335966207604863244330915)
              ·
                refine ⟨2003949311407294866496373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335966207604863244330915 2003949311407294866496373)
                ·
                  refine ⟨187870247944433893734035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2003949311407294866496373 187870247944433893734035)
                  ·
                    rfl

theorem cell22_1646442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_1646442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646442 prefixEnd_1646442 := by exact prefixLift 1646442
  have htrace : WordTrace (prefixWord ++ tailWord_1646442) baseStart_1646442 baseEnd_1646442 := by
    simpa [prefixWord, tailWord_1646442, baseEnd_1646442] using wordTrace_append hprefix tailTrace_1646442
  have hstable : (prefixWord ++ tailWord_1646442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646442).length < 2 ^ (prefixWord ++ tailWord_1646442).sum := by decide
  have hdescent : baseEnd_1646442 < baseStart_1646442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646464 : List Nat := [2, 1, 1, 2, 1, 2, 3, 10]
def baseStart_1646464 : Nat := 118140960795 + 1646464 * 2 ^ 59
def prefixEnd_1646464 : Nat := 4983230072969 + 3 ^ 40 * 1646464 * 2
def baseEnd_1646464 : Nat := 62624252764766773016893

theorem tailTrace_1646464 : CollatzResearch.WordTrace tailWord_1646464 prefixEnd_1646464 62624252764766773016893 := by
  unfold tailWord_1646464
  simp only [CollatzResearch.WordTrace]
  refine ⟨30025737753574798254669223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40034317004766397672892297 30025737753574798254669223)
  ·
    refine ⟨45038606630362197382003835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30025737753574798254669223 45038606630362197382003835)
    ·
      refine ⟨67557909945543296073005753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45038606630362197382003835 67557909945543296073005753)
      ·
        refine ⟨50668432459157472054754315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67557909945543296073005753 50668432459157472054754315)
        ·
          refine ⟨76002648688736208082131473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50668432459157472054754315 76002648688736208082131473)
          ·
            refine ⟨57001986516552156061598605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76002648688736208082131473 57001986516552156061598605)
            ·
              refine ⟨21375744943707058523099477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57001986516552156061598605 21375744943707058523099477)
              ·
                refine ⟨62624252764766773016893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21375744943707058523099477 62624252764766773016893)
                ·
                  rfl

theorem cell22_1646464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_1646464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646464 prefixEnd_1646464 := by exact prefixLift 1646464
  have htrace : WordTrace (prefixWord ++ tailWord_1646464) baseStart_1646464 baseEnd_1646464 := by
    simpa [prefixWord, tailWord_1646464, baseEnd_1646464] using wordTrace_append hprefix tailTrace_1646464
  have hstable : (prefixWord ++ tailWord_1646464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646464).length < 2 ^ (prefixWord ++ tailWord_1646464).sum := by decide
  have hdescent : baseEnd_1646464 < baseStart_1646464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646479 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_1646479 : Nat := 118140960795 + 1646479 * 2 ^ 59
def prefixEnd_1646479 : Nat := 4983230072969 + 3 ^ 40 * 1646479 * 2
def baseEnd_1646479 : Nat := 563623409689445918026991

theorem tailTrace_1646479 : CollatzResearch.WordTrace tailWord_1646479 prefixEnd_1646479 563623409689445918026991 := by
  unfold tailWord_1646479
  simp only [CollatzResearch.WordTrace]
  refine ⟨60052022602095254071134491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40034681734730169380756327 60052022602095254071134491)
  ·
    refine ⟨90078033903142881106701737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60052022602095254071134491 90078033903142881106701737)
    ·
      refine ⟨67558525427357160830026303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90078033903142881106701737 67558525427357160830026303)
      ·
        refine ⟨101337788141035741245039455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67558525427357160830026303 101337788141035741245039455)
        ·
          refine ⟨152006682211553611867559183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101337788141035741245039455 152006682211553611867559183)
          ·
            refine ⟨228010023317330417801338775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152006682211553611867559183 228010023317330417801338775)
            ·
              refine ⟨342015034975995626702008163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228010023317330417801338775 342015034975995626702008163)
              ·
                refine ⟨513022552463993440053012245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342015034975995626702008163 513022552463993440053012245)
                ·
                  refine ⟨24047932146749692502484949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 513022552463993440053012245 24047932146749692502484949)
                  ·
                    refine ⟨563623409689445918026991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24047932146749692502484949 563623409689445918026991)
                    ·
                      rfl

theorem cell22_1646479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_1646479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646479 prefixEnd_1646479 := by exact prefixLift 1646479
  have htrace : WordTrace (prefixWord ++ tailWord_1646479) baseStart_1646479 baseEnd_1646479 := by
    simpa [prefixWord, tailWord_1646479, baseEnd_1646479] using wordTrace_append hprefix tailTrace_1646479
  have hstable : (prefixWord ++ tailWord_1646479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646479).length < 2 ^ (prefixWord ++ tailWord_1646479).sum := by decide
  have hdescent : baseEnd_1646479 < baseStart_1646479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646513 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_1646513 : Nat := 118140960795 + 1646513 * 2 ^ 59
def prefixEnd_1646513 : Nat := 4983230072969 + 3 ^ 40 * 1646513 * 2
def baseEnd_1646513 : Nat := 563635048584281162676887

theorem tailTrace_1646513 : CollatzResearch.WordTrace tailWord_1646513 prefixEnd_1646513 563635048584281162676887 := by
  unfold tailWord_1646513
  simp only [CollatzResearch.WordTrace]
  refine ⟨60053262683972077877872193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40035508455981385251914795 60053262683972077877872193)
  ·
    refine ⟨45039947012979058408404145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60053262683972077877872193 45039947012979058408404145)
    ·
      refine ⟨33779960259734293806303109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45039947012979058408404145 33779960259734293806303109)
      ·
        refine ⟨6333742548700180088681833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33779960259734293806303109 6333742548700180088681833)
        ·
          refine ⟨4750306911525135066511375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6333742548700180088681833 4750306911525135066511375)
          ·
            refine ⟨7125460367287702599767063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750306911525135066511375 7125460367287702599767063)
            ·
              refine ⟨10688190550931553899650595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125460367287702599767063 10688190550931553899650595)
              ·
                refine ⟨16032285826397330849475893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10688190550931553899650595 16032285826397330849475893)
                ·
                  refine ⟨1503026796224749767138365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16032285826397330849475893 1503026796224749767138365)
                  ·
                    refine ⟨563635048584281162676887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503026796224749767138365 563635048584281162676887)
                    ·
                      rfl

theorem cell22_1646513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_1646513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646513 prefixEnd_1646513 := by exact prefixLift 1646513
  have htrace : WordTrace (prefixWord ++ tailWord_1646513) baseStart_1646513 baseEnd_1646513 := by
    simpa [prefixWord, tailWord_1646513, baseEnd_1646513] using wordTrace_append hprefix tailTrace_1646513
  have hstable : (prefixWord ++ tailWord_1646513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646513).length < 2 ^ (prefixWord ++ tailWord_1646513).sum := by decide
  have hdescent : baseEnd_1646513 < baseStart_1646513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646598 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1646598 : Nat := 118140960795 + 1646598 * 2 ^ 59
def prefixEnd_1646598 : Nat := 4983230072969 + 3 ^ 40 * 1646598 * 2
def baseEnd_1646598 : Nat := 563664145821369274301627

theorem tailTrace_1646598 : CollatzResearch.WordTrace tailWord_1646598 prefixEnd_1646598 563664145821369274301627 := by
  unfold tailWord_1646598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876761340270754293584889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40037575259109424929810965 1876761340270754293584889)
  ·
    refine ⟨1407571005203065720188667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1876761340270754293584889 1407571005203065720188667)
    ·
      refine ⟨2111356507804598580283001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407571005203065720188667 2111356507804598580283001)
      ·
        refine ⟨1583517380853448935212251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111356507804598580283001 1583517380853448935212251)
        ·
          refine ⟨2375276071280173402818377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583517380853448935212251 2375276071280173402818377)
          ·
            refine ⟨1781457053460130052113783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375276071280173402818377 1781457053460130052113783)
            ·
              refine ⟨2672185580190195078170675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781457053460130052113783 2672185580190195078170675)
              ·
                refine ⟨4008278370285292617256013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672185580190195078170675 4008278370285292617256013)
                ·
                  refine ⟨1503104388856984731471005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4008278370285292617256013 1503104388856984731471005)
                  ·
                    refine ⟨563664145821369274301627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503104388856984731471005 563664145821369274301627)
                    ·
                      rfl

theorem cell22_1646598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1646598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646598 prefixEnd_1646598 := by exact prefixLift 1646598
  have htrace : WordTrace (prefixWord ++ tailWord_1646598) baseStart_1646598 baseEnd_1646598 := by
    simpa [prefixWord, tailWord_1646598, baseEnd_1646598] using wordTrace_append hprefix tailTrace_1646598
  have hstable : (prefixWord ++ tailWord_1646598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646598).length < 2 ^ (prefixWord ++ tailWord_1646598).sum := by decide
  have hdescent : baseEnd_1646598 < baseStart_1646598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646603 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 4, 3]
def baseStart_1646603 : Nat := 118140960795 + 1646603 * 2 ^ 59
def prefixEnd_1646603 : Nat := 4983230072969 + 3 ^ 40 * 1646603 * 2
def baseEnd_1646603 : Nat := 563665857423550927926611

theorem tailTrace_1646603 : CollatzResearch.WordTrace tailWord_1646603 prefixEnd_1646603 563665857423550927926611 := by
  unfold tailWord_1646603
  simp only [CollatzResearch.WordTrace]
  refine ⟨60056545253646023248648463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40037696835764015499098975 60056545253646023248648463)
  ·
    refine ⟨90084817880469034872972695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60056545253646023248648463 90084817880469034872972695)
    ·
      refine ⟨135127226820703552309459043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90084817880469034872972695 135127226820703552309459043)
      ·
        refine ⟨202690840231055328464188565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135127226820703552309459043 202690840231055328464188565)
        ·
          refine ⟨9501133135830718521758839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202690840231055328464188565 9501133135830718521758839)
          ·
            refine ⟨14251699703746077782638259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501133135830718521758839 14251699703746077782638259)
            ·
              refine ⟨21377549555619116673957389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14251699703746077782638259 21377549555619116673957389)
              ·
                refine ⟨8016581083357168752734021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21377549555619116673957389 8016581083357168752734021)
                ·
                  refine ⟨1503108953129469141137629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8016581083357168752734021 1503108953129469141137629)
                  ·
                    refine ⟨563665857423550927926611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503108953129469141137629 563665857423550927926611)
                    ·
                      rfl

theorem cell22_1646603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3].length) (baseStart_1646603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646603 prefixEnd_1646603 := by exact prefixLift 1646603
  have htrace : WordTrace (prefixWord ++ tailWord_1646603) baseStart_1646603 baseEnd_1646603 := by
    simpa [prefixWord, tailWord_1646603, baseEnd_1646603] using wordTrace_append hprefix tailTrace_1646603
  have hstable : (prefixWord ++ tailWord_1646603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646603).length < 2 ^ (prefixWord ++ tailWord_1646603).sum := by decide
  have hdescent : baseEnd_1646603 < baseStart_1646603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646654 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1646654 : Nat := 118140960795 + 1646654 * 2 ^ 59
def prefixEnd_1646654 : Nat := 4983230072969 + 3 ^ 40 * 1646654 * 2
def baseEnd_1646654 : Nat := 563683315765803794901455

theorem tailTrace_1646654 : CollatzResearch.WordTrace tailWord_1646654 prefixEnd_1646654 563683315765803794901455 := by
  unfold tailWord_1646654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507300672057657369844377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40038936917640839305836677 7507300672057657369844377)
  ·
    refine ⟨5630475504043243027383283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7507300672057657369844377 5630475504043243027383283)
    ·
      refine ⟨8445713256064864541074925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5630475504043243027383283 8445713256064864541074925)
      ·
        refine ⟨3167142471024324202903097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8445713256064864541074925 3167142471024324202903097)
        ·
          refine ⟨2375356853268243152177323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167142471024324202903097 2375356853268243152177323)
          ·
            refine ⟨3563035279902364728265985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375356853268243152177323 3563035279902364728265985)
            ·
              refine ⟨2672276459926773546199489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563035279902364728265985 2672276459926773546199489)
              ·
                refine ⟨2004207344945080159649617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2672276459926773546199489 2004207344945080159649617)
                ·
                  refine ⟨1503155508708810119737213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004207344945080159649617 1503155508708810119737213)
                  ·
                    refine ⟨563683315765803794901455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503155508708810119737213 563683315765803794901455)
                    ·
                      rfl

theorem cell22_1646654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1646654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646654 prefixEnd_1646654 := by exact prefixLift 1646654
  have htrace : WordTrace (prefixWord ++ tailWord_1646654) baseStart_1646654 baseEnd_1646654 := by
    simpa [prefixWord, tailWord_1646654, baseEnd_1646654] using wordTrace_append hprefix tailTrace_1646654
  have hstable : (prefixWord ++ tailWord_1646654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646654).length < 2 ^ (prefixWord ++ tailWord_1646654).sum := by decide
  have hdescent : baseEnd_1646654 < baseStart_1646654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646686 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1646686 : Nat := 118140960795 + 1646686 * 2 ^ 59
def prefixEnd_1646686 : Nat := 4983230072969 + 3 ^ 40 * 1646686 * 2
def baseEnd_1646686 : Nat := 563694270019766378101357

theorem tailTrace_1646686 : CollatzResearch.WordTrace tailWord_1646686 prefixEnd_1646686 563694270019766378101357 := by
  unfold tailWord_1646686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507446564043166052989989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40039715008230218949279941 7507446564043166052989989)
  ·
    refine ⟨1407646230758093634935623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7507446564043166052989989 1407646230758093634935623)
    ·
      refine ⟨2111469346137140452403435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407646230758093634935623 2111469346137140452403435)
      ·
        refine ⟨3167204019205710678605153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111469346137140452403435 3167204019205710678605153)
        ·
          refine ⟨2375403014404283008953865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167204019205710678605153 2375403014404283008953865)
          ·
            refine ⟨1781552260803212256715399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375403014404283008953865 1781552260803212256715399)
            ·
              refine ⟨2672328391204818385073099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781552260803212256715399 2672328391204818385073099)
              ·
                refine ⟨4008492586807227577609649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672328391204818385073099 4008492586807227577609649)
                ·
                  refine ⟨3006369440105420683207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008492586807227577609649 3006369440105420683207237)
                  ·
                    refine ⟨563694270019766378101357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006369440105420683207237 563694270019766378101357)
                    ·
                      rfl

theorem cell22_1646686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1646686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646686 prefixEnd_1646686 := by exact prefixLift 1646686
  have htrace : WordTrace (prefixWord ++ tailWord_1646686) baseStart_1646686 baseEnd_1646686 := by
    simpa [prefixWord, tailWord_1646686, baseEnd_1646686] using wordTrace_append hprefix tailTrace_1646686
  have hstable : (prefixWord ++ tailWord_1646686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646686).length < 2 ^ (prefixWord ++ tailWord_1646686).sum := by decide
  have hdescent : baseEnd_1646686 < baseStart_1646686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646710 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1646710 : Nat := 118140960795 + 1646710 * 2 ^ 59
def prefixEnd_1646710 : Nat := 4983230072969 + 3 ^ 40 * 1646710 * 2
def baseEnd_1646710 : Nat := 563702485710238315501283

theorem tailTrace_1646710 : CollatzResearch.WordTrace tailWord_1646710 prefixEnd_1646710 563702485710238315501283 := by
  unfold tailWord_1646710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753777991516148782674599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40040298576172253681862389 3753777991516148782674599)
  ·
    refine ⟨5630666987274223174011899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3753777991516148782674599 5630666987274223174011899)
    ·
      refine ⟨8446000480911334761017849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5630666987274223174011899 8446000480911334761017849)
      ·
        refine ⟨6334500360683501070763387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8446000480911334761017849 6334500360683501070763387)
        ·
          refine ⟨9501750541025251606145081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334500360683501070763387 9501750541025251606145081)
          ·
            refine ⟨7126312905768938704608811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501750541025251606145081 7126312905768938704608811)
            ·
              refine ⟨10689469358653408056913217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126312905768938704608811 10689469358653408056913217)
              ·
                refine ⟨8017102018990056042684913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10689469358653408056913217 8017102018990056042684913)
                ·
                  refine ⟨6012826514242542032013685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8017102018990056042684913 6012826514242542032013685)
                  ·
                    refine ⟨563702485710238315501283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6012826514242542032013685 563702485710238315501283)
                    ·
                      rfl

theorem cell22_1646710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1646710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646710 prefixEnd_1646710 := by exact prefixLift 1646710
  have htrace : WordTrace (prefixWord ++ tailWord_1646710) baseStart_1646710 baseEnd_1646710 := by
    simpa [prefixWord, tailWord_1646710, baseEnd_1646710] using wordTrace_append hprefix tailTrace_1646710
  have hstable : (prefixWord ++ tailWord_1646710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646710).length < 2 ^ (prefixWord ++ tailWord_1646710).sum := by decide
  have hdescent : baseEnd_1646710 < baseStart_1646710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646723 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 6]
def baseStart_1646723 : Nat := 118140960795 + 1646723 * 2 ^ 59
def prefixEnd_1646723 : Nat := 4983230072969 + 3 ^ 40 * 1646723 * 2
def baseEnd_1646723 : Nat := 187902311958636871642081

theorem tailTrace_1646723 : CollatzResearch.WordTrace tailWord_1646723 prefixEnd_1646723 187902311958636871642081 := by
  unfold tailWord_1646723
  simp only [CollatzResearch.WordTrace]
  refine ⟨60060922013211283743016823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40040614675474189162011215 60060922013211283743016823)
  ·
    refine ⟨90091383019816925614525235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60060922013211283743016823 90091383019816925614525235)
    ·
      refine ⟨135137074529725388421787853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90091383019816925614525235 135137074529725388421787853)
      ·
        refine ⟨50676402948647020658170445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135137074529725388421787853 50676402948647020658170445)
        ·
          refine ⟨19003651105742632746813917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50676402948647020658170445 19003651105742632746813917)
          ·
            refine ⟨7126369164653487280055219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19003651105742632746813917 7126369164653487280055219)
            ·
              refine ⟨10689553746980230920082829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126369164653487280055219 10689553746980230920082829)
              ·
                refine ⟨4008582655117586595031061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10689553746980230920082829 4008582655117586595031061)
                ·
                  refine ⟨187902311958636871642081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4008582655117586595031061 187902311958636871642081)
                  ·
                    rfl

theorem cell22_1646723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_1646723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646723 prefixEnd_1646723 := by exact prefixLift 1646723
  have htrace : WordTrace (prefixWord ++ tailWord_1646723) baseStart_1646723 baseEnd_1646723 := by
    simpa [prefixWord, tailWord_1646723, baseEnd_1646723] using wordTrace_append hprefix tailTrace_1646723
  have hstable : (prefixWord ++ tailWord_1646723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646723).length < 2 ^ (prefixWord ++ tailWord_1646723).sum := by decide
  have hdescent : baseEnd_1646723 < baseStart_1646723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646770 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1646770 : Nat := 118140960795 + 1646770 * 2 ^ 59
def prefixEnd_1646770 : Nat := 4983230072969 + 3 ^ 40 * 1646770 * 2
def baseEnd_1646770 : Nat := 563723024936418159001099

theorem tailTrace_1646770 : CollatzResearch.WordTrace tailWord_1646770 prefixEnd_1646770 563723024936418159001099 := by
  unfold tailWord_1646770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015659061010252692494441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40041757496027340513318509 15015659061010252692494441)
  ·
    refine ⟨11261744295757689519370831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15015659061010252692494441 11261744295757689519370831)
    ·
      refine ⟨16892616443636534279056247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11261744295757689519370831 16892616443636534279056247)
      ·
        refine ⟨25338924665454801418584371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16892616443636534279056247 25338924665454801418584371)
        ·
          refine ⟨38008386998182202127876557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25338924665454801418584371 38008386998182202127876557)
          ·
            refine ⟨14253145124318325797953709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38008386998182202127876557 14253145124318325797953709)
            ·
              refine ⟨5344929421619372174232641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14253145124318325797953709 5344929421619372174232641)
              ·
                refine ⟨4008697066214529130674481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344929421619372174232641 4008697066214529130674481)
                ·
                  refine ⟨3006522799660896848005861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008697066214529130674481 3006522799660896848005861)
                  ·
                    refine ⟨563723024936418159001099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006522799660896848005861 563723024936418159001099)
                    ·
                      rfl

theorem cell22_1646770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1646770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646770 prefixEnd_1646770 := by exact prefixLift 1646770
  have htrace : WordTrace (prefixWord ++ tailWord_1646770) baseStart_1646770 baseEnd_1646770 := by
    simpa [prefixWord, tailWord_1646770, baseEnd_1646770] using wordTrace_append hprefix tailTrace_1646770
  have hstable : (prefixWord ++ tailWord_1646770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646770).length < 2 ^ (prefixWord ++ tailWord_1646770).sum := by decide
  have hdescent : baseEnd_1646770 < baseStart_1646770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646860 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1646860 : Nat := 118140960795 + 1646860 * 2 ^ 59
def prefixEnd_1646860 : Nat := 4983230072969 + 3 ^ 40 * 1646860 * 2
def baseEnd_1646860 : Nat := 563753833775687924250823

theorem tailTrace_1646860 : CollatzResearch.WordTrace tailWord_1646860 prefixEnd_1646860 563753833775687924250823 := by
  unfold tailWord_1646860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30032959406857478070377017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40043945875809970760502689 30032959406857478070377017)
  ·
    refine ⟨22524719555143108552782763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30032959406857478070377017 22524719555143108552782763)
    ·
      refine ⟨33787079332714662829174145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524719555143108552782763 33787079332714662829174145)
      ·
        refine ⟨25340309499535997121880609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33787079332714662829174145 25340309499535997121880609)
        ·
          refine ⟨19005232124651997841410457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25340309499535997121880609 19005232124651997841410457)
          ·
            refine ⟨14253924093488998381057843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19005232124651997841410457 14253924093488998381057843)
            ·
              refine ⟨21380886140233497571586765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14253924093488998381057843 21380886140233497571586765)
              ·
                refine ⟨8017832302587561589345037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21380886140233497571586765 8017832302587561589345037)
                ·
                  refine ⟨3006687113470335596004389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8017832302587561589345037 3006687113470335596004389)
                  ·
                    refine ⟨563753833775687924250823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006687113470335596004389 563753833775687924250823)
                    ·
                      rfl

theorem cell22_1646860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1646860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646860 prefixEnd_1646860 := by exact prefixLift 1646860
  have htrace : WordTrace (prefixWord ++ tailWord_1646860) baseStart_1646860 baseEnd_1646860 := by
    simpa [prefixWord, tailWord_1646860, baseEnd_1646860] using wordTrace_append hprefix tailTrace_1646860
  have hstable : (prefixWord ++ tailWord_1646860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646860).length < 2 ^ (prefixWord ++ tailWord_1646860).sum := by decide
  have hdescent : baseEnd_1646860 < baseStart_1646860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646892 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_1646892 : Nat := 118140960795 + 1646892 * 2 ^ 59
def prefixEnd_1646892 : Nat := 4983230072969 + 3 ^ 40 * 1646892 * 2
def baseEnd_1646892 : Nat := 187921596009883502483575

theorem tailTrace_1646892 : CollatzResearch.WordTrace tailWord_1646892 prefixEnd_1646892 187921596009883502483575 := by
  unfold tailWord_1646892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30033542974799512802959465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40044723966399350403945953 30033542974799512802959465)
  ·
    refine ⟨22525157231099634602219599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30033542974799512802959465 22525157231099634602219599)
    ·
      refine ⟨33787735846649451903329399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22525157231099634602219599 33787735846649451903329399)
      ·
        refine ⟨50681603769974177854994099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33787735846649451903329399 50681603769974177854994099)
        ·
          refine ⟨76022405654961266782491149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50681603769974177854994099 76022405654961266782491149)
          ·
            refine ⟨28508402120610475043434181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76022405654961266782491149 28508402120610475043434181)
            ·
              refine ⟨5345325397614464070643909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28508402120610475043434181 5345325397614464070643909)
              ·
                refine ⟨1002248512052712013245733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5345325397614464070643909 1002248512052712013245733)
                ·
                  refine ⟨187921596009883502483575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002248512052712013245733 187921596009883502483575)
                  ·
                    rfl

theorem cell22_1646892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_1646892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1646892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1646892 prefixEnd_1646892 := by exact prefixLift 1646892
  have htrace : WordTrace (prefixWord ++ tailWord_1646892) baseStart_1646892 baseEnd_1646892 := by
    simpa [prefixWord, tailWord_1646892, baseEnd_1646892] using wordTrace_append hprefix tailTrace_1646892
  have hstable : (prefixWord ++ tailWord_1646892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646892).length < 2 ^ (prefixWord ++ tailWord_1646892).sum := by decide
  have hdescent : baseEnd_1646892 < baseStart_1646892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647012 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1647012 : Nat := 118140960795 + 1647012 * 2 ^ 59
def prefixEnd_1647012 : Nat := 4983230072969 + 3 ^ 40 * 1647012 * 2
def baseEnd_1647012 : Nat := 563805866482010194450357

theorem tailTrace_1647012 : CollatzResearch.WordTrace tailWord_1647012 prefixEnd_1647012 563805866482010194450357 := by
  unfold tailWord_1647012
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035731354582143050143645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40047641806109524066858193 30035731354582143050143645)
  ·
    refine ⟨11263399257968303643803867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30035731354582143050143645 11263399257968303643803867)
    ·
      refine ⟨16895098886952455465705801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263399257968303643803867 16895098886952455465705801)
      ·
        refine ⟨12671324165214341599279351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16895098886952455465705801 12671324165214341599279351)
        ·
          refine ⟨19006986247821512398919027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12671324165214341599279351 19006986247821512398919027)
          ·
            refine ⟨28510479371732268598378541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19006986247821512398919027 28510479371732268598378541)
            ·
              refine ⟨10691429764399600724391953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28510479371732268598378541 10691429764399600724391953)
              ·
                refine ⟨8018572323299700543293965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10691429764399600724391953 8018572323299700543293965)
                ·
                  refine ⟨3006964621237387703735237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8018572323299700543293965 3006964621237387703735237)
                  ·
                    refine ⟨563805866482010194450357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006964621237387703735237 563805866482010194450357)
                    ·
                      rfl

theorem cell22_1647012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1647012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647012 prefixEnd_1647012 := by exact prefixLift 1647012
  have htrace : WordTrace (prefixWord ++ tailWord_1647012) baseStart_1647012 baseEnd_1647012 := by
    simpa [prefixWord, tailWord_1647012, baseEnd_1647012] using wordTrace_append hprefix tailTrace_1647012
  have hstable : (prefixWord ++ tailWord_1647012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647012).length < 2 ^ (prefixWord ++ tailWord_1647012).sum := by decide
  have hdescent : baseEnd_1647012 < baseStart_1647012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647057 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1647057 : Nat := 118140960795 + 1647057 * 2 ^ 59
def prefixEnd_1647057 : Nat := 4983230072969 + 3 ^ 40 * 1647057 * 2
def baseEnd_1647057 : Nat := 563821270901645077075219

theorem tailTrace_1647057 : CollatzResearch.WordTrace tailWord_1647057 prefixEnd_1647057 563821270901645077075219 := by
  unfold tailWord_1647057
  simp only [CollatzResearch.WordTrace]
  refine ⟨60073103994001258785675425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40048735996000839190450283 60073103994001258785675425)
  ·
    refine ⟨45054827995500944089256569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60073103994001258785675425 45054827995500944089256569)
    ·
      refine ⟨33791120996625708066942427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45054827995500944089256569 33791120996625708066942427)
      ·
        refine ⟨50686681494938562100413641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33791120996625708066942427 50686681494938562100413641)
        ·
          refine ⟨38015011121203921575310231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50686681494938562100413641 38015011121203921575310231)
          ·
            refine ⟨57022516681805882362965347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38015011121203921575310231 57022516681805882362965347)
            ·
              refine ⟨85533775022708823544448021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57022516681805882362965347 85533775022708823544448021)
              ·
                refine ⟨4009395704189476103646001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85533775022708823544448021 4009395704189476103646001)
                ·
                  refine ⟨3007046778142107077734501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4009395704189476103646001 3007046778142107077734501)
                  ·
                    refine ⟨563821270901645077075219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007046778142107077734501 563821270901645077075219)
                    ·
                      rfl

theorem cell22_1647057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1647057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647057 prefixEnd_1647057 := by exact prefixLift 1647057
  have htrace : WordTrace (prefixWord ++ tailWord_1647057) baseStart_1647057 baseEnd_1647057 := by
    simpa [prefixWord, tailWord_1647057, baseEnd_1647057] using wordTrace_append hprefix tailTrace_1647057
  have hstable : (prefixWord ++ tailWord_1647057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647057).length < 2 ^ (prefixWord ++ tailWord_1647057).sum := by decide
  have hdescent : baseEnd_1647057 < baseStart_1647057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647106 : List Nat := [3, 4, 1, 2, 2, 2, 8]
def baseStart_1647106 : Nat := 118140960795 + 1647106 * 2 ^ 59
def prefixEnd_1647106 : Nat := 4983230072969 + 3 ^ 40 * 1647106 * 2
def baseEnd_1647106 : Nat := 20882890540852788244447

theorem tailTrace_1647106 : CollatzResearch.WordTrace tailWord_1647106 prefixEnd_1647106 20882890540852788244447 := by
  unfold tailWord_1647106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15018722792705935038552293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40049927447215826769472781 15018722792705935038552293)
  ·
    refine ⟨2816010523632362819728555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15018722792705935038552293 2816010523632362819728555)
    ·
      refine ⟨4224015785448544229592833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816010523632362819728555 4224015785448544229592833)
      ·
        refine ⟨3168011839086408172194625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4224015785448544229592833 3168011839086408172194625)
        ·
          refine ⟨2376008879314806129145969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168011839086408172194625 2376008879314806129145969)
          ·
            refine ⟨1782006659486104596859477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376008879314806129145969 1782006659486104596859477)
            ·
              refine ⟨20882890540852788244447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1782006659486104596859477 20882890540852788244447)
              ·
                rfl

theorem cell22_1647106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 8].length) (baseStart_1647106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647106 prefixEnd_1647106 := by exact prefixLift 1647106
  have htrace : WordTrace (prefixWord ++ tailWord_1647106) baseStart_1647106 baseEnd_1647106 := by
    simpa [prefixWord, tailWord_1647106, baseEnd_1647106] using wordTrace_append hprefix tailTrace_1647106
  have hstable : (prefixWord ++ tailWord_1647106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647106).length < 2 ^ (prefixWord ++ tailWord_1647106).sum := by decide
  have hdescent : baseEnd_1647106 < baseStart_1647106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647110 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1647110 : Nat := 118140960795 + 1647110 * 2 ^ 59
def prefixEnd_1647110 : Nat := 4983230072969 + 3 ^ 40 * 1647110 * 2
def baseEnd_1647110 : Nat := 563839413884770605500057

theorem tailTrace_1647110 : CollatzResearch.WordTrace tailWord_1647110 prefixEnd_1647110 563839413884770605500057 := by
  unfold tailWord_1647110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877344908212789026167337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40050024708539499224903189 1877344908212789026167337)
  ·
    refine ⟨1408008681159591769625503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1877344908212789026167337 1408008681159591769625503)
    ·
      refine ⟨2112013021739387654438255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408008681159591769625503 2112013021739387654438255)
      ·
        refine ⟨3168019532609081481657383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112013021739387654438255 3168019532609081481657383)
        ·
          refine ⟨4752029298913622222486075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168019532609081481657383 4752029298913622222486075)
          ·
            refine ⟨7128043948370433333729113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752029298913622222486075 7128043948370433333729113)
            ·
              refine ⟨5346032961277825000296835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7128043948370433333729113 5346032961277825000296835)
              ·
                refine ⟨8019049441916737500445253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346032961277825000296835 8019049441916737500445253)
                ·
                  refine ⟨1503571770359388281333485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8019049441916737500445253 1503571770359388281333485)
                  ·
                    refine ⟨563839413884770605500057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503571770359388281333485 563839413884770605500057)
                    ·
                      rfl

theorem cell22_1647110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1647110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647110 prefixEnd_1647110 := by exact prefixLift 1647110
  have htrace : WordTrace (prefixWord ++ tailWord_1647110) baseStart_1647110 baseEnd_1647110 := by
    simpa [prefixWord, tailWord_1647110, baseEnd_1647110] using wordTrace_append hprefix tailTrace_1647110
  have hstable : (prefixWord ++ tailWord_1647110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647110).length < 2 ^ (prefixWord ++ tailWord_1647110).sum := by decide
  have hdescent : baseEnd_1647110 < baseStart_1647110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647127 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 2, 3]
def baseStart_1647127 : Nat := 118140960795 + 1647127 * 2 ^ 59
def prefixEnd_1647127 : Nat := 4983230072969 + 3 ^ 40 * 1647127 * 2
def baseEnd_1647127 : Nat := 563845233332188227825005

theorem tailTrace_1647127 : CollatzResearch.WordTrace tailWord_1647127 prefixEnd_1647127 563845233332188227825005 := by
  unfold tailWord_1647127
  simp only [CollatzResearch.WordTrace]
  refine ⟨60075657103747660740723635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40050438069165107160482423 60075657103747660740723635)
  ·
    refine ⟨90113485655621491111085453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60075657103747660740723635 90113485655621491111085453)
    ·
      refine ⟨33792557120858059166657045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90113485655621491111085453 33792557120858059166657045)
      ·
        refine ⟨1584026115040221523437049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33792557120858059166657045 1584026115040221523437049)
        ·
          refine ⟨1188019586280166142577787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584026115040221523437049 1188019586280166142577787)
          ·
            refine ⟨1782029379420249213866681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188019586280166142577787 1782029379420249213866681)
            ·
              refine ⟨1336522034565186910400011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1782029379420249213866681 1336522034565186910400011)
              ·
                refine ⟨2004783051847780365600017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336522034565186910400011 2004783051847780365600017)
                ·
                  refine ⟨1503587288885835274200013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004783051847780365600017 1503587288885835274200013)
                  ·
                    refine ⟨563845233332188227825005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503587288885835274200013 563845233332188227825005)
                    ·
                      rfl

theorem cell22_1647127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_1647127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647127 prefixEnd_1647127 := by exact prefixLift 1647127
  have htrace : WordTrace (prefixWord ++ tailWord_1647127) baseStart_1647127 baseEnd_1647127 := by
    simpa [prefixWord, tailWord_1647127, baseEnd_1647127] using wordTrace_append hprefix tailTrace_1647127
  have hstable : (prefixWord ++ tailWord_1647127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647127).length < 2 ^ (prefixWord ++ tailWord_1647127).sum := by decide
  have hdescent : baseEnd_1647127 < baseStart_1647127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647181 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1647181 : Nat := 118140960795 + 1647181 * 2 ^ 59
def prefixEnd_1647181 : Nat := 4983230072969 + 3 ^ 40 * 1647181 * 2
def baseEnd_1647181 : Nat := 563863718635750086974839

theorem tailTrace_1647181 : CollatzResearch.WordTrace tailWord_1647181 prefixEnd_1647181 563863718635750086974839 := by
  unfold tailWord_1647181
  simp only [CollatzResearch.WordTrace]
  refine ⟨60077626645552027963189397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40051751097034685308792931 60077626645552027963189397)
  ·
    refine ⟨2816138749010251310774503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60077626645552027963189397 2816138749010251310774503)
    ·
      refine ⟨4224208123515376966161755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816138749010251310774503 4224208123515376966161755)
      ·
        refine ⟨6336312185273065449242633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224208123515376966161755 6336312185273065449242633)
        ·
          refine ⟨4752234138954799086931975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6336312185273065449242633 4752234138954799086931975)
          ·
            refine ⟨7128351208432198630397963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752234138954799086931975 7128351208432198630397963)
            ·
              refine ⟨10692526812648297945596945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128351208432198630397963 10692526812648297945596945)
              ·
                refine ⟨8019395109486223459197709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10692526812648297945596945 8019395109486223459197709)
                ·
                  refine ⟨3007273166057333797199141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8019395109486223459197709 3007273166057333797199141)
                  ·
                    refine ⟨563863718635750086974839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007273166057333797199141 563863718635750086974839)
                    ·
                      rfl

theorem cell22_1647181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1647181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647181 prefixEnd_1647181 := by exact prefixLift 1647181
  have htrace : WordTrace (prefixWord ++ tailWord_1647181) baseStart_1647181 baseEnd_1647181 := by
    simpa [prefixWord, tailWord_1647181, baseEnd_1647181] using wordTrace_append hprefix tailTrace_1647181
  have hstable : (prefixWord ++ tailWord_1647181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647181).length < 2 ^ (prefixWord ++ tailWord_1647181).sum := by decide
  have hdescent : baseEnd_1647181 < baseStart_1647181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647194 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_1647194 : Nat := 118140960795 + 1647194 * 2 ^ 59
def prefixEnd_1647194 : Nat := 4983230072969 + 3 ^ 40 * 1647194 * 2
def baseEnd_1647194 : Nat := 563868168801422386399799

theorem tailTrace_1647194 : CollatzResearch.WordTrace tailWord_1647194 prefixEnd_1647194 563868168801422386399799 := by
  unfold tailWord_1647194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019525198626232795853159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40052067196336620788941757 15019525198626232795853159)
  ·
    refine ⟨22529287797939349193779739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15019525198626232795853159 22529287797939349193779739)
    ·
      refine ⟨33793931696909023790669609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22529287797939349193779739 33793931696909023790669609)
      ·
        refine ⟨25345448772681767843002207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33793931696909023790669609 25345448772681767843002207)
        ·
          refine ⟨38018173159022651764503311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25345448772681767843002207 38018173159022651764503311)
          ·
            refine ⟨57027259738533977646754967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38018173159022651764503311 57027259738533977646754967)
            ·
              refine ⟨85540889607800966470132451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57027259738533977646754967 85540889607800966470132451)
              ·
                refine ⟨128311334411701449705198677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85540889607800966470132451 128311334411701449705198677)
                ·
                  refine ⟨1503648450137126363732797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 128311334411701449705198677 1503648450137126363732797)
                  ·
                    refine ⟨563868168801422386399799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503648450137126363732797 563868168801422386399799)
                    ·
                      rfl

theorem cell22_1647194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_1647194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647194 prefixEnd_1647194 := by exact prefixLift 1647194
  have htrace : WordTrace (prefixWord ++ tailWord_1647194) baseStart_1647194 baseEnd_1647194 := by
    simpa [prefixWord, tailWord_1647194, baseEnd_1647194] using wordTrace_append hprefix tailTrace_1647194
  have hstable : (prefixWord ++ tailWord_1647194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647194).length < 2 ^ (prefixWord ++ tailWord_1647194).sum := by decide
  have hdescent : baseEnd_1647194 < baseStart_1647194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647196 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1647196 : Nat := 118140960795 + 1647196 * 2 ^ 59
def prefixEnd_1647196 : Nat := 4983230072969 + 3 ^ 40 * 1647196 * 2
def baseEnd_1647196 : Nat := 187956284480765015949931

theorem tailTrace_1647196 : CollatzResearch.WordTrace tailWord_1647196 prefixEnd_1647196 187956284480765015949931 := by
  unfold tailWord_1647196
  simp only [CollatzResearch.WordTrace]
  refine ⟨30039086870248842762492721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40052115826998457016656961 30039086870248842762492721)
  ·
    refine ⟨22529315152686632071869541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30039086870248842762492721 22529315152686632071869541)
    ·
      refine ⟨4224246591128743513475539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22529315152686632071869541 4224246591128743513475539)
      ·
        refine ⟨6336369886693115270213309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224246591128743513475539 6336369886693115270213309)
        ·
          refine ⟨2376138707509918226329991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6336369886693115270213309 2376138707509918226329991)
          ·
            refine ⟨3564208061264877339494987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376138707509918226329991 3564208061264877339494987)
            ·
              refine ⟨5346312091897316009242481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564208061264877339494987 5346312091897316009242481)
              ·
                refine ⟨4009734068922987006931861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346312091897316009242481 4009734068922987006931861)
                ·
                  refine ⟨187956284480765015949931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4009734068922987006931861 187956284480765015949931)
                  ·
                    rfl

theorem cell22_1647196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1647196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647196 prefixEnd_1647196 := by exact prefixLift 1647196
  have htrace : WordTrace (prefixWord ++ tailWord_1647196) baseStart_1647196 baseEnd_1647196 := by
    simpa [prefixWord, tailWord_1647196, baseEnd_1647196] using wordTrace_append hprefix tailTrace_1647196
  have hstable : (prefixWord ++ tailWord_1647196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647196).length < 2 ^ (prefixWord ++ tailWord_1647196).sum := by decide
  have hdescent : baseEnd_1647196 < baseStart_1647196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647213 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1647213 : Nat := 118140960795 + 1647213 * 2 ^ 59
def prefixEnd_1647213 : Nat := 4983230072969 + 3 ^ 40 * 1647213 * 2
def baseEnd_1647213 : Nat := 187958224296570890058247

theorem tailTrace_1647213 : CollatzResearch.WordTrace tailWord_1647213 prefixEnd_1647213 187958224296570890058247 := by
  unfold tailWord_1647213
  simp only [CollatzResearch.WordTrace]
  refine ⟨60078793781436097428354293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40052529187624064952236195 60078793781436097428354293)
  ·
    refine ⟨5632386917009634133908215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60078793781436097428354293 5632386917009634133908215)
    ·
      refine ⟨8448580375514451200862323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632386917009634133908215 8448580375514451200862323)
      ·
        refine ⟨12672870563271676801293485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8448580375514451200862323 12672870563271676801293485)
        ·
          refine ⟨4752326461226878800485057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12672870563271676801293485 4752326461226878800485057)
          ·
            refine ⟨3564244845920159100363793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752326461226878800485057 3564244845920159100363793)
            ·
              refine ⟨2673183634440119325272845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3564244845920159100363793 2673183634440119325272845)
              ·
                refine ⟨1002443862915044746977317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673183634440119325272845 1002443862915044746977317)
                ·
                  refine ⟨187958224296570890058247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002443862915044746977317 187958224296570890058247)
                  ·
                    rfl

theorem cell22_1647213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1647213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647213 prefixEnd_1647213 := by exact prefixLift 1647213
  have htrace : WordTrace (prefixWord ++ tailWord_1647213) baseStart_1647213 baseEnd_1647213 := by
    simpa [prefixWord, tailWord_1647213, baseEnd_1647213] using wordTrace_append hprefix tailTrace_1647213
  have hstable : (prefixWord ++ tailWord_1647213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647213).length < 2 ^ (prefixWord ++ tailWord_1647213).sum := by decide
  have hdescent : baseEnd_1647213 < baseStart_1647213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647256 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_1647256 : Nat := 118140960795 + 1647256 * 2 ^ 59
def prefixEnd_1647256 : Nat := 4983230072969 + 3 ^ 40 * 1647256 * 2
def baseEnd_1647256 : Nat := 563889392668474891349609

theorem tailTrace_1647256 : CollatzResearch.WordTrace tailWord_1647256 prefixEnd_1647256 563889392668474891349609 := by
  unfold tailWord_1647256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040181060140157886084811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40053574746853543848113081 30040181060140157886084811)
  ·
    refine ⟨45060271590210236829127217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30040181060140157886084811 45060271590210236829127217)
    ·
      refine ⟨33795203692657677621845413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45060271590210236829127217 33795203692657677621845413)
      ·
        refine ⟨6336600692373314554096015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33795203692657677621845413 6336600692373314554096015)
        ·
          refine ⟨9504901038559971831144023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336600692373314554096015 9504901038559971831144023)
          ·
            refine ⟨14257351557839957746716035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9504901038559971831144023 14257351557839957746716035)
            ·
              refine ⟨21386027336759936620074053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14257351557839957746716035 21386027336759936620074053)
              ·
                refine ⟨4009880125642488116263885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21386027336759936620074053 4009880125642488116263885)
                ·
                  refine ⟨1503705047115933043598957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4009880125642488116263885 1503705047115933043598957)
                  ·
                    refine ⟨563889392668474891349609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503705047115933043598957 563889392668474891349609)
                    ·
                      rfl

theorem cell22_1647256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_1647256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647256 prefixEnd_1647256 := by exact prefixLift 1647256
  have htrace : WordTrace (prefixWord ++ tailWord_1647256) baseStart_1647256 baseEnd_1647256 := by
    simpa [prefixWord, tailWord_1647256, baseEnd_1647256] using wordTrace_append hprefix tailTrace_1647256
  have hstable : (prefixWord ++ tailWord_1647256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647256).length < 2 ^ (prefixWord ++ tailWord_1647256).sum := by decide
  have hdescent : baseEnd_1647256 < baseStart_1647256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647290 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_1647290 : Nat := 118140960795 + 1647290 * 2 ^ 59
def prefixEnd_1647290 : Nat := 4983230072969 + 3 ^ 40 * 1647290 * 2
def baseEnd_1647290 : Nat := 563901031563310135999505

theorem tailTrace_1647290 : CollatzResearch.WordTrace tailWord_1647290 prefixEnd_1647290 563901031563310135999505 := by
  unfold tailWord_1647290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020400550539284894726831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40054401468104759719271549 15020400550539284894726831)
  ·
    refine ⟨22530600825808927342090247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15020400550539284894726831 22530600825808927342090247)
    ·
      refine ⟨33795901238713391013135371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22530600825808927342090247 33795901238713391013135371)
      ·
        refine ⟨50693851858070086519703057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33795901238713391013135371 50693851858070086519703057)
        ·
          refine ⟨38020388893552564889777293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50693851858070086519703057 38020388893552564889777293)
          ·
            refine ⟨14257645835082211833666485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38020388893552564889777293 14257645835082211833666485)
            ·
              refine ⟨1336654297038957359406233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14257645835082211833666485 1336654297038957359406233)
              ·
                refine ⟨1002490722779218019554675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336654297038957359406233 1002490722779218019554675)
                ·
                  refine ⟨1503736084168827029332013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002490722779218019554675 1503736084168827029332013)
                  ·
                    refine ⟨563901031563310135999505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503736084168827029332013 563901031563310135999505)
                    ·
                      rfl

theorem cell22_1647290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_1647290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647290 prefixEnd_1647290 := by exact prefixLift 1647290
  have htrace : WordTrace (prefixWord ++ tailWord_1647290) baseStart_1647290 baseEnd_1647290 := by
    simpa [prefixWord, tailWord_1647290, baseEnd_1647290] using wordTrace_append hprefix tailTrace_1647290
  have hstable : (prefixWord ++ tailWord_1647290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647290).length < 2 ^ (prefixWord ++ tailWord_1647290).sum := by decide
  have hdescent : baseEnd_1647290 < baseStart_1647290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647414 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1647414 : Nat := 118140960795 + 1647414 * 2 ^ 59
def prefixEnd_1647414 : Nat := 4983230072969 + 3 ^ 40 * 1647414 * 2
def baseEnd_1647414 : Nat := 563943479297415145899125

theorem tailTrace_1647414 : CollatzResearch.WordTrace tailWord_1647414 prefixEnd_1647414 563943479297415145899125 := by
  unfold tailWord_1647414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755382803356744297276331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40057416569138605837614197 3755382803356744297276331)
  ·
    refine ⟨5633074205035116445914497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3755382803356744297276331 5633074205035116445914497)
    ·
      refine ⟨4224805653776337334435873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5633074205035116445914497 4224805653776337334435873)
      ·
        refine ⟨3168604240332253000826905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4224805653776337334435873 3168604240332253000826905)
        ·
          refine ⟨2376453180249189750620179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168604240332253000826905 2376453180249189750620179)
          ·
            refine ⟨3564679770373784625930269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376453180249189750620179 3564679770373784625930269)
            ·
              refine ⟨1336754913890169234723851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3564679770373784625930269 1336754913890169234723851)
              ·
                refine ⟨2005132370835253852085777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336754913890169234723851 2005132370835253852085777)
                ·
                  refine ⟨1503849278126440389064333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005132370835253852085777 1503849278126440389064333)
                  ·
                    refine ⟨563943479297415145899125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503849278126440389064333 563943479297415145899125)
                    ·
                      rfl

theorem cell22_1647414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1647414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647414 prefixEnd_1647414 := by exact prefixLift 1647414
  have htrace : WordTrace (prefixWord ++ tailWord_1647414) baseStart_1647414 baseEnd_1647414 := by
    simpa [prefixWord, tailWord_1647414, baseEnd_1647414] using wordTrace_append hprefix tailTrace_1647414
  have hstable : (prefixWord ++ tailWord_1647414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647414).length < 2 ^ (prefixWord ++ tailWord_1647414).sum := by decide
  have hdescent : baseEnd_1647414 < baseStart_1647414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647498 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1647498 : Nat := 118140960795 + 1647498 * 2 ^ 59
def prefixEnd_1647498 : Nat := 4983230072969 + 3 ^ 40 * 1647498 * 2
def baseEnd_1647498 : Nat := 563972234214066926798867

theorem tailTrace_1647498 : CollatzResearch.WordTrace tailWord_1647498 prefixEnd_1647498 563972234214066926798867 := by
  unfold tailWord_1647498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022297146350897775619787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40059459056935727401652765 15022297146350897775619787)
  ·
    refine ⟨22533445719526346663429681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15022297146350897775619787 22533445719526346663429681)
    ·
      refine ⟨16900084289644759997572261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22533445719526346663429681 16900084289644759997572261)
      ·
        refine ⟨3168765804308392499544799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16900084289644759997572261 3168765804308392499544799)
        ·
          refine ⟨4753148706462588749317199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168765804308392499544799 4753148706462588749317199)
          ·
            refine ⟨7129723059693883123975799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753148706462588749317199 7129723059693883123975799)
            ·
              refine ⟨10694584589540824685963699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129723059693883123975799 10694584589540824685963699)
              ·
                refine ⟨16041876884311237028945549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694584589540824685963699 16041876884311237028945549)
                ·
                  refine ⟨6015703831616713885854581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16041876884311237028945549 6015703831616713885854581)
                  ·
                    refine ⟨563972234214066926798867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6015703831616713885854581 563972234214066926798867)
                    ·
                      rfl

theorem cell22_1647498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1647498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647498 prefixEnd_1647498 := by exact prefixLift 1647498
  have htrace : WordTrace (prefixWord ++ tailWord_1647498) baseStart_1647498 baseEnd_1647498 := by
    simpa [prefixWord, tailWord_1647498, baseEnd_1647498] using wordTrace_append hprefix tailTrace_1647498
  have hstable : (prefixWord ++ tailWord_1647498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647498).length < 2 ^ (prefixWord ++ tailWord_1647498).sum := by decide
  have hdescent : baseEnd_1647498 < baseStart_1647498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647543 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 5, 3]
def baseStart_1647543 : Nat := 118140960795 + 1647543 * 2 ^ 59
def prefixEnd_1647543 : Nat := 4983230072969 + 3 ^ 40 * 1647543 * 2
def baseEnd_1647543 : Nat := 563987638633701809423729

theorem tailTrace_1647543 : CollatzResearch.WordTrace tailWord_1647543 prefixEnd_1647543 563987638633701809423729 := by
  unfold tailWord_1647543
  simp only [CollatzResearch.WordTrace]
  refine ⟨60090829870240563787867283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40060553246827042525244855 60090829870240563787867283)
  ·
    refine ⟨90136244805360845681800925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60090829870240563787867283 90136244805360845681800925)
    ·
      refine ⟨33801091802010317130675347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90136244805360845681800925 33801091802010317130675347)
      ·
        refine ⟨50701637703015475696013021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33801091802010317130675347 50701637703015475696013021)
        ·
          refine ⟨19013114138630803386004883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50701637703015475696013021 19013114138630803386004883)
          ·
            refine ⟨28519671207946205079007325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19013114138630803386004883 28519671207946205079007325)
            ·
              refine ⟨10694876702979826904627747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28519671207946205079007325 10694876702979826904627747)
              ·
                refine ⟨16042315054469740356941621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694876702979826904627747 16042315054469740356941621)
                ·
                  refine ⟨1503967036356538158463277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16042315054469740356941621 1503967036356538158463277)
                  ·
                    refine ⟨563987638633701809423729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503967036356538158463277 563987638633701809423729)
                    ·
                      rfl

theorem cell22_1647543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_1647543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647543 prefixEnd_1647543 := by exact prefixLift 1647543
  have htrace : WordTrace (prefixWord ++ tailWord_1647543) baseStart_1647543 baseEnd_1647543 := by
    simpa [prefixWord, tailWord_1647543, baseEnd_1647543] using wordTrace_append hprefix tailTrace_1647543
  have hstable : (prefixWord ++ tailWord_1647543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647543).length < 2 ^ (prefixWord ++ tailWord_1647543).sum := by decide
  have hdescent : baseEnd_1647543 < baseStart_1647543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647577 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 1, 3]
def baseStart_1647577 : Nat := 118140960795 + 1647577 * 2 ^ 59
def prefixEnd_1647577 : Nat := 4983230072969 + 3 ^ 40 * 1647577 * 2
def baseEnd_1647577 : Nat := 563999277528537054073625

theorem tailTrace_1647577 : CollatzResearch.WordTrace tailWord_1647577 prefixEnd_1647577 563999277528537054073625 := by
  unfold tailWord_1647577
  simp only [CollatzResearch.WordTrace]
  refine ⟨60092069952117387594604985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40061379968078258396403323 60092069952117387594604985)
  ·
    refine ⟨45069052464088040695953739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60092069952117387594604985 45069052464088040695953739)
    ·
      refine ⟨67603578696132061043930609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45069052464088040695953739 67603578696132061043930609)
      ·
        refine ⟨50702684022099045782947957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67603578696132061043930609 50702684022099045782947957)
        ·
          refine ⟨4753376627071785542151371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50702684022099045782947957 4753376627071785542151371)
          ·
            refine ⟨7130064940607678313227057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753376627071785542151371 7130064940607678313227057)
            ·
              refine ⟨5347548705455758734920293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7130064940607678313227057 5347548705455758734920293)
              ·
                refine ⟨1002665382272954762797555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5347548705455758734920293 1002665382272954762797555)
                ·
                  refine ⟨1503998073409432144196333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002665382272954762797555 1503998073409432144196333)
                  ·
                    refine ⟨563999277528537054073625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503998073409432144196333 563999277528537054073625)
                    ·
                      rfl

theorem cell22_1647577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_1647577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647577 prefixEnd_1647577 := by exact prefixLift 1647577
  have htrace : WordTrace (prefixWord ++ tailWord_1647577) baseStart_1647577 baseEnd_1647577 := by
    simpa [prefixWord, tailWord_1647577, baseEnd_1647577] using wordTrace_append hprefix tailTrace_1647577
  have hstable : (prefixWord ++ tailWord_1647577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647577).length < 2 ^ (prefixWord ++ tailWord_1647577).sum := by decide
  have hdescent : baseEnd_1647577 < baseStart_1647577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647665 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_1647665 : Nat := 118140960795 + 1647665 * 2 ^ 59
def prefixEnd_1647665 : Nat := 4983230072969 + 3 ^ 40 * 1647665 * 2
def baseEnd_1647665 : Nat := 564029401726934157873355

theorem tailTrace_1647665 : CollatzResearch.WordTrace tailWord_1647665 prefixEnd_1647665 564029401726934157873355 := by
  unfold tailWord_1647665
  simp only [CollatzResearch.WordTrace]
  refine ⟨60095279575798578623808449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40063519717199052415872299 60095279575798578623808449)
  ·
    refine ⟨45071459681848933967856337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60095279575798578623808449 45071459681848933967856337)
    ·
      refine ⟨33803594761386700475892253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45071459681848933967856337 33803594761386700475892253)
      ·
        refine ⟨12676348035520012678459595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33803594761386700475892253 12676348035520012678459595)
        ·
          refine ⟨19014522053280019017689393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12676348035520012678459595 19014522053280019017689393)
          ·
            refine ⟨14260891539960014263267045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19014522053280019017689393 14260891539960014263267045)
            ·
              refine ⟨2673917163742502674362571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14260891539960014263267045 2673917163742502674362571)
              ·
                refine ⟨4010875745613754011543857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673917163742502674362571 4010875745613754011543857)
                ·
                  refine ⟨3008156809210315508657893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4010875745613754011543857 3008156809210315508657893)
                  ·
                    refine ⟨564029401726934157873355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3008156809210315508657893 564029401726934157873355)
                    ·
                      rfl

theorem cell22_1647665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_1647665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647665 prefixEnd_1647665 := by exact prefixLift 1647665
  have htrace : WordTrace (prefixWord ++ tailWord_1647665) baseStart_1647665 baseEnd_1647665 := by
    simpa [prefixWord, tailWord_1647665, baseEnd_1647665] using wordTrace_append hprefix tailTrace_1647665
  have hstable : (prefixWord ++ tailWord_1647665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647665).length < 2 ^ (prefixWord ++ tailWord_1647665).sum := by decide
  have hdescent : baseEnd_1647665 < baseStart_1647665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647686 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1647686 : Nat := 118140960795 + 1647686 * 2 ^ 59
def prefixEnd_1647686 : Nat := 4983230072969 + 3 ^ 40 * 1647686 * 2
def baseEnd_1647686 : Nat := 188012196818699034366097

theorem tailTrace_1647686 : CollatzResearch.WordTrace tailWord_1647686 prefixEnd_1647686 188012196818699034366097 := by
  unfold tailWord_1647686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878001422147578100322591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40064030339148332806881941 1878001422147578100322591)
  ·
    refine ⟨2817002133221367150483887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878001422147578100322591 2817002133221367150483887)
    ·
      refine ⟨4225503199832050725725831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817002133221367150483887 4225503199832050725725831)
      ·
        refine ⟨6338254799748076088588747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4225503199832050725725831 6338254799748076088588747)
        ·
          refine ⟨9507382199622114132883121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338254799748076088588747 9507382199622114132883121)
          ·
            refine ⟨7130536649716585599662341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9507382199622114132883121 7130536649716585599662341)
            ·
              refine ⟨1336975621821859799936689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7130536649716585599662341 1336975621821859799936689)
              ·
                refine ⟨1002731716366394849952517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336975621821859799936689 1002731716366394849952517)
                ·
                  refine ⟨188012196818699034366097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002731716366394849952517 188012196818699034366097)
                  ·
                    rfl

theorem cell22_1647686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1647686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647686 prefixEnd_1647686 := by exact prefixLift 1647686
  have htrace : WordTrace (prefixWord ++ tailWord_1647686) baseStart_1647686 baseEnd_1647686 := by
    simpa [prefixWord, tailWord_1647686, baseEnd_1647686] using wordTrace_append hprefix tailTrace_1647686
  have hstable : (prefixWord ++ tailWord_1647686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647686).length < 2 ^ (prefixWord ++ tailWord_1647686).sum := by decide
  have hdescent : baseEnd_1647686 < baseStart_1647686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647772 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1647772 : Nat := 118140960795 + 1647772 * 2 ^ 59
def prefixEnd_1647772 : Nat := 4983230072969 + 3 ^ 40 * 1647772 * 2
def baseEnd_1647772 : Nat := 564066030013621545448027

theorem tailTrace_1647772 : CollatzResearch.WordTrace tailWord_1647772 prefixEnd_1647772 564066030013621545448027 := by
  unfold tailWord_1647772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30049591093205467948976785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40066121457607290598635713 30049591093205467948976785)
  ·
    refine ⟨22537193319904100961732589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30049591093205467948976785 22537193319904100961732589)
    ·
      refine ⟨8451447494964037860649721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22537193319904100961732589 8451447494964037860649721)
      ·
        refine ⟨6338585621223028395487291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8451447494964037860649721 6338585621223028395487291)
        ·
          refine ⟨9507878431834542593230937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338585621223028395487291 9507878431834542593230937)
          ·
            refine ⟨7130908823875906944923203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9507878431834542593230937 7130908823875906944923203)
            ·
              refine ⟨10696363235813860417384805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130908823875906944923203 10696363235813860417384805)
              ·
                refine ⟨2005568106715098828259651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10696363235813860417384805 2005568106715098828259651)
                ·
                  refine ⟨3008352160072648242389477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005568106715098828259651 3008352160072648242389477)
                  ·
                    refine ⟨564066030013621545448027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3008352160072648242389477 564066030013621545448027)
                    ·
                      rfl

theorem cell22_1647772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1647772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647772 prefixEnd_1647772 := by exact prefixLift 1647772
  have htrace : WordTrace (prefixWord ++ tailWord_1647772) baseStart_1647772 baseEnd_1647772 := by
    simpa [prefixWord, tailWord_1647772, baseEnd_1647772] using wordTrace_append hprefix tailTrace_1647772
  have hstable : (prefixWord ++ tailWord_1647772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647772).length < 2 ^ (prefixWord ++ tailWord_1647772).sum := by decide
  have hdescent : baseEnd_1647772 < baseStart_1647772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647802 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_1647802 : Nat := 118140960795 + 1647802 * 2 ^ 59
def prefixEnd_1647802 : Nat := 4983230072969 + 3 ^ 40 * 1647802 * 2
def baseEnd_1647802 : Nat := 564076299626711467197935

theorem tailTrace_1647802 : CollatzResearch.WordTrace tailWord_1647802 prefixEnd_1647802 564076299626711467197935 := by
  unfold tailWord_1647802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025069094075562755386415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40066850917534834014363773 15025069094075562755386415)
  ·
    refine ⟨22537603641113344133079623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15025069094075562755386415 22537603641113344133079623)
    ·
      refine ⟨33806405461670016199619435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22537603641113344133079623 33806405461670016199619435)
      ·
        refine ⟨50709608192505024299429153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33806405461670016199619435 50709608192505024299429153)
        ·
          refine ⟨38032206144378768224571865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50709608192505024299429153 38032206144378768224571865)
          ·
            refine ⟨28524154608284076168428899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38032206144378768224571865 28524154608284076168428899)
            ·
              refine ⟨42786231912426114252643349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28524154608284076168428899 42786231912426114252643349)
              ·
                refine ⟨2005604620894974105592657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42786231912426114252643349 2005604620894974105592657)
                ·
                  refine ⟨1504203465671230579194493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005604620894974105592657 1504203465671230579194493)
                  ·
                    refine ⟨564076299626711467197935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1504203465671230579194493 564076299626711467197935)
                    ·
                      rfl

theorem cell22_1647802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_1647802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647802 prefixEnd_1647802 := by exact prefixLift 1647802
  have htrace : WordTrace (prefixWord ++ tailWord_1647802) baseStart_1647802 baseEnd_1647802 := by
    simpa [prefixWord, tailWord_1647802, baseEnd_1647802] using wordTrace_append hprefix tailTrace_1647802
  have hstable : (prefixWord ++ tailWord_1647802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647802).length < 2 ^ (prefixWord ++ tailWord_1647802).sum := by decide
  have hdescent : baseEnd_1647802 < baseStart_1647802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647810 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1647810 : Nat := 118140960795 + 1647810 * 2 ^ 59
def prefixEnd_1647810 : Nat := 4983230072969 + 3 ^ 40 * 1647810 * 2
def baseEnd_1647810 : Nat := 188026346063400704332637

theorem tailTrace_1647810 : CollatzResearch.WordTrace tailWord_1647810 prefixEnd_1647810 188026346063400704332637 := by
  unfold tailWord_1647810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025142040068317096959221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40067045440182178925224589 15025142040068317096959221)
  ·
    refine ⟨1408607066256404727839927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15025142040068317096959221 1408607066256404727839927)
    ·
      refine ⟨2112910599384607091759891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408607066256404727839927 2112910599384607091759891)
      ·
        refine ⟨3169365899076910637639837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112910599384607091759891 3169365899076910637639837)
        ·
          refine ⟨1188512212153841489114939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3169365899076910637639837 1188512212153841489114939)
          ·
            refine ⟨1782768318230762233672409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188512212153841489114939 1782768318230762233672409)
            ·
              refine ⟨1337076238673071675254307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1782768318230762233672409 1337076238673071675254307)
              ·
                refine ⟨2005614358009607512881461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337076238673071675254307 2005614358009607512881461)
                ·
                  refine ⟨188026346063400704332637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2005614358009607512881461 188026346063400704332637)
                  ·
                    rfl

theorem cell22_1647810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1647810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647810 prefixEnd_1647810 := by exact prefixLift 1647810
  have htrace : WordTrace (prefixWord ++ tailWord_1647810) baseStart_1647810 baseEnd_1647810 := by
    simpa [prefixWord, tailWord_1647810, baseEnd_1647810] using wordTrace_append hprefix tailTrace_1647810
  have hstable : (prefixWord ++ tailWord_1647810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647810).length < 2 ^ (prefixWord ++ tailWord_1647810).sum := by decide
  have hdescent : baseEnd_1647810 < baseStart_1647810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647875 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_1647875 : Nat := 118140960795 + 1647875 * 2 ^ 59
def prefixEnd_1647875 : Nat := 4983230072969 + 3 ^ 40 * 1647875 * 2
def baseEnd_1647875 : Nat := 564101289018563610122711

theorem tailTrace_1647875 : CollatzResearch.WordTrace tailWord_1647875 prefixEnd_1647875 564101289018563610122711 := by
  unfold tailWord_1647875
  simp only [CollatzResearch.WordTrace]
  refine ⟨60102938905037784488953079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40068625936691856325968719 60102938905037784488953079)
  ·
    refine ⟨90154408357556676733429619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60102938905037784488953079 90154408357556676733429619)
    ·
      refine ⟨135231612536335015100144429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90154408357556676733429619 135231612536335015100144429)
      ·
        refine ⟨50711854701125630662554161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135231612536335015100144429 50711854701125630662554161)
        ·
          refine ⟨38033891025844222996915621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50711854701125630662554161 38033891025844222996915621)
          ·
            refine ⟨7131354567345791811921679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38033891025844222996915621 7131354567345791811921679)
            ·
              refine ⟨10697031851018687717882519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7131354567345791811921679 10697031851018687717882519)
              ·
                refine ⟨16045547776528031576823779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10697031851018687717882519 16045547776528031576823779)
                ·
                  refine ⟨24068321664792047365235669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16045547776528031576823779 24068321664792047365235669)
                  ·
                    refine ⟨564101289018563610122711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24068321664792047365235669 564101289018563610122711)
                    ·
                      rfl

theorem cell22_1647875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_1647875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647875 prefixEnd_1647875 := by exact prefixLift 1647875
  have htrace : WordTrace (prefixWord ++ tailWord_1647875) baseStart_1647875 baseEnd_1647875 := by
    simpa [prefixWord, tailWord_1647875, baseEnd_1647875] using wordTrace_append hprefix tailTrace_1647875
  have hstable : (prefixWord ++ tailWord_1647875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647875).length < 2 ^ (prefixWord ++ tailWord_1647875).sum := by decide
  have hdescent : baseEnd_1647875 < baseStart_1647875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647905 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 10]
def baseStart_1647905 : Nat := 118140960795 + 1647905 * 2 ^ 59
def prefixEnd_1647905 : Nat := 4983230072969 + 3 ^ 40 * 1647905 * 2
def baseEnd_1647905 : Nat := 188037186210551177290873

theorem tailTrace_1647905 : CollatzResearch.WordTrace tailWord_1647905 prefixEnd_1647905 188037186210551177290873 := by
  unfold tailWord_1647905
  simp only [CollatzResearch.WordTrace]
  refine ⟨60104033094929099612545169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40069355396619399741696779 60104033094929099612545169)
  ·
    refine ⟨45078024821196824709408877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60104033094929099612545169 45078024821196824709408877)
    ·
      refine ⟨16904259307948809266028329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45078024821196824709408877 16904259307948809266028329)
      ·
        refine ⟨12678194480961606949521247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16904259307948809266028329 12678194480961606949521247)
        ·
          refine ⟨19017291721442410424281871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12678194480961606949521247 19017291721442410424281871)
          ·
            refine ⟨28525937582163615636422807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19017291721442410424281871 28525937582163615636422807)
            ·
              refine ⟨42788906373245423454634211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28525937582163615636422807 42788906373245423454634211)
              ·
                refine ⟨64183359559868135181951317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42788906373245423454634211 64183359559868135181951317)
                ·
                  refine ⟨188037186210551177290873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 64183359559868135181951317 188037186210551177290873)
                  ·
                    rfl

theorem cell22_1647905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_1647905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647905 prefixEnd_1647905 := by exact prefixLift 1647905
  have htrace : WordTrace (prefixWord ++ tailWord_1647905) baseStart_1647905 baseEnd_1647905 := by
    simpa [prefixWord, tailWord_1647905, baseEnd_1647905] using wordTrace_append hprefix tailTrace_1647905
  have hstable : (prefixWord ++ tailWord_1647905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647905).length < 2 ^ (prefixWord ++ tailWord_1647905).sum := by decide
  have hdescent : baseEnd_1647905 < baseStart_1647905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647922 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1647922 : Nat := 118140960795 + 1647922 * 2 ^ 59
def prefixEnd_1647922 : Nat := 4983230072969 + 3 ^ 40 * 1647922 * 2
def baseEnd_1647922 : Nat := 188039126026357051399189

theorem tailTrace_1647922 : CollatzResearch.WordTrace tailWord_1647922 prefixEnd_1647922 188039126026357051399189 := by
  unfold tailWord_1647922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15026163283966877878978505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40069768757245007677276013 15026163283966877878978505)
  ·
    refine ⟨11269622462975158409233879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15026163283966877878978505 11269622462975158409233879)
    ·
      refine ⟨16904433694462737613850819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11269622462975158409233879 16904433694462737613850819)
      ·
        refine ⟨25356650541694106420776229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16904433694462737613850819 25356650541694106420776229)
        ·
          refine ⟨4754371976567644953895543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25356650541694106420776229 4754371976567644953895543)
          ·
            refine ⟨7131557964851467430843315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754371976567644953895543 7131557964851467430843315)
            ·
              refine ⟨10697336947277201146264973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7131557964851467430843315 10697336947277201146264973)
              ·
                refine ⟨4011501355228950429849365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10697336947277201146264973 4011501355228950429849365)
                ·
                  refine ⟨188039126026357051399189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4011501355228950429849365 188039126026357051399189)
                  ·
                    rfl

theorem cell22_1647922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1647922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647922 prefixEnd_1647922 := by exact prefixLift 1647922
  have htrace : WordTrace (prefixWord ++ tailWord_1647922) baseStart_1647922 baseEnd_1647922 := by
    simpa [prefixWord, tailWord_1647922, baseEnd_1647922] using wordTrace_append hprefix tailTrace_1647922
  have hstable : (prefixWord ++ tailWord_1647922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647922).length < 2 ^ (prefixWord ++ tailWord_1647922).sum := by decide
  have hdescent : baseEnd_1647922 < baseStart_1647922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647952 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_1647952 : Nat := 118140960795 + 1647952 * 2 ^ 59
def prefixEnd_1647952 : Nat := 4983230072969 + 3 ^ 40 * 1647952 * 2
def baseEnd_1647952 : Nat := 564127647692161075947475

theorem tailTrace_1647952 : CollatzResearch.WordTrace tailWord_1647952 prefixEnd_1647952 564127647692161075947475 := by
  unfold tailWord_1647952
  simp only [CollatzResearch.WordTrace]
  refine ⟨30052873662879413319753055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40070498217172551093004073 30052873662879413319753055)
  ·
    refine ⟨45079310494319119979629583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30052873662879413319753055 45079310494319119979629583)
    ·
      refine ⟨67618965741478679969444375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45079310494319119979629583 67618965741478679969444375)
      ·
        refine ⟨101428448612218019954166563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67618965741478679969444375 101428448612218019954166563)
        ·
          refine ⟨152142672918327029931249845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101428448612218019954166563 152142672918327029931249845)
          ·
            refine ⟨14263375586093159056054673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152142672918327029931249845 14263375586093159056054673)
            ·
              refine ⟨10697531689569869292041005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14263375586093159056054673 10697531689569869292041005)
              ·
                refine ⟨4011574383588700984515377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10697531689569869292041005 4011574383588700984515377)
                ·
                  refine ⟨3008680787691525738386533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4011574383588700984515377 3008680787691525738386533)
                  ·
                    refine ⟨564127647692161075947475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3008680787691525738386533 564127647692161075947475)
                    ·
                      rfl

theorem cell22_1647952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_1647952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1647952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1647952 prefixEnd_1647952 := by exact prefixLift 1647952
  have htrace : WordTrace (prefixWord ++ tailWord_1647952) baseStart_1647952 baseEnd_1647952 := by
    simpa [prefixWord, tailWord_1647952, baseEnd_1647952] using wordTrace_append hprefix tailTrace_1647952
  have hstable : (prefixWord ++ tailWord_1647952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647952).length < 2 ^ (prefixWord ++ tailWord_1647952).sum := by decide
  have hdescent : baseEnd_1647952 < baseStart_1647952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648029 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1648029 : Nat := 118140960795 + 1648029 * 2 ^ 59
def prefixEnd_1648029 : Nat := 4983230072969 + 3 ^ 40 * 1648029 * 2
def baseEnd_1648029 : Nat := 188051335455252847257413

theorem tailTrace_1648029 : CollatzResearch.WordTrace tailWord_1648029 prefixEnd_1648029 188051335455252847257413 := by
  unfold tailWord_1648029
  simp only [CollatzResearch.WordTrace]
  refine ⟨60108555746479868790059141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40072370497653245860039427 60108555746479868790059141)
  ·
    refine ⟨11270354202464975398136089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60108555746479868790059141 11270354202464975398136089)
    ·
      refine ⟨8452765651848731548602067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11270354202464975398136089 8452765651848731548602067)
      ·
        refine ⟨12679148477773097322903101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8452765651848731548602067 12679148477773097322903101)
        ·
          refine ⟨4754680679164911496088663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12679148477773097322903101 4754680679164911496088663)
          ·
            refine ⟨7132021018747367244132995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754680679164911496088663 7132021018747367244132995)
            ·
              refine ⟨10698031528121050866199493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132021018747367244132995 10698031528121050866199493)
              ·
                refine ⟨2005880911522697037412405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10698031528121050866199493 2005880911522697037412405)
                ·
                  refine ⟨188051335455252847257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2005880911522697037412405 188051335455252847257413)
                  ·
                    rfl

theorem cell22_1648029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1648029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648029 prefixEnd_1648029 := by exact prefixLift 1648029
  have htrace : WordTrace (prefixWord ++ tailWord_1648029) baseStart_1648029 baseEnd_1648029 := by
    simpa [prefixWord, tailWord_1648029, baseEnd_1648029] using wordTrace_append hprefix tailTrace_1648029
  have hstable : (prefixWord ++ tailWord_1648029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648029).length < 2 ^ (prefixWord ++ tailWord_1648029).sum := by decide
  have hdescent : baseEnd_1648029 < baseStart_1648029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648076 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_1648076 : Nat := 118140960795 + 1648076 * 2 ^ 59
def prefixEnd_1648076 : Nat := 4983230072969 + 3 ^ 40 * 1648076 * 2
def baseEnd_1648076 : Nat := 564170095426266085847095

theorem tailTrace_1648076 : CollatzResearch.WordTrace tailWord_1648076 prefixEnd_1648076 564170095426266085847095 := by
  unfold tailWord_1648076
  simp only [CollatzResearch.WordTrace]
  refine ⟨30055134988654797908510041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40073513318206397211346721 30055134988654797908510041)
  ·
    refine ⟨22541351241491098431382531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30055134988654797908510041 22541351241491098431382531)
    ·
      refine ⟨33812026862236647647073797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22541351241491098431382531 33812026862236647647073797)
      ·
        refine ⟨6339755036669371433826337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33812026862236647647073797 6339755036669371433826337)
        ·
          refine ⟨4754816277502028575369753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6339755036669371433826337 4754816277502028575369753)
          ·
            refine ⟨3566112208126521431527315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754816277502028575369753 3566112208126521431527315)
            ·
              refine ⟨5349168312189782147290973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566112208126521431527315 5349168312189782147290973)
              ·
                refine ⟨2005938117071168305234115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5349168312189782147290973 2005938117071168305234115)
                ·
                  refine ⟨3008907175606752457851173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005938117071168305234115 3008907175606752457851173)
                  ·
                    refine ⟨564170095426266085847095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3008907175606752457851173 564170095426266085847095)
                    ·
                      rfl

theorem cell22_1648076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_1648076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648076 prefixEnd_1648076 := by exact prefixLift 1648076
  have htrace : WordTrace (prefixWord ++ tailWord_1648076) baseStart_1648076 baseEnd_1648076 := by
    simpa [prefixWord, tailWord_1648076, baseEnd_1648076] using wordTrace_append hprefix tailTrace_1648076
  have hstable : (prefixWord ++ tailWord_1648076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648076).length < 2 ^ (prefixWord ++ tailWord_1648076).sum := by decide
  have hdescent : baseEnd_1648076 < baseStart_1648076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648209 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 6]
def baseStart_1648209 : Nat := 118140960795 + 1648209 * 2 ^ 59
def prefixEnd_1648209 : Nat := 4983230072969 + 3 ^ 40 * 1648209 * 2
def baseEnd_1648209 : Nat := 188071874681432690757229

theorem tailTrace_1648209 : CollatzResearch.WordTrace tailWord_1648209 prefixEnd_1648209 188071874681432690757229 := by
  unfold tailWord_1648209
  simp only [CollatzResearch.WordTrace]
  refine ⟨60115120885827759531611681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40076747257218506354407787 60115120885827759531611681)
  ·
    refine ⟨45086340664370819648708761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60115120885827759531611681 45086340664370819648708761)
    ·
      refine ⟨33814755498278114736531571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45086340664370819648708761 33814755498278114736531571)
      ·
        refine ⟨50722133247417172104797357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33814755498278114736531571 50722133247417172104797357)
        ·
          refine ⟨19020799967781439539299009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50722133247417172104797357 19020799967781439539299009)
          ·
            refine ⟨14265599975836079654474257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19020799967781439539299009 14265599975836079654474257)
            ·
              refine ⟨10699199981877059740855693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14265599975836079654474257 10699199981877059740855693)
              ·
                refine ⟨4012199993203897402820885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10699199981877059740855693 4012199993203897402820885)
                ·
                  refine ⟨188071874681432690757229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4012199993203897402820885 188071874681432690757229)
                  ·
                    rfl

theorem cell22_1648209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_1648209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648209 prefixEnd_1648209 := by exact prefixLift 1648209
  have htrace : WordTrace (prefixWord ++ tailWord_1648209) baseStart_1648209 baseEnd_1648209 := by
    simpa [prefixWord, tailWord_1648209, baseEnd_1648209] using wordTrace_append hprefix tailTrace_1648209
  have hstable : (prefixWord ++ tailWord_1648209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648209).length < 2 ^ (prefixWord ++ tailWord_1648209).sum := by decide
  have hdescent : baseEnd_1648209 < baseStart_1648209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648245 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1648245 : Nat := 118140960795 + 1648245 * 2 ^ 59
def prefixEnd_1648245 : Nat := 4983230072969 + 3 ^ 40 * 1648245 * 2
def baseEnd_1648245 : Nat := 564227947580005978371577

theorem tailTrace_1648245 : CollatzResearch.WordTrace tailWord_1648245 prefixEnd_1648245 564227947580005978371577 := by
  unfold tailWord_1648245
  simp only [CollatzResearch.WordTrace]
  refine ⟨60116433913697337679922189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40077622609131558453281459 60116433913697337679922189)
  ·
    refine ⟨22543662717636501629970821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60116433913697337679922189 22543662717636501629970821)
    ·
      refine ⟨4226936759556844055619529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22543662717636501629970821 4226936759556844055619529)
      ·
        refine ⟨3170202569667633041714647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4226936759556844055619529 3170202569667633041714647)
        ·
          refine ⟨4755303854501449562571971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170202569667633041714647 4755303854501449562571971)
          ·
            refine ⟨7132955781752174343857957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755303854501449562571971 7132955781752174343857957)
            ·
              refine ⟨1337429209078532689473367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7132955781752174343857957 1337429209078532689473367)
              ·
                refine ⟨2006143813617799034210051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337429209078532689473367 2006143813617799034210051)
                ·
                  refine ⟨3009215720426698551315077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006143813617799034210051 3009215720426698551315077)
                  ·
                    refine ⟨564227947580005978371577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009215720426698551315077 564227947580005978371577)
                    ·
                      rfl

theorem cell22_1648245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1648245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648245 prefixEnd_1648245 := by exact prefixLift 1648245
  have htrace : WordTrace (prefixWord ++ tailWord_1648245) baseStart_1648245 baseEnd_1648245 := by
    simpa [prefixWord, tailWord_1648245, baseEnd_1648245] using wordTrace_append hprefix tailTrace_1648245
  have hstable : (prefixWord ++ tailWord_1648245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648245).length < 2 ^ (prefixWord ++ tailWord_1648245).sum := by decide
  have hdescent : baseEnd_1648245 < baseStart_1648245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648288 : List Nat := [2, 1, 1, 4, 3, 3, 2, 6]
def baseStart_1648288 : Nat := 118140960795 + 1648288 * 2 ^ 59
def prefixEnd_1648288 : Nat := 4983230072969 + 3 ^ 40 * 1648288 * 2
def baseEnd_1648288 : Nat := 62693629706529799949605

theorem tailTrace_1648288 : CollatzResearch.WordTrace tailWord_1648288 prefixEnd_1648288 62693629706529799949605 := by
  unfold tailWord_1648288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30059001126270778011868759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40078668168361037349158345 30059001126270778011868759)
  ·
    refine ⟨45088501689406167017803139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30059001126270778011868759 45088501689406167017803139)
    ·
      refine ⟨67632752534109250526704709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45088501689406167017803139 67632752534109250526704709)
      ·
        refine ⟨12681141100145484473757133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67632752534109250526704709 12681141100145484473757133)
        ·
          refine ⟨4755427912554556677658925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12681141100145484473757133 4755427912554556677658925)
          ·
            refine ⟨1783285467207958754122097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4755427912554556677658925 1783285467207958754122097)
            ·
              refine ⟨1337464100405969065591573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783285467207958754122097 1337464100405969065591573)
              ·
                refine ⟨62693629706529799949605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1337464100405969065591573 62693629706529799949605)
                ·
                  rfl

theorem cell22_1648288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_1648288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648288 prefixEnd_1648288 := by exact prefixLift 1648288
  have htrace : WordTrace (prefixWord ++ tailWord_1648288) baseStart_1648288 baseEnd_1648288 := by
    simpa [prefixWord, tailWord_1648288, baseEnd_1648288] using wordTrace_append hprefix tailTrace_1648288
  have hstable : (prefixWord ++ tailWord_1648288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648288).length < 2 ^ (prefixWord ++ tailWord_1648288).sum := by decide
  have hdescent : baseEnd_1648288 < baseStart_1648288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648316 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1648316 : Nat := 118140960795 + 1648316 * 2 ^ 59
def prefixEnd_1648316 : Nat := 4983230072969 + 3 ^ 40 * 1648316 * 2
def baseEnd_1648316 : Nat := 188084084110328486615453

theorem tailTrace_1648316 : CollatzResearch.WordTrace tailWord_1648316 prefixEnd_1648316 188084084110328486615453 := by
  unfold tailWord_1648316
  simp only [CollatzResearch.WordTrace]
  refine ⟨30059511748220058402878401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40079348997626744537171201 30059511748220058402878401)
  ·
    refine ⟨22544633811165043802158801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30059511748220058402878401 22544633811165043802158801)
    ·
      refine ⟨16908475358373782851619101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22544633811165043802158801 16908475358373782851619101)
      ·
        refine ⟨6340678259390168569357163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16908475358373782851619101 6340678259390168569357163)
        ·
          refine ⟨9511017389085252854035745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340678259390168569357163 9511017389085252854035745)
          ·
            refine ⟨7133263041813939640526809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9511017389085252854035745 7133263041813939640526809)
            ·
              refine ⟨5349947281360454730395107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7133263041813939640526809 5349947281360454730395107)
              ·
                refine ⟨8024920922040682095592661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349947281360454730395107 8024920922040682095592661)
                ·
                  refine ⟨188084084110328486615453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8024920922040682095592661 188084084110328486615453)
                  ·
                    rfl

theorem cell22_1648316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1648316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648316 prefixEnd_1648316 := by exact prefixLift 1648316
  have htrace : WordTrace (prefixWord ++ tailWord_1648316) baseStart_1648316 baseEnd_1648316 := by
    simpa [prefixWord, tailWord_1648316, baseEnd_1648316] using wordTrace_append hprefix tailTrace_1648316
  have hstable : (prefixWord ++ tailWord_1648316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648316).length < 2 ^ (prefixWord ++ tailWord_1648316).sum := by decide
  have hdescent : baseEnd_1648316 < baseStart_1648316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648322 : List Nat := [3, 5, 1, 2, 1, 1, 2, 7]
def baseStart_1648322 : Nat := 118140960795 + 1648322 * 2 ^ 59
def prefixEnd_1648322 : Nat := 4983230072969 + 3 ^ 40 * 1648322 * 2
def baseEnd_1648322 : Nat := 62694922917067049355149

theorem tailTrace_1648322 : CollatzResearch.WordTrace tailWord_1648322 prefixEnd_1648322 62694922917067049355149 := by
  unfold tailWord_1648322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15029810583604594957618805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40079494889612253220316813 15029810583604594957618805)
  ·
    refine ⟨1409044742212930777276763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15029810583604594957618805 1409044742212930777276763)
    ·
      refine ⟨2113567113319396165915145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409044742212930777276763 2113567113319396165915145)
      ·
        refine ⟨1585175334989547124436359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2113567113319396165915145 1585175334989547124436359)
        ·
          refine ⟨2377763002484320686654539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585175334989547124436359 2377763002484320686654539)
          ·
            refine ⟨3566644503726481029981809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377763002484320686654539 3566644503726481029981809)
            ·
              refine ⟨2674983377794860772486357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566644503726481029981809 2674983377794860772486357)
              ·
                refine ⟨62694922917067049355149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2674983377794860772486357 62694922917067049355149)
                ·
                  rfl

theorem cell22_1648322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_1648322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648322 prefixEnd_1648322 := by exact prefixLift 1648322
  have htrace : WordTrace (prefixWord ++ tailWord_1648322) baseStart_1648322 baseEnd_1648322 := by
    simpa [prefixWord, tailWord_1648322, baseEnd_1648322] using wordTrace_append hprefix tailTrace_1648322
  have hstable : (prefixWord ++ tailWord_1648322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648322).length < 2 ^ (prefixWord ++ tailWord_1648322).sum := by decide
  have hdescent : baseEnd_1648322 < baseStart_1648322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648326 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1648326 : Nat := 118140960795 + 1648326 * 2 ^ 59
def prefixEnd_1648326 : Nat := 4983230072969 + 3 ^ 40 * 1648326 * 2
def baseEnd_1648326 : Nat := 564255675535348767096329

theorem tailTrace_1648326 : CollatzResearch.WordTrace tailWord_1648326 prefixEnd_1648326 564255675535348767096329 := by
  unfold tailWord_1648326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878730882075121516050651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40079592150935925675747221 1878730882075121516050651)
  ·
    refine ⟨2818096323112682274075977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878730882075121516050651 2818096323112682274075977)
    ·
      refine ⟨2113572242334511705556983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818096323112682274075977 2113572242334511705556983)
      ·
        refine ⟨3170358363501767558335475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113572242334511705556983 3170358363501767558335475)
        ·
          refine ⟨4755537545252651337503213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170358363501767558335475 4755537545252651337503213)
          ·
            refine ⟨1783326579469744251563705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4755537545252651337503213 1783326579469744251563705)
            ·
              refine ⟨1337494934602308188672779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783326579469744251563705 1337494934602308188672779)
              ·
                refine ⟨2006242401903462283009169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337494934602308188672779 2006242401903462283009169)
                ·
                  refine ⟨1504681801427596712256877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2006242401903462283009169 1504681801427596712256877)
                  ·
                    refine ⟨564255675535348767096329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1504681801427596712256877 564255675535348767096329)
                    ·
                      rfl

theorem cell22_1648326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1648326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648326 prefixEnd_1648326 := by exact prefixLift 1648326
  have htrace : WordTrace (prefixWord ++ tailWord_1648326) baseStart_1648326 baseEnd_1648326 := by
    simpa [prefixWord, tailWord_1648326, baseEnd_1648326] using wordTrace_append hprefix tailTrace_1648326
  have hstable : (prefixWord ++ tailWord_1648326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648326).length < 2 ^ (prefixWord ++ tailWord_1648326).sum := by decide
  have hdescent : baseEnd_1648326 < baseStart_1648326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648408 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_1648408 : Nat := 118140960795 + 1648408 * 2 ^ 59
def prefixEnd_1648408 : Nat := 4983230072969 + 3 ^ 40 * 1648408 * 2
def baseEnd_1648408 : Nat := 564283745811127886546077

theorem tailTrace_1648408 : CollatzResearch.WordTrace tailWord_1648408 prefixEnd_1648408 564283745811127886546077 := by
  unfold tailWord_1648408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30061189506053408259052939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40081586008071211012070585 30061189506053408259052939)
  ·
    refine ⟨45091784259080112388579409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30061189506053408259052939 45091784259080112388579409)
    ·
      refine ⟨33818838194310084291434557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45091784259080112388579409 33818838194310084291434557)
      ·
        refine ⟨12682064322866281609287959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33818838194310084291434557 12682064322866281609287959)
        ·
          refine ⟨19023096484299422413931939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12682064322866281609287959 19023096484299422413931939)
          ·
            refine ⟨28534644726449133620897909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19023096484299422413931939 28534644726449133620897909)
            ·
              refine ⟨2675122943104606276959179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28534644726449133620897909 2675122943104606276959179)
              ·
                refine ⟨4012684414656909415438769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675122943104606276959179 4012684414656909415438769)
                ·
                  refine ⟨3009513310992682061579077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012684414656909415438769 3009513310992682061579077)
                  ·
                    refine ⟨564283745811127886546077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009513310992682061579077 564283745811127886546077)
                    ·
                      rfl

theorem cell22_1648408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_1648408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648408 prefixEnd_1648408 := by exact prefixLift 1648408
  have htrace : WordTrace (prefixWord ++ tailWord_1648408) baseStart_1648408 baseEnd_1648408 := by
    simpa [prefixWord, tailWord_1648408, baseEnd_1648408] using wordTrace_append hprefix tailTrace_1648408
  have hstable : (prefixWord ++ tailWord_1648408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648408).length < 2 ^ (prefixWord ++ tailWord_1648408).sum := by decide
  have hdescent : baseEnd_1648408 < baseStart_1648408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648414 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1648414 : Nat := 118140960795 + 1648414 * 2 ^ 59
def prefixEnd_1648414 : Nat := 4983230072969 + 3 ^ 40 * 1648414 * 2
def baseEnd_1648414 : Nat := 564285799733745870896059

theorem tailTrace_1648414 : CollatzResearch.WordTrace tailWord_1648414 prefixEnd_1648414 564285799733745870896059 := by
  unfold tailWord_1648414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515324731260634942853037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40081731900056719695216197 7515324731260634942853037)
  ·
    refine ⟨2818246774222738103569889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7515324731260634942853037 2818246774222738103569889)
    ·
      refine ⟨2113685080667053577677417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818246774222738103569889 2113685080667053577677417)
      ·
        refine ⟨1585263810500290183258063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2113685080667053577677417 1585263810500290183258063)
        ·
          refine ⟨2377895715750435274887095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585263810500290183258063 2377895715750435274887095)
          ·
            refine ⟨3566843573625652912330643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377895715750435274887095 3566843573625652912330643)
            ·
              refine ⟨5350265360438479368495965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566843573625652912330643 5350265360438479368495965)
              ·
                refine ⟨2006349510164429763185987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5350265360438479368495965 2006349510164429763185987)
                ·
                  refine ⟨3009524265246644644778981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006349510164429763185987 3009524265246644644778981)
                  ·
                    refine ⟨564285799733745870896059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009524265246644644778981 564285799733745870896059)
                    ·
                      rfl

theorem cell22_1648414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1648414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648414 prefixEnd_1648414 := by exact prefixLift 1648414
  have htrace : WordTrace (prefixWord ++ tailWord_1648414) baseStart_1648414 baseEnd_1648414 := by
    simpa [prefixWord, tailWord_1648414, baseEnd_1648414] using wordTrace_append hprefix tailTrace_1648414
  have hstable : (prefixWord ++ tailWord_1648414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648414).length < 2 ^ (prefixWord ++ tailWord_1648414).sum := by decide
  have hdescent : baseEnd_1648414 < baseStart_1648414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648468 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1648468 : Nat := 118140960795 + 1648468 * 2 ^ 59
def prefixEnd_1648468 : Nat := 4983230072969 + 3 ^ 40 * 1648468 * 2
def baseEnd_1648468 : Nat := 188101428345769243348631

theorem tailTrace_1648468 : CollatzResearch.WordTrace tailWord_1648468 prefixEnd_1648468 188101428345769243348631 := by
  unfold tailWord_1648468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30062283695944723382645029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40083044927926297843526705 30062283695944723382645029)
  ·
    refine ⟨5636678192989635634245943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30062283695944723382645029 5636678192989635634245943)
    ·
      refine ⟨8455017289484453451368915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636678192989635634245943 8455017289484453451368915)
      ·
        refine ⟨12682525934226680177053373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8455017289484453451368915 12682525934226680177053373)
        ·
          refine ⟨4755947225335005066395015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12682525934226680177053373 4755947225335005066395015)
          ·
            refine ⟨7133920838002507599592523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755947225335005066395015 7133920838002507599592523)
            ·
              refine ⟨10700881257003761399388785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133920838002507599592523 10700881257003761399388785)
              ·
                refine ⟨8025660942752821049541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700881257003761399388785 8025660942752821049541589)
                ·
                  refine ⟨188101428345769243348631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8025660942752821049541589 188101428345769243348631)
                  ·
                    rfl

theorem cell22_1648468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1648468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648468 prefixEnd_1648468 := by exact prefixLift 1648468
  have htrace : WordTrace (prefixWord ++ tailWord_1648468) baseStart_1648468 baseEnd_1648468 := by
    simpa [prefixWord, tailWord_1648468, baseEnd_1648468] using wordTrace_append hprefix tailTrace_1648468
  have hstable : (prefixWord ++ tailWord_1648468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648468).length < 2 ^ (prefixWord ++ tailWord_1648468).sum := by decide
  have hdescent : baseEnd_1648468 < baseStart_1648468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648498 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1648498 : Nat := 118140960795 + 1648498 * 2 ^ 59
def prefixEnd_1648498 : Nat := 4983230072969 + 3 ^ 40 * 1648498 * 2
def baseEnd_1648498 : Nat := 564314554650397651795801

theorem tailTrace_1648498 : CollatzResearch.WordTrace tailWord_1648498 prefixEnd_1648498 564314554650397651795801 := by
  unfold tailWord_1648498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031415395445190472220537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40083774387853841259254765 15031415395445190472220537)
  ·
    refine ⟨11273561546583892854165403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15031415395445190472220537 11273561546583892854165403)
    ·
      refine ⟨16910342319875839281248105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11273561546583892854165403 16910342319875839281248105)
      ·
        refine ⟨12682756739906879460936079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16910342319875839281248105 12682756739906879460936079)
        ·
          refine ⟨19024135109860319191404119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12682756739906879460936079 19024135109860319191404119)
          ·
            refine ⟨28536202664790478787106179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024135109860319191404119 28536202664790478787106179)
            ·
              refine ⟨42804303997185718180659269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28536202664790478787106179 42804303997185718180659269)
              ·
                refine ⟨8025806999472322158873613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42804303997185718180659269 8025806999472322158873613)
                ·
                  refine ⟨3009677624802120809577605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8025806999472322158873613 3009677624802120809577605)
                  ·
                    refine ⟨564314554650397651795801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009677624802120809577605 564314554650397651795801)
                    ·
                      rfl

theorem cell22_1648498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1648498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648498 prefixEnd_1648498 := by exact prefixLift 1648498
  have htrace : WordTrace (prefixWord ++ tailWord_1648498) baseStart_1648498 baseEnd_1648498 := by
    simpa [prefixWord, tailWord_1648498, baseEnd_1648498] using wordTrace_append hprefix tailTrace_1648498
  have hstable : (prefixWord ++ tailWord_1648498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648498).length < 2 ^ (prefixWord ++ tailWord_1648498).sum := by decide
  have hdescent : baseEnd_1648498 < baseStart_1648498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648502 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1648502 : Nat := 118140960795 + 1648502 * 2 ^ 59
def prefixEnd_1648502 : Nat := 4983230072969 + 3 ^ 40 * 1648502 * 2
def baseEnd_1648502 : Nat := 188105307977380991565263

theorem tailTrace_1648502 : CollatzResearch.WordTrace tailWord_1648502 prefixEnd_1648502 188105307977380991565263 := by
  unfold tailWord_1648502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757862967110391910751735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40083871649177513714685173 3757862967110391910751735)
  ·
    refine ⟨5636794450665587866127603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3757862967110391910751735 5636794450665587866127603)
    ·
      refine ⟨8455191675998381799191405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636794450665587866127603 8455191675998381799191405)
      ·
        refine ⟨3170696878499393174696777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8455191675998381799191405 3170696878499393174696777)
        ·
          refine ⟨2378022658874544881022583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170696878499393174696777 2378022658874544881022583)
          ·
            refine ⟨3567033988311817321533875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378022658874544881022583 3567033988311817321533875)
            ·
              refine ⟨5350550982467725982300813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567033988311817321533875 5350550982467725982300813)
              ·
                refine ⟨2006456618425397243362805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5350550982467725982300813 2006456618425397243362805)
                ·
                  refine ⟨188105307977380991565263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2006456618425397243362805 188105307977380991565263)
                  ·
                    rfl

theorem cell22_1648502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1648502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648502 prefixEnd_1648502 := by exact prefixLift 1648502
  have htrace : WordTrace (prefixWord ++ tailWord_1648502) baseStart_1648502 baseEnd_1648502 := by
    simpa [prefixWord, tailWord_1648502, baseEnd_1648502] using wordTrace_append hprefix tailTrace_1648502
  have hstable : (prefixWord ++ tailWord_1648502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648502).length < 2 ^ (prefixWord ++ tailWord_1648502).sum := by decide
  have hdescent : baseEnd_1648502 < baseStart_1648502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648515 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 1, 4]
def baseStart_1648515 : Nat := 118140960795 + 1648515 * 2 ^ 59
def prefixEnd_1648515 : Nat := 4983230072969 + 3 ^ 40 * 1648515 * 2
def baseEnd_1648515 : Nat := 564320374097815274120749

theorem tailTrace_1648515 : CollatzResearch.WordTrace tailWord_1648515 prefixEnd_1648515 564320374097815274120749 := by
  unfold tailWord_1648515
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126281622719173792250999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40084187748479449194833999 60126281622719173792250999)
  ·
    refine ⟨90189422434078760688376499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60126281622719173792250999 90189422434078760688376499)
    ·
      refine ⟨135284133651118141032564749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90189422434078760688376499 135284133651118141032564749)
      ·
        refine ⟨50731550119169302887211781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135284133651118141032564749 50731550119169302887211781)
        ·
          refine ⟨9512165647344244291352209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50731550119169302887211781 9512165647344244291352209)
          ·
            refine ⟨7134124235508183218514157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9512165647344244291352209 7134124235508183218514157)
            ·
              refine ⟨2675296588315568706942809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7134124235508183218514157 2675296588315568706942809)
              ·
                refine ⟨2006472441236676530207107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675296588315568706942809 2006472441236676530207107)
                ·
                  refine ⟨3009708661855014795310661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006472441236676530207107 3009708661855014795310661)
                  ·
                    refine ⟨564320374097815274120749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3009708661855014795310661 564320374097815274120749)
                    ·
                      rfl

theorem cell22_1648515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4].length) (baseStart_1648515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648515 prefixEnd_1648515 := by exact prefixLift 1648515
  have htrace : WordTrace (prefixWord ++ tailWord_1648515) baseStart_1648515 baseEnd_1648515 := by
    simpa [prefixWord, tailWord_1648515, baseEnd_1648515] using wordTrace_append hprefix tailTrace_1648515
  have hstable : (prefixWord ++ tailWord_1648515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648515).length < 2 ^ (prefixWord ++ tailWord_1648515).sum := by decide
  have hdescent : baseEnd_1648515 < baseStart_1648515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648590 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1648590 : Nat := 118140960795 + 1648590 * 2 ^ 59
def prefixEnd_1648590 : Nat := 4983230072969 + 3 ^ 40 * 1648590 * 2
def baseEnd_1648590 : Nat := 564346048130540078495519

theorem tailTrace_1648590 : CollatzResearch.WordTrace tailWord_1648590 prefixEnd_1648590 564346048130540078495519 := by
  unfold tailWord_1648590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516127137180932700153903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40086011398298307734154149 7516127137180932700153903)
  ·
    refine ⟨11274190705771399050230855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7516127137180932700153903 11274190705771399050230855)
    ·
      refine ⟨16911286058657098575346283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11274190705771399050230855 16911286058657098575346283)
      ·
        refine ⟨25366929087985647863019425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16911286058657098575346283 25366929087985647863019425)
        ·
          refine ⟨19025196815989235897264569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25366929087985647863019425 19025196815989235897264569)
          ·
            refine ⟨14268897611991926922948427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19025196815989235897264569 14268897611991926922948427)
            ·
              refine ⟨21403346417987890384422641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268897611991926922948427 21403346417987890384422641)
              ·
                refine ⟨16052509813490917788316981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21403346417987890384422641 16052509813490917788316981)
                ·
                  refine ⟨1504922795014773542654717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16052509813490917788316981 1504922795014773542654717)
                  ·
                    refine ⟨564346048130540078495519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1504922795014773542654717 564346048130540078495519)
                    ·
                      rfl

theorem cell22_1648590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1648590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648590 prefixEnd_1648590 := by exact prefixLift 1648590
  have htrace : WordTrace (prefixWord ++ tailWord_1648590) baseStart_1648590 baseEnd_1648590 := by
    simpa [prefixWord, tailWord_1648590, baseEnd_1648590] using wordTrace_append hprefix tailTrace_1648590
  have hstable : (prefixWord ++ tailWord_1648590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648590).length < 2 ^ (prefixWord ++ tailWord_1648590).sum := by decide
  have hdescent : baseEnd_1648590 < baseStart_1648590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648607 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 3, 3]
def baseStart_1648607 : Nat := 118140960795 + 1648607 * 2 ^ 59
def prefixEnd_1648607 : Nat := 4983230072969 + 3 ^ 40 * 1648607 * 2
def baseEnd_1648607 : Nat := 564351867577957700820467

theorem tailTrace_1648607 : CollatzResearch.WordTrace tailWord_1648607 prefixEnd_1648607 564351867577957700820467 := by
  unfold tailWord_1648607
  simp only [CollatzResearch.WordTrace]
  refine ⟨60129637138385873504600075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40086424758923915669733383 60129637138385873504600075)
  ·
    refine ⟨90194455707578810256900113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60129637138385873504600075 90194455707578810256900113)
    ·
      refine ⟨67645841780684107692675085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90194455707578810256900113 67645841780684107692675085)
      ·
        refine ⟨25367190667756540384753157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67645841780684107692675085 25367190667756540384753157)
        ·
          refine ⟨4756348250204351322141217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25367190667756540384753157 4756348250204351322141217)
          ·
            refine ⟨3567261187653263491605913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4756348250204351322141217 3567261187653263491605913)
            ·
              refine ⟨2675445890739947618704435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567261187653263491605913 2675445890739947618704435)
              ·
                refine ⟨4013168836109921428056653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675445890739947618704435 4013168836109921428056653)
                ·
                  refine ⟨1504938313541220535521245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4013168836109921428056653 1504938313541220535521245)
                  ·
                    refine ⟨564351867577957700820467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1504938313541220535521245 564351867577957700820467)
                    ·
                      rfl

theorem cell22_1648607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_1648607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648607 prefixEnd_1648607 := by exact prefixLift 1648607
  have htrace : WordTrace (prefixWord ++ tailWord_1648607) baseStart_1648607 baseEnd_1648607 := by
    simpa [prefixWord, tailWord_1648607, baseEnd_1648607] using wordTrace_append hprefix tailTrace_1648607
  have hstable : (prefixWord ++ tailWord_1648607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648607).length < 2 ^ (prefixWord ++ tailWord_1648607).sum := by decide
  have hdescent : baseEnd_1648607 < baseStart_1648607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648695 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1648695 : Nat := 118140960795 + 1648695 * 2 ^ 59
def prefixEnd_1648695 : Nat := 4983230072969 + 3 ^ 40 * 1648695 * 2
def baseEnd_1648695 : Nat := 564381991776354804620197

theorem tailTrace_1648695 : CollatzResearch.WordTrace tailWord_1648695 prefixEnd_1648695 564381991776354804620197 := by
  unfold tailWord_1648695
  simp only [CollatzResearch.WordTrace]
  refine ⟨60132846762067064533803539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40088564508044709689202359 60132846762067064533803539)
  ·
    refine ⟨90199270143100596800705309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60132846762067064533803539 90199270143100596800705309)
    ·
      refine ⟨33824726303662723800264491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90199270143100596800705309 33824726303662723800264491)
      ·
        refine ⟨50737089455494085700396737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33824726303662723800264491 50737089455494085700396737)
        ·
          refine ⟨38052817091620564275297553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50737089455494085700396737 38052817091620564275297553)
          ·
            refine ⟨28539612818715423206473165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38052817091620564275297553 28539612818715423206473165)
            ·
              refine ⟨10702354807018283702427437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28539612818715423206473165 10702354807018283702427437)
              ·
                refine ⟨4013383052631856388410289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10702354807018283702427437 4013383052631856388410289)
                ·
                  refine ⟨3010037289473892291307717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013383052631856388410289 3010037289473892291307717)
                  ·
                    refine ⟨564381991776354804620197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010037289473892291307717 564381991776354804620197)
                    ·
                      rfl

theorem cell22_1648695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1648695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648695 prefixEnd_1648695 := by exact prefixLift 1648695
  have htrace : WordTrace (prefixWord ++ tailWord_1648695) baseStart_1648695 baseEnd_1648695 := by
    simpa [prefixWord, tailWord_1648695, baseEnd_1648695] using wordTrace_append hprefix tailTrace_1648695
  have hstable : (prefixWord ++ tailWord_1648695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648695).length < 2 ^ (prefixWord ++ tailWord_1648695).sum := by decide
  have hdescent : baseEnd_1648695 < baseStart_1648695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648697 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_1648697 : Nat := 118140960795 + 1648697 * 2 ^ 59
def prefixEnd_1648697 : Nat := 4983230072969 + 3 ^ 40 * 1648697 * 2
def baseEnd_1648697 : Nat := 564382676417227466070191

theorem tailTrace_1648697 : CollatzResearch.WordTrace tailWord_1648697 prefixEnd_1648697 564382676417227466070191 := by
  unfold tailWord_1648697
  simp only [CollatzResearch.WordTrace]
  refine ⟨60132919708059818875376345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40088613138706545916917563 60132919708059818875376345)
  ·
    refine ⟨45099689781044864156532259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60132919708059818875376345 45099689781044864156532259)
    ·
      refine ⟨67649534671567296234798389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45099689781044864156532259 67649534671567296234798389)
      ·
        refine ⟨6342143875459434022012349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67649534671567296234798389 6342143875459434022012349)
        ·
          refine ⟨2378303953297287758254631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6342143875459434022012349 2378303953297287758254631)
          ·
            refine ⟨3567455929945931637381947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378303953297287758254631 3567455929945931637381947)
            ·
              refine ⟨5351183894918897456072921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567455929945931637381947 5351183894918897456072921)
              ·
                refine ⟨4013387921189173092054691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351183894918897456072921 4013387921189173092054691)
                ·
                  refine ⟨6020081881783759638082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013387921189173092054691 6020081881783759638082037)
                  ·
                    refine ⟨564382676417227466070191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6020081881783759638082037 564382676417227466070191)
                    ·
                      rfl

theorem cell22_1648697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_1648697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648697 prefixEnd_1648697 := by exact prefixLift 1648697
  have htrace : WordTrace (prefixWord ++ tailWord_1648697) baseStart_1648697 baseEnd_1648697 := by
    simpa [prefixWord, tailWord_1648697, baseEnd_1648697] using wordTrace_append hprefix tailTrace_1648697
  have hstable : (prefixWord ++ tailWord_1648697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648697).length < 2 ^ (prefixWord ++ tailWord_1648697).sum := by decide
  have hdescent : baseEnd_1648697 < baseStart_1648697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648746 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1648746 : Nat := 118140960795 + 1648746 * 2 ^ 59
def prefixEnd_1648746 : Nat := 4983230072969 + 3 ^ 40 * 1648746 * 2
def baseEnd_1648746 : Nat := 564399450118607671595041

theorem tailTrace_1648746 : CollatzResearch.WordTrace tailWord_1648746 prefixEnd_1648746 564399450118607671595041 := by
  unfold tailWord_1648746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033676721220575060977523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40089804589921533495940061 15033676721220575060977523)
  ·
    refine ⟨22550515081830862591466285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15033676721220575060977523 22550515081830862591466285)
    ·
      refine ⟨8456443155686573471799857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22550515081830862591466285 8456443155686573471799857)
      ·
        refine ⟨6342332366764930103849893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8456443155686573471799857 6342332366764930103849893)
        ·
          refine ⟨1189187318768424394471855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6342332366764930103849893 1189187318768424394471855)
          ·
            refine ⟨1783780978152636591707783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189187318768424394471855 1783780978152636591707783)
            ·
              refine ⟨2675671467228954887561675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783780978152636591707783 2675671467228954887561675)
              ·
                refine ⟨4013507200843432331342513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675671467228954887561675 4013507200843432331342513)
                ·
                  refine ⟨3010130400632574248506885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013507200843432331342513 3010130400632574248506885)
                  ·
                    refine ⟨564399450118607671595041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010130400632574248506885 564399450118607671595041)
                    ·
                      rfl

theorem cell22_1648746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1648746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648746 prefixEnd_1648746 := by exact prefixLift 1648746
  have htrace : WordTrace (prefixWord ++ tailWord_1648746) baseStart_1648746 baseEnd_1648746 := by
    simpa [prefixWord, tailWord_1648746, baseEnd_1648746] using wordTrace_append hprefix tailTrace_1648746
  have hstable : (prefixWord ++ tailWord_1648746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648746).length < 2 ^ (prefixWord ++ tailWord_1648746).sum := by decide
  have hdescent : baseEnd_1648746 < baseStart_1648746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648759 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 1, 3]
def baseStart_1648759 : Nat := 118140960795 + 1648759 * 2 ^ 59
def prefixEnd_1648759 : Nat := 4983230072969 + 3 ^ 40 * 1648759 * 2
def baseEnd_1648759 : Nat := 564403900284279971020001

theorem tailTrace_1648759 : CollatzResearch.WordTrace tailWord_1648759 prefixEnd_1648759 564403900284279971020001 := by
  unfold tailWord_1648759
  simp only [CollatzResearch.WordTrace]
  refine ⟨60135181033835203464133331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40090120689223468976088887 60135181033835203464133331)
  ·
    refine ⟨90202771550752805196199997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60135181033835203464133331 90202771550752805196199997)
    ·
      refine ⟨33826039331532301948574999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90202771550752805196199997 33826039331532301948574999)
      ·
        refine ⟨50739058997298452922862499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33826039331532301948574999 50739058997298452922862499)
        ·
          refine ⟨76108588495947679384293749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50739058997298452922862499 76108588495947679384293749)
          ·
            refine ⟨7135180171495094942277539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76108588495947679384293749 7135180171495094942277539)
            ·
              refine ⟨10702770257242642413416309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135180171495094942277539 10702770257242642413416309)
              ·
                refine ⟨1003384711616497726257779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10702770257242642413416309 1003384711616497726257779)
                ·
                  refine ⟨1505077067424746589386669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003384711616497726257779 1505077067424746589386669)
                  ·
                    refine ⟨564403900284279971020001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505077067424746589386669 564403900284279971020001)
                    ·
                      rfl

theorem cell22_1648759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_1648759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648759 prefixEnd_1648759 := by exact prefixLift 1648759
  have htrace : WordTrace (prefixWord ++ tailWord_1648759) baseStart_1648759 baseEnd_1648759 := by
    simpa [prefixWord, tailWord_1648759, baseEnd_1648759] using wordTrace_append hprefix tailTrace_1648759
  have hstable : (prefixWord ++ tailWord_1648759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648759).length < 2 ^ (prefixWord ++ tailWord_1648759).sum := by decide
  have hdescent : baseEnd_1648759 < baseStart_1648759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648776 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 1, 3]
def baseStart_1648776 : Nat := 118140960795 + 1648776 * 2 ^ 59
def prefixEnd_1648776 : Nat := 4983230072969 + 3 ^ 40 * 1648776 * 2
def baseEnd_1648776 : Nat := 564409719731697593344949

theorem tailTrace_1648776 : CollatzResearch.WordTrace tailWord_1648776 prefixEnd_1648776 564409719731697593344949 := by
  unfold tailWord_1648776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067900537386807683751091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40090534049849076911668121 30067900537386807683751091)
  ·
    refine ⟨45101850806080211525626637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30067900537386807683751091 45101850806080211525626637)
    ·
      refine ⟨16913194052280079322109989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45101850806080211525626637 16913194052280079322109989)
      ·
        refine ⟨3171223884802514872895623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16913194052280079322109989 3171223884802514872895623)
        ·
          refine ⟨4756835827203772309343435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171223884802514872895623 4756835827203772309343435)
          ·
            refine ⟨7135253740805658464015153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756835827203772309343435 7135253740805658464015153)
            ·
              refine ⟨5351440305604243848011365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7135253740805658464015153 5351440305604243848011365)
              ·
                refine ⟨1003395057300795721502131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5351440305604243848011365 1003395057300795721502131)
                ·
                  refine ⟨1505092585951193582253197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003395057300795721502131 1505092585951193582253197)
                  ·
                    refine ⟨564409719731697593344949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505092585951193582253197 564409719731697593344949)
                    ·
                      rfl

theorem cell22_1648776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_1648776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648776 prefixEnd_1648776 := by exact prefixLift 1648776
  have htrace : WordTrace (prefixWord ++ tailWord_1648776) baseStart_1648776 baseEnd_1648776 := by
    simpa [prefixWord, tailWord_1648776, baseEnd_1648776] using wordTrace_append hprefix tailTrace_1648776
  have hstable : (prefixWord ++ tailWord_1648776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648776).length < 2 ^ (prefixWord ++ tailWord_1648776).sum := by decide
  have hdescent : baseEnd_1648776 < baseStart_1648776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648810 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1648810 : Nat := 118140960795 + 1648810 * 2 ^ 59
def prefixEnd_1648810 : Nat := 4983230072969 + 3 ^ 40 * 1648810 * 2
def baseEnd_1648810 : Nat := 564421358626532837994845

theorem tailTrace_1648810 : CollatzResearch.WordTrace tailWord_1648810 prefixEnd_1648810 564421358626532837994845 := by
  unfold tailWord_1648810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034260289162609793559971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40091360771100292782826589 15034260289162609793559971)
  ·
    refine ⟨22551390433743914690339957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15034260289162609793559971 22551390433743914690339957)
    ·
      refine ⟨2114192853163492002219371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22551390433743914690339957 2114192853163492002219371)
      ·
        refine ⟨3171289279745238003329057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114192853163492002219371 3171289279745238003329057)
        ·
          refine ⟨2378466959808928502496793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3171289279745238003329057 2378466959808928502496793)
          ·
            refine ⟨1783850219856696376872595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2378466959808928502496793 1783850219856696376872595)
            ·
              refine ⟨2675775329785044565308893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783850219856696376872595 2675775329785044565308893)
              ·
                refine ⟨1003415748669391711990835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2675775329785044565308893 1003415748669391711990835)
                ·
                  refine ⟨1505123623004087567986253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003415748669391711990835 1505123623004087567986253)
                  ·
                    refine ⟨564421358626532837994845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505123623004087567986253 564421358626532837994845)
                    ·
                      rfl

theorem cell22_1648810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1648810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648810 prefixEnd_1648810 := by exact prefixLift 1648810
  have htrace : WordTrace (prefixWord ++ tailWord_1648810) baseStart_1648810 baseEnd_1648810 := by
    simpa [prefixWord, tailWord_1648810, baseEnd_1648810] using wordTrace_append hprefix tailTrace_1648810
  have hstable : (prefixWord ++ tailWord_1648810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648810).length < 2 ^ (prefixWord ++ tailWord_1648810).sum := by decide
  have hdescent : baseEnd_1648810 < baseStart_1648810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648815 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_1648815 : Nat := 118140960795 + 1648815 * 2 ^ 59
def prefixEnd_1648815 : Nat := 4983230072969 + 3 ^ 40 * 1648815 * 2
def baseEnd_1648815 : Nat := 564423070228714491619829

theorem tailTrace_1648815 : CollatzResearch.WordTrace tailWord_1648815 prefixEnd_1648815 564423070228714491619829 := by
  unfold tailWord_1648815
  simp only [CollatzResearch.WordTrace]
  refine ⟨60137223521632325028171899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40091482347754883352114599 60137223521632325028171899)
  ·
    refine ⟨90205835282448487542257849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60137223521632325028171899 90205835282448487542257849)
    ·
      refine ⟨67654376461836365656693387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90205835282448487542257849 67654376461836365656693387)
      ·
        refine ⟨101481564692754548485040081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67654376461836365656693387 101481564692754548485040081)
        ·
          refine ⟨76111173519565911363780061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101481564692754548485040081 76111173519565911363780061)
          ·
            refine ⟨28541690069837216761417523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76111173519565911363780061 28541690069837216761417523)
            ·
              refine ⟨42812535104755825142126285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28541690069837216761417523 42812535104755825142126285)
              ·
                refine ⟨16054700664283434428297357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42812535104755825142126285 16054700664283434428297357)
                ·
                  refine ⟨6020512749106287910611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16054700664283434428297357 6020512749106287910611509)
                  ·
                    refine ⟨564423070228714491619829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6020512749106287910611509 564423070228714491619829)
                    ·
                      rfl

theorem cell22_1648815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_1648815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648815 prefixEnd_1648815 := by exact prefixLift 1648815
  have htrace : WordTrace (prefixWord ++ tailWord_1648815) baseStart_1648815 baseEnd_1648815 := by
    simpa [prefixWord, tailWord_1648815, baseEnd_1648815] using wordTrace_append hprefix tailTrace_1648815
  have hstable : (prefixWord ++ tailWord_1648815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648815).length < 2 ^ (prefixWord ++ tailWord_1648815).sum := by decide
  have hdescent : baseEnd_1648815 < baseStart_1648815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648853 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1648853 : Nat := 118140960795 + 1648853 * 2 ^ 59
def prefixEnd_1648853 : Nat := 4983230072969 + 3 ^ 40 * 1648853 * 2
def baseEnd_1648853 : Nat := 564436078405295059169713

theorem tailTrace_1648853 : CollatzResearch.WordTrace tailWord_1648853 prefixEnd_1648853 564436078405295059169713 := by
  unfold tailWord_1648853
  simp only [CollatzResearch.WordTrace]
  refine ⟨60138609495494657518055213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40092406330329771678703475 60138609495494657518055213)
  ·
    refine ⟨22551978560810496569270705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60138609495494657518055213 22551978560810496569270705)
    ·
      refine ⟨16913983920607872426953029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22551978560810496569270705 16913983920607872426953029)
      ·
        refine ⟨3171371985113976080053693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16913983920607872426953029 3171371985113976080053693)
        ·
          refine ⟨1189264494417741030020135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3171371985113976080053693 1189264494417741030020135)
          ·
            refine ⟨1783896741626611545030203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189264494417741030020135 1783896741626611545030203)
            ·
              refine ⟨2675845112439917317545305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783896741626611545030203 2675845112439917317545305)
              ·
                refine ⟨2006883834329937988158979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675845112439917317545305 2006883834329937988158979)
                ·
                  refine ⟨3010325751494906982238469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006883834329937988158979 3010325751494906982238469)
                  ·
                    refine ⟨564436078405295059169713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010325751494906982238469 564436078405295059169713)
                    ·
                      rfl

theorem cell22_1648853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1648853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648853 prefixEnd_1648853 := by exact prefixLift 1648853
  have htrace : WordTrace (prefixWord ++ tailWord_1648853) baseStart_1648853 baseEnd_1648853 := by
    simpa [prefixWord, tailWord_1648853, baseEnd_1648853] using wordTrace_append hprefix tailTrace_1648853
  have hstable : (prefixWord ++ tailWord_1648853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648853).length < 2 ^ (prefixWord ++ tailWord_1648853).sum := by decide
  have hdescent : baseEnd_1648853 < baseStart_1648853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648892 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_1648892 : Nat := 118140960795 + 1648892 * 2 ^ 59
def prefixEnd_1648892 : Nat := 4983230072969 + 3 ^ 40 * 1648892 * 2
def baseEnd_1648892 : Nat := 564449428902311957444593

theorem tailTrace_1648892 : CollatzResearch.WordTrace tailWord_1648892 prefixEnd_1648892 564449428902311957444593 := by
  unfold tailWord_1648892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070015971176683589362465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40093354628235578119149953 30070015971176683589362465)
  ·
    refine ⟨22552511978382512692021849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30070015971176683589362465 22552511978382512692021849)
    ·
      refine ⟨16914383983786884519016387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22552511978382512692021849 16914383983786884519016387)
      ·
        refine ⟨25371575975680326778524581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16914383983786884519016387 25371575975680326778524581)
        ·
          refine ⟨4757170495440061270973359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25371575975680326778524581 4757170495440061270973359)
          ·
            refine ⟨7135755743160091906460039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757170495440061270973359 7135755743160091906460039)
            ·
              refine ⟨10703633614740137859690059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135755743160091906460039 10703633614740137859690059)
              ·
                refine ⟨16055450422110206789535089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703633614740137859690059 16055450422110206789535089)
                ·
                  refine ⟨12041587816582655092151317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16055450422110206789535089 12041587816582655092151317)
                  ·
                    refine ⟨564449428902311957444593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12041587816582655092151317 564449428902311957444593)
                    ·
                      rfl

theorem cell22_1648892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_1648892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648892 prefixEnd_1648892 := by exact prefixLift 1648892
  have htrace : WordTrace (prefixWord ++ tailWord_1648892) baseStart_1648892 baseEnd_1648892 := by
    simpa [prefixWord, tailWord_1648892, baseEnd_1648892] using wordTrace_append hprefix tailTrace_1648892
  have hstable : (prefixWord ++ tailWord_1648892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648892).length < 2 ^ (prefixWord ++ tailWord_1648892).sum := by decide
  have hdescent : baseEnd_1648892 < baseStart_1648892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648907 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 5]
def baseStart_1648907 : Nat := 118140960795 + 1648907 * 2 ^ 59
def prefixEnd_1648907 : Nat := 4983230072969 + 3 ^ 40 * 1648907 * 2
def baseEnd_1648907 : Nat := 188151521236285639439849

theorem tailTrace_1648907 : CollatzResearch.WordTrace tailWord_1648907 prefixEnd_1648907 188151521236285639439849 := by
  unfold tailWord_1648907
  simp only [CollatzResearch.WordTrace]
  refine ⟨60140579037299024740520975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40093719358199349827013983 60140579037299024740520975)
  ·
    refine ⟨90210868555948537110781463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60140579037299024740520975 90210868555948537110781463)
    ·
      refine ⟨135316302833922805666172195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90210868555948537110781463 135316302833922805666172195)
      ·
        refine ⟨202974454250884208499258293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135316302833922805666172195 202974454250884208499258293)
        ·
          refine ⟨19028855086020394546805465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202974454250884208499258293 19028855086020394546805465)
          ·
            refine ⟨14271641314515295910104099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19028855086020394546805465 14271641314515295910104099)
            ·
              refine ⟨21407461971772943865156149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14271641314515295910104099 21407461971772943865156149)
              ·
                refine ⟨2006949559853713487358389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21407461971772943865156149 2006949559853713487358389)
                ·
                  refine ⟨188151521236285639439849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2006949559853713487358389 188151521236285639439849)
                  ·
                    rfl

theorem cell22_1648907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 5].length) (baseStart_1648907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648907 prefixEnd_1648907 := by exact prefixLift 1648907
  have htrace : WordTrace (prefixWord ++ tailWord_1648907) baseStart_1648907 baseEnd_1648907 := by
    simpa [prefixWord, tailWord_1648907, baseEnd_1648907] using wordTrace_append hprefix tailTrace_1648907
  have hstable : (prefixWord ++ tailWord_1648907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648907).length < 2 ^ (prefixWord ++ tailWord_1648907).sum := by decide
  have hdescent : baseEnd_1648907 < baseStart_1648907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648928 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 1, 3]
def baseStart_1648928 : Nat := 118140960795 + 1648928 * 2 ^ 59
def prefixEnd_1648928 : Nat := 4983230072969 + 3 ^ 40 * 1648928 * 2
def baseEnd_1648928 : Nat := 564461752438019863544483

theorem tailTrace_1648928 : CollatzResearch.WordTrace tailWord_1648928 prefixEnd_1648928 564461752438019863544483 := by
  unfold tailWord_1648928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070672485111472663517719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40094229980148630218023625 30070672485111472663517719)
  ·
    refine ⟨45106008727667208995276579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30070672485111472663517719 45106008727667208995276579)
    ·
      refine ⟨67659013091500813492914869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45106008727667208995276579 67659013091500813492914869)
      ·
        refine ⟨6343032477328201264960769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67659013091500813492914869 6343032477328201264960769)
        ·
          refine ⟨4757274357996150948720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6343032477328201264960769 4757274357996150948720577)
          ·
            refine ⟨3567955768497113211540433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4757274357996150948720577 3567955768497113211540433)
            ·
              refine ⟨2675966826372834908655325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567955768497113211540433 2675966826372834908655325)
              ·
                refine ⟨1003487559889813090745747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2675966826372834908655325 1003487559889813090745747)
                ·
                  refine ⟨1505231339834719636118621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003487559889813090745747 1505231339834719636118621)
                  ·
                    refine ⟨564461752438019863544483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505231339834719636118621 564461752438019863544483)
                    ·
                      rfl

theorem cell22_1648928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_1648928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648928 prefixEnd_1648928 := by exact prefixLift 1648928
  have htrace : WordTrace (prefixWord ++ tailWord_1648928) baseStart_1648928 baseEnd_1648928 := by
    simpa [prefixWord, tailWord_1648928, baseEnd_1648928] using wordTrace_append hprefix tailTrace_1648928
  have hstable : (prefixWord ++ tailWord_1648928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648928).length < 2 ^ (prefixWord ++ tailWord_1648928).sum := by decide
  have hdescent : baseEnd_1648928 < baseStart_1648928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648941 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1648941 : Nat := 118140960795 + 1648941 * 2 ^ 59
def prefixEnd_1648941 : Nat := 4983230072969 + 3 ^ 40 * 1648941 * 2
def baseEnd_1648941 : Nat := 188155400867897387656481

theorem tailTrace_1648941 : CollatzResearch.WordTrace tailWord_1648941 prefixEnd_1648941 188155400867897387656481 := by
  unfold tailWord_1648941
  simp only [CollatzResearch.WordTrace]
  refine ⟨60141819119175848547258677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40094546079450565698172451 60141819119175848547258677)
  ·
    refine ⟨5638295542422735801305501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60141819119175848547258677 5638295542422735801305501)
    ·
      refine ⟨2114360828408525925489563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5638295542422735801305501 2114360828408525925489563)
      ·
        refine ⟨3171541242612788888234345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114360828408525925489563 3171541242612788888234345)
        ·
          refine ⟨2378655931959591666175759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3171541242612788888234345 2378655931959591666175759)
          ·
            refine ⟨3567983897939387499263639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378655931959591666175759 3567983897939387499263639)
            ·
              refine ⟨5351975846909081248895459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567983897939387499263639 5351975846909081248895459)
              ·
                refine ⟨8027963770363621873343189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351975846909081248895459 8027963770363621873343189)
                ·
                  refine ⟨188155400867897387656481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8027963770363621873343189 188155400867897387656481)
                  ·
                    rfl

theorem cell22_1648941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1648941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648941 prefixEnd_1648941 := by exact prefixLift 1648941
  have htrace : WordTrace (prefixWord ++ tailWord_1648941) baseStart_1648941 baseEnd_1648941 := by
    simpa [prefixWord, tailWord_1648941, baseEnd_1648941] using wordTrace_append hprefix tailTrace_1648941
  have hstable : (prefixWord ++ tailWord_1648941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648941).length < 2 ^ (prefixWord ++ tailWord_1648941).sum := by decide
  have hdescent : baseEnd_1648941 < baseStart_1648941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648952 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_1648952 : Nat := 118140960795 + 1648952 * 2 ^ 59
def prefixEnd_1648952 : Nat := 4983230072969 + 3 ^ 40 * 1648952 * 2
def baseEnd_1648952 : Nat := 188156656042830600314803

theorem tailTrace_1648952 : CollatzResearch.WordTrace tailWord_1648952 prefixEnd_1648952 188156656042830600314803 := by
  unfold tailWord_1648952
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071110161067998712954555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40094813548090664950606073 30071110161067998712954555)
  ·
    refine ⟨45106665241601998069431833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30071110161067998712954555 45106665241601998069431833)
    ·
      refine ⟨33829998931201498552073875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45106665241601998069431833 33829998931201498552073875)
      ·
        refine ⟨50744998396802247828110813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33829998931201498552073875 50744998396802247828110813)
        ·
          refine ⟨19029374398800842935541555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50744998396802247828110813 19029374398800842935541555)
          ·
            refine ⟨28544061598201264403312333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19029374398800842935541555 28544061598201264403312333)
            ·
              refine ⟨10704023099325474151242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28544061598201264403312333 10704023099325474151242125)
              ·
                refine ⟨4014008662247052806715797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10704023099325474151242125 4014008662247052806715797)
                ·
                  refine ⟨188156656042830600314803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4014008662247052806715797 188156656042830600314803)
                  ·
                    rfl

theorem cell22_1648952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_1648952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648952 prefixEnd_1648952 := by exact prefixLift 1648952
  have htrace : WordTrace (prefixWord ++ tailWord_1648952) baseStart_1648952 baseEnd_1648952 := by
    simpa [prefixWord, tailWord_1648952, baseEnd_1648952] using wordTrace_append hprefix tailTrace_1648952
  have hstable : (prefixWord ++ tailWord_1648952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648952).length < 2 ^ (prefixWord ++ tailWord_1648952).sum := by decide
  have hdescent : baseEnd_1648952 < baseStart_1648952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648997 : List Nat := [1, 3, 1, 3, 1, 3, 10]
def baseStart_1648997 : Nat := 118140960795 + 1648997 * 2 ^ 59
def prefixEnd_1648997 : Nat := 4983230072969 + 3 ^ 40 * 1648997 * 2
def baseEnd_1648997 : Nat := 20906865649930617909973

theorem tailTrace_1648997 : CollatzResearch.WordTrace tailWord_1648997 prefixEnd_1648997 20906865649930617909973 := by
  unfold tailWord_1648997
  simp only [CollatzResearch.WordTrace]
  refine ⟨60143861606972970111297245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40095907737981980074198163 60143861606972970111297245)
  ·
    refine ⟨22553948102614863791736467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60143861606972970111297245 22553948102614863791736467)
    ·
      refine ⟨33830922153922295687604701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22553948102614863791736467 33830922153922295687604701)
      ·
        refine ⟨12686595807720860882851763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33830922153922295687604701 12686595807720860882851763)
        ·
          refine ⟨19029893711581291324277645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12686595807720860882851763 19029893711581291324277645)
          ·
            refine ⟨7136210141842984246604117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19029893711581291324277645 7136210141842984246604117)
            ·
              refine ⟨20906865649930617909973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7136210141842984246604117 20906865649930617909973)
              ·
                rfl

theorem cell22_1648997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 10].length) (baseStart_1648997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648997 prefixEnd_1648997 := by exact prefixLift 1648997
  have htrace : WordTrace (prefixWord ++ tailWord_1648997) baseStart_1648997 baseEnd_1648997 := by
    simpa [prefixWord, tailWord_1648997, baseEnd_1648997] using wordTrace_append hprefix tailTrace_1648997
  have hstable : (prefixWord ++ tailWord_1648997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648997).length < 2 ^ (prefixWord ++ tailWord_1648997).sum := by decide
  have hdescent : baseEnd_1648997 < baseStart_1648997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648999 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1648999 : Nat := 118140960795 + 1648999 * 2 ^ 59
def prefixEnd_1648999 : Nat := 4983230072969 + 3 ^ 40 * 1648999 * 2
def baseEnd_1648999 : Nat := 564486057188999345019265

theorem tailTrace_1648999 : CollatzResearch.WordTrace tailWord_1648999 prefixEnd_1648999 564486057188999345019265 := by
  unfold tailWord_1648999
  simp only [CollatzResearch.WordTrace]
  refine ⟨60143934552965724452870051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40095956368643816301913367 60143934552965724452870051)
  ·
    refine ⟨90215901829448586679305077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60143934552965724452870051 90215901829448586679305077)
    ·
      refine ⟨8457740796510805001184851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90215901829448586679305077 8457740796510805001184851)
      ·
        refine ⟨12686611194766207501777277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457740796510805001184851 12686611194766207501777277)
        ·
          refine ⟨4757479198037327813166479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12686611194766207501777277 4757479198037327813166479)
          ·
            refine ⟨7136218797055991719749719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757479198037327813166479 7136218797055991719749719)
            ·
              refine ⟨10704328195583987579624579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136218797055991719749719 10704328195583987579624579)
              ·
                refine ⟨16056492293375981369436869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704328195583987579624579 16056492293375981369436869)
                ·
                  refine ⟨3010592305007996506769413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16056492293375981369436869 3010592305007996506769413)
                  ·
                    refine ⟨564486057188999345019265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010592305007996506769413 564486057188999345019265)
                    ·
                      rfl

theorem cell22_1648999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1648999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1648999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1648999 prefixEnd_1648999 := by exact prefixLift 1648999
  have htrace : WordTrace (prefixWord ++ tailWord_1648999) baseStart_1648999 baseEnd_1648999 := by
    simpa [prefixWord, tailWord_1648999, baseEnd_1648999] using wordTrace_append hprefix tailTrace_1648999
  have hstable : (prefixWord ++ tailWord_1648999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648999).length < 2 ^ (prefixWord ++ tailWord_1648999).sum := by decide
  have hdescent : baseEnd_1648999 < baseStart_1648999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649029 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_1649029 : Nat := 118140960795 + 1649029 * 2 ^ 59
def prefixEnd_1649029 : Nat := 4983230072969 + 3 ^ 40 * 1649029 * 2
def baseEnd_1649029 : Nat := 564496326802089266769173

theorem tailTrace_1649029 : CollatzResearch.WordTrace tailWord_1649029 prefixEnd_1649029 564496326802089266769173 := by
  unfold tailWord_1649029
  simp only [CollatzResearch.WordTrace]
  refine ⟨60145028742857039576462141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40096685828571359717641427 60145028742857039576462141)
  ·
    refine ⟨22554385778571389841173303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60145028742857039576462141 22554385778571389841173303)
    ·
      refine ⟨33831578667857084761759955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22554385778571389841173303 33831578667857084761759955)
      ·
        refine ⟨50747368001785627142639933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33831578667857084761759955 50747368001785627142639933)
        ·
          refine ⟨19030263000669610178489975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50747368001785627142639933 19030263000669610178489975)
          ·
            refine ⟨28545394501004415267734963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19030263000669610178489975 28545394501004415267734963)
            ·
              refine ⟨42818091751506622901602445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28545394501004415267734963 42818091751506622901602445)
              ·
                refine ⟨16056784406814983588100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42818091751506622901602445 16056784406814983588100917)
                ·
                  refine ⟨1505323538138904711384461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16056784406814983588100917 1505323538138904711384461)
                  ·
                    refine ⟨564496326802089266769173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505323538138904711384461 564496326802089266769173)
                    ·
                      rfl

theorem cell22_1649029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_1649029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649029 prefixEnd_1649029 := by exact prefixLift 1649029
  have htrace : WordTrace (prefixWord ++ tailWord_1649029) baseStart_1649029 baseEnd_1649029 := by
    simpa [prefixWord, tailWord_1649029, baseEnd_1649029] using wordTrace_append hprefix tailTrace_1649029
  have hstable : (prefixWord ++ tailWord_1649029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649029).length < 2 ^ (prefixWord ++ tailWord_1649029).sum := by decide
  have hdescent : baseEnd_1649029 < baseStart_1649029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649059 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 5]
def baseStart_1649059 : Nat := 118140960795 + 1649059 * 2 ^ 59
def prefixEnd_1649059 : Nat := 4983230072969 + 3 ^ 40 * 1649059 * 2
def baseEnd_1649059 : Nat := 188168865471726396173027

theorem tailTrace_1649059 : CollatzResearch.WordTrace tailWord_1649059 prefixEnd_1649059 188168865471726396173027 := by
  unfold tailWord_1649059
  simp only [CollatzResearch.WordTrace]
  refine ⟨60146122932748354700054231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40097415288498903133369487 60146122932748354700054231)
  ·
    refine ⟨90219184399122532050081347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60146122932748354700054231 90219184399122532050081347)
    ·
      refine ⟨135328776598683798075122021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90219184399122532050081347 135328776598683798075122021)
      ·
        refine ⟨25374145612253212139085379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135328776598683798075122021 25374145612253212139085379)
        ·
          refine ⟨38061218418379818208628069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25374145612253212139085379 38061218418379818208628069)
          ·
            refine ⟨7136478453446215914117763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38061218418379818208628069 7136478453446215914117763)
            ·
              refine ⟨10704717680169323871176645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136478453446215914117763 10704717680169323871176645)
              ·
                refine ⟨2007134565031748225845621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10704717680169323871176645 2007134565031748225845621)
                ·
                  refine ⟨188168865471726396173027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2007134565031748225845621 188168865471726396173027)
                  ·
                    rfl

theorem cell22_1649059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 5].length) (baseStart_1649059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649059 prefixEnd_1649059 := by exact prefixLift 1649059
  have htrace : WordTrace (prefixWord ++ tailWord_1649059) baseStart_1649059 baseEnd_1649059 := by
    simpa [prefixWord, tailWord_1649059, baseEnd_1649059] using wordTrace_append hprefix tailTrace_1649059
  have hstable : (prefixWord ++ tailWord_1649059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649059).length < 2 ^ (prefixWord ++ tailWord_1649059).sum := by decide
  have hdescent : baseEnd_1649059 < baseStart_1649059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649074 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1649074 : Nat := 118140960795 + 1649074 * 2 ^ 59
def prefixEnd_1649074 : Nat := 4983230072969 + 3 ^ 40 * 1649074 * 2
def baseEnd_1649074 : Nat := 564511731221724149394035

theorem tailTrace_1649074 : CollatzResearch.WordTrace tailWord_1649074 prefixEnd_1649074 564511731221724149394035 := by
  unfold tailWord_1649074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15036667506923503065462569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40097780018462674841233517 15036667506923503065462569)
  ·
    refine ⟨11277500630192627299096927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15036667506923503065462569 11277500630192627299096927)
    ·
      refine ⟨16916250945288940948645391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11277500630192627299096927 16916250945288940948645391)
      ·
        refine ⟨25374376417933411422968087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16916250945288940948645391 25374376417933411422968087)
        ·
          refine ⟨38061564626900117134452131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25374376417933411422968087 38061564626900117134452131)
          ·
            refine ⟨57092346940350175701678197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38061564626900117134452131 57092346940350175701678197)
            ·
              refine ⟨5352407525657828972032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57092346940350175701678197 5352407525657828972032331)
              ·
                refine ⟨8028611288486743458048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352407525657828972032331 8028611288486743458048497)
                ·
                  refine ⟨6021458466365057593536373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8028611288486743458048497 6021458466365057593536373)
                  ·
                    refine ⟨564511731221724149394035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6021458466365057593536373 564511731221724149394035)
                    ·
                      rfl

theorem cell22_1649074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1649074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649074 prefixEnd_1649074 := by exact prefixLift 1649074
  have htrace : WordTrace (prefixWord ++ tailWord_1649074) baseStart_1649074 baseEnd_1649074 := by
    simpa [prefixWord, tailWord_1649074, baseEnd_1649074] using wordTrace_append hprefix tailTrace_1649074
  have hstable : (prefixWord ++ tailWord_1649074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649074).length < 2 ^ (prefixWord ++ tailWord_1649074).sum := by decide
  have hdescent : baseEnd_1649074 < baseStart_1649074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649121 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 4]
def baseStart_1649121 : Nat := 118140960795 + 1649121 * 2 ^ 59
def prefixEnd_1649121 : Nat := 4983230072969 + 3 ^ 40 * 1649121 * 2
def baseEnd_1649121 : Nat := 188175940094077231156297

theorem tailTrace_1649121 : CollatzResearch.WordTrace tailWord_1649121 prefixEnd_1649121 188175940094077231156297 := by
  unfold tailWord_1649121
  simp only [CollatzResearch.WordTrace]
  refine ⟨60148384258523739288811217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40098922839015826192540811 60148384258523739288811217)
  ·
    refine ⟨45111288193892804466608413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60148384258523739288811217 45111288193892804466608413)
    ·
      refine ⟨16916733072709801674978155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45111288193892804466608413 16916733072709801674978155)
      ·
        refine ⟨25375099609064702512467233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16916733072709801674978155 25375099609064702512467233)
        ·
          refine ⟨19031324706798526884350425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25375099609064702512467233 19031324706798526884350425)
          ·
            refine ⟨14273493530098895163262819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19031324706798526884350425 14273493530098895163262819)
            ·
              refine ⟨21410240295148342744894229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14273493530098895163262819 21410240295148342744894229)
              ·
                refine ⟨1003605013835078566166917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21410240295148342744894229 1003605013835078566166917)
                ·
                  refine ⟨188175940094077231156297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003605013835078566166917 188175940094077231156297)
                  ·
                    rfl

theorem cell22_1649121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_1649121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649121 prefixEnd_1649121 := by exact prefixLift 1649121
  have htrace : WordTrace (prefixWord ++ tailWord_1649121) baseStart_1649121 baseEnd_1649121 := by
    simpa [prefixWord, tailWord_1649121, baseEnd_1649121] using wordTrace_append hprefix tailTrace_1649121
  have hstable : (prefixWord ++ tailWord_1649121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649121).length < 2 ^ (prefixWord ++ tailWord_1649121).sum := by decide
  have hdescent : baseEnd_1649121 < baseStart_1649121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649149 : List Nat := [1, 4, 1, 1, 1, 3, 3, 8]
def baseStart_1649149 : Nat := 118140960795 + 1649149 * 2 ^ 59
def prefixEnd_1649149 : Nat := 4983230072969 + 3 ^ 40 * 1649149 * 2
def baseEnd_1649149 : Nat := 62726378361605439307645

theorem tailTrace_1649149 : CollatzResearch.WordTrace tailWord_1649149 prefixEnd_1649149 62726378361605439307645 := by
  unfold tailWord_1649149
  simp only [CollatzResearch.WordTrace]
  refine ⟨60149405502422300070830501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40099603668281533380553667 60149405502422300070830501)
  ·
    refine ⟨11278013531704181263280719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60149405502422300070830501 11278013531704181263280719)
    ·
      refine ⟨16917020297556271894921079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11278013531704181263280719 16917020297556271894921079)
      ·
        refine ⟨25375530446334407842381619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16917020297556271894921079 25375530446334407842381619)
        ·
          refine ⟨38063295669501611763572429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25375530446334407842381619 38063295669501611763572429)
          ·
            refine ⟨14273735876063104411339661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38063295669501611763572429 14273735876063104411339661)
            ·
              refine ⟨5352650953523664154252373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14273735876063104411339661 5352650953523664154252373)
              ·
                refine ⟨62726378361605439307645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5352650953523664154252373 62726378361605439307645)
                ·
                  rfl

theorem cell22_1649149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 8].length) (baseStart_1649149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649149 prefixEnd_1649149 := by exact prefixLift 1649149
  have htrace : WordTrace (prefixWord ++ tailWord_1649149) baseStart_1649149 baseEnd_1649149 := by
    simpa [prefixWord, tailWord_1649149, baseEnd_1649149] using wordTrace_append hprefix tailTrace_1649149
  have hstable : (prefixWord ++ tailWord_1649149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649149).length < 2 ^ (prefixWord ++ tailWord_1649149).sum := by decide
  have hdescent : baseEnd_1649149 < baseStart_1649149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649166 : List Nat := [4, 1, 1, 2, 3, 3, 8]
def baseStart_1649166 : Nat := 118140960795 + 1649166 * 2 ^ 59
def prefixEnd_1649166 : Nat := 4983230072969 + 3 ^ 40 * 1649166 * 2
def baseEnd_1649166 : Nat := 20909008322291354670139

theorem tailTrace_1649166 : CollatzResearch.WordTrace tailWord_1649166 prefixEnd_1649166 20909008322291354670139 := by
  unfold tailWord_1649166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7518753192920088996774919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40100017028907141316132901 7518753192920088996774919)
  ·
    refine ⟨11278129789380133495162379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7518753192920088996774919 11278129789380133495162379)
    ·
      refine ⟨16917194684070200242743569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11278129789380133495162379 16917194684070200242743569)
      ·
        refine ⟨12687896013052650182057677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16917194684070200242743569 12687896013052650182057677)
        ·
          refine ⟨4757961004894743818271629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12687896013052650182057677 4757961004894743818271629)
          ·
            refine ⟨1784235376835528931851861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4757961004894743818271629 1784235376835528931851861)
            ·
              refine ⟨20909008322291354670139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1784235376835528931851861 20909008322291354670139)
              ·
                rfl

theorem cell22_1649166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 8].length) (baseStart_1649166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649166 prefixEnd_1649166 := by exact prefixLift 1649166
  have htrace : WordTrace (prefixWord ++ tailWord_1649166) baseStart_1649166 baseEnd_1649166 := by
    simpa [prefixWord, tailWord_1649166, baseEnd_1649166] using wordTrace_append hprefix tailTrace_1649166
  have hstable : (prefixWord ++ tailWord_1649166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649166).length < 2 ^ (prefixWord ++ tailWord_1649166).sum := by decide
  have hdescent : baseEnd_1649166 < baseStart_1649166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649172 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1649172 : Nat := 118140960795 + 1649172 * 2 ^ 59
def prefixEnd_1649172 : Nat := 4983230072969 + 3 ^ 40 * 1649172 * 2
def baseEnd_1649172 : Nat := 188181759541494853481245

theorem tailTrace_1649172 : CollatzResearch.WordTrace tailWord_1649172 prefixEnd_1649172 188181759541494853481245 := by
  unfold tailWord_1649172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30075122190669487499458885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40100162920892649999278513 30075122190669487499458885)
  ·
    refine ⟨5639085410750528906148541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30075122190669487499458885 5639085410750528906148541)
    ·
      refine ⟨2114657029031448339805703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5639085410750528906148541 2114657029031448339805703)
      ·
        refine ⟨3171985543547172509708555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114657029031448339805703 3171985543547172509708555)
        ·
          refine ⟨4757978315320758764562833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171985543547172509708555 4757978315320758764562833)
          ·
            refine ⟨3568483736490569073422125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4757978315320758764562833 3568483736490569073422125)
            ·
              refine ⟨1338181401183963402533297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3568483736490569073422125 1338181401183963402533297)
              ·
                refine ⟨1003636050887972551899973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338181401183963402533297 1003636050887972551899973)
                ·
                  refine ⟨188181759541494853481245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003636050887972551899973 188181759541494853481245)
                  ·
                    rfl

theorem cell22_1649172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1649172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649172 prefixEnd_1649172 := by exact prefixLift 1649172
  have htrace : WordTrace (prefixWord ++ tailWord_1649172) baseStart_1649172 baseEnd_1649172 := by
    simpa [prefixWord, tailWord_1649172, baseEnd_1649172] using wordTrace_append hprefix tailTrace_1649172
  have hstable : (prefixWord ++ tailWord_1649172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649172).length < 2 ^ (prefixWord ++ tailWord_1649172).sum := by decide
  have hdescent : baseEnd_1649172 < baseStart_1649172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649258 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1649258 : Nat := 118140960795 + 1649258 * 2 ^ 59
def prefixEnd_1649258 : Nat := 4983230072969 + 3 ^ 40 * 1649258 * 2
def baseEnd_1649258 : Nat := 564574718182009002793471

theorem tailTrace_1649258 : CollatzResearch.WordTrace tailWord_1649258 prefixEnd_1649258 564574718182009002793471 := by
  unfold tailWord_1649258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038345264756852921637107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40102254039351607791032285 15038345264756852921637107)
  ·
    refine ⟨22557517897135279382455661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15038345264756852921637107 22557517897135279382455661)
    ·
      refine ⟨8459069211425729768420873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22557517897135279382455661 8459069211425729768420873)
      ·
        refine ⟨6344301908569297326315655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8459069211425729768420873 6344301908569297326315655)
        ·
          refine ⟨9516452862853945989473483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344301908569297326315655 9516452862853945989473483)
          ·
            refine ⟨14274679294280918984210225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9516452862853945989473483 14274679294280918984210225)
            ·
              refine ⟨10706009470710689238157669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14274679294280918984210225 10706009470710689238157669)
              ·
                refine ⟨2007376775758254232154563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10706009470710689238157669 2007376775758254232154563)
                ·
                  refine ⟨3011065163637381348231845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007376775758254232154563 3011065163637381348231845)
                  ·
                    refine ⟨564574718182009002793471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011065163637381348231845 564574718182009002793471)
                    ·
                      rfl

theorem cell22_1649258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1649258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649258 prefixEnd_1649258 := by exact prefixLift 1649258
  have htrace : WordTrace (prefixWord ++ tailWord_1649258) baseStart_1649258 baseEnd_1649258 := by
    simpa [prefixWord, tailWord_1649258, baseEnd_1649258] using wordTrace_append hprefix tailTrace_1649258
  have hstable : (prefixWord ++ tailWord_1649258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649258).length < 2 ^ (prefixWord ++ tailWord_1649258).sum := by decide
  have hdescent : baseEnd_1649258 < baseStart_1649258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649271 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1649271 : Nat := 118140960795 + 1649271 * 2 ^ 59
def prefixEnd_1649271 : Nat := 4983230072969 + 3 ^ 40 * 1649271 * 2
def baseEnd_1649271 : Nat := 564579168347681302218431

theorem tailTrace_1649271 : CollatzResearch.WordTrace tailWord_1649271 prefixEnd_1649271 564579168347681302218431 := by
  unfold tailWord_1649271
  simp only [CollatzResearch.WordTrace]
  refine ⟨60153855207980314906771667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40102570138653543271181111 60153855207980314906771667)
  ·
    refine ⟨90230782811970472360157501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60153855207980314906771667 90230782811970472360157501)
    ·
      refine ⟨33836543554488927135059063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90230782811970472360157501 33836543554488927135059063)
      ·
        refine ⟨50754815331733390702588595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33836543554488927135059063 50754815331733390702588595)
        ·
          refine ⟨76132222997600086053882893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50754815331733390702588595 76132222997600086053882893)
          ·
            refine ⟨28549583624100032270206085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76132222997600086053882893 28549583624100032270206085)
            ·
              refine ⟨5353046929518756050663641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28549583624100032270206085 5353046929518756050663641)
              ·
                refine ⟨4014785197139067037997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353046929518756050663641 4014785197139067037997731)
                ·
                  refine ⟨6022177795708600556996597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014785197139067037997731 6022177795708600556996597)
                  ·
                    refine ⟨564579168347681302218431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6022177795708600556996597 564579168347681302218431)
                    ·
                      rfl

theorem cell22_1649271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1649271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649271 prefixEnd_1649271 := by exact prefixLift 1649271
  have htrace : WordTrace (prefixWord ++ tailWord_1649271) baseStart_1649271 baseEnd_1649271 := by
    simpa [prefixWord, tailWord_1649271, baseEnd_1649271] using wordTrace_append hprefix tailTrace_1649271
  have hstable : (prefixWord ++ tailWord_1649271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649271).length < 2 ^ (prefixWord ++ tailWord_1649271).sum := by decide
  have hdescent : baseEnd_1649271 < baseStart_1649271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649273 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 4]
def baseStart_1649273 : Nat := 118140960795 + 1649273 * 2 ^ 59
def prefixEnd_1649273 : Nat := 4983230072969 + 3 ^ 40 * 1649273 * 2
def baseEnd_1649273 : Nat := 188193284329517987889475

theorem tailTrace_1649273 : CollatzResearch.WordTrace tailWord_1649273 prefixEnd_1649273 188193284329517987889475 := by
  unfold tailWord_1649273
  simp only [CollatzResearch.WordTrace]
  refine ⟨60153928153973069248344473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40102618769315379498896315 60153928153973069248344473)
  ·
    refine ⟨45115446115479801936258355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60153928153973069248344473 45115446115479801936258355)
    ·
      refine ⟨67673169173219702904387533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45115446115479801936258355 67673169173219702904387533)
      ·
        refine ⟨25377438439957388589145325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67673169173219702904387533 25377438439957388589145325)
        ·
          refine ⟨9516539414984020720929497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25377438439957388589145325 9516539414984020720929497)
          ·
            refine ⟨7137404561238015540697123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9516539414984020720929497 7137404561238015540697123)
            ·
              refine ⟨10706106841857023311045685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137404561238015540697123 10706106841857023311045685)
              ·
                refine ⟨1003697516424095935410533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10706106841857023311045685 1003697516424095935410533)
                ·
                  refine ⟨188193284329517987889475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003697516424095935410533 188193284329517987889475)
                  ·
                    rfl

theorem cell22_1649273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_1649273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649273 prefixEnd_1649273 := by exact prefixLift 1649273
  have htrace : WordTrace (prefixWord ++ tailWord_1649273) baseStart_1649273 baseEnd_1649273 := by
    simpa [prefixWord, tailWord_1649273, baseEnd_1649273] using wordTrace_append hprefix tailTrace_1649273
  have hstable : (prefixWord ++ tailWord_1649273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649273).length < 2 ^ (prefixWord ++ tailWord_1649273).sum := by decide
  have hdescent : baseEnd_1649273 < baseStart_1649273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649305 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_1649305 : Nat := 118140960795 + 1649305 * 2 ^ 59
def prefixEnd_1649305 : Nat := 4983230072969 + 3 ^ 40 * 1649305 * 2
def baseEnd_1649305 : Nat := 564590807242516546868327

theorem tailTrace_1649305 : CollatzResearch.WordTrace tailWord_1649305 prefixEnd_1649305 564590807242516546868327 := by
  unfold tailWord_1649305
  simp only [CollatzResearch.WordTrace]
  refine ⟨60155095289857138713509369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40103396859904759142339579 60155095289857138713509369)
  ·
    refine ⟨45116321467392854035132027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60155095289857138713509369 45116321467392854035132027)
    ·
      refine ⟨67674482201089281052698041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45116321467392854035132027 67674482201089281052698041)
      ·
        refine ⟨50755861650816960789523531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67674482201089281052698041 50755861650816960789523531)
        ·
          refine ⟨76133792476225441184285297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50755861650816960789523531 76133792476225441184285297)
          ·
            refine ⟨57100344357169080888213973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76133792476225441184285297 57100344357169080888213973)
            ·
              refine ⟨1338289320871150333317515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57100344357169080888213973 1338289320871150333317515)
              ·
                refine ⟨2007433981306725499976273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338289320871150333317515 2007433981306725499976273)
                ·
                  refine ⟨1505575485980044124982205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2007433981306725499976273 1505575485980044124982205)
                  ·
                    refine ⟨564590807242516546868327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505575485980044124982205 564590807242516546868327)
                    ·
                      rfl

theorem cell22_1649305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_1649305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649305 prefixEnd_1649305 := by exact prefixLift 1649305
  have htrace : WordTrace (prefixWord ++ tailWord_1649305) baseStart_1649305 baseEnd_1649305 := by
    simpa [prefixWord, tailWord_1649305, baseEnd_1649305] using wordTrace_append hprefix tailTrace_1649305
  have hstable : (prefixWord ++ tailWord_1649305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649305).length < 2 ^ (prefixWord ++ tailWord_1649305).sum := by decide
  have hdescent : baseEnd_1649305 < baseStart_1649305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649316 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1649316 : Nat := 118140960795 + 1649316 * 2 ^ 59
def prefixEnd_1649316 : Nat := 4983230072969 + 3 ^ 40 * 1649316 * 2
def baseEnd_1649316 : Nat := 564594572767316184843293

theorem tailTrace_1649316 : CollatzResearch.WordTrace tailWord_1649316 prefixEnd_1649316 564594572767316184843293 := by
  unfold tailWord_1649316
  simp only [CollatzResearch.WordTrace]
  refine ⟨30077748246408643796079901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40103664328544858394773201 30077748246408643796079901)
  ·
    refine ⟨11279155592403241423529963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30077748246408643796079901 11279155592403241423529963)
    ·
      refine ⟨16918733388604862135294945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279155592403241423529963 16918733388604862135294945)
      ·
        refine ⟨12689050041453646601471209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16918733388604862135294945 12689050041453646601471209)
        ·
          refine ⟨9516787531090234951103407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12689050041453646601471209 9516787531090234951103407)
          ·
            refine ⟨14275181296635352426655111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9516787531090234951103407 14275181296635352426655111)
            ·
              refine ⟨21412771944953028639982667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14275181296635352426655111 21412771944953028639982667)
              ·
                refine ⟨32119157917429542959974001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21412771944953028639982667 32119157917429542959974001)
                ·
                  refine ⟨24089368438072157219980501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32119157917429542959974001 24089368438072157219980501)
                  ·
                    refine ⟨564594572767316184843293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24089368438072157219980501 564594572767316184843293)
                    ·
                      rfl

theorem cell22_1649316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1649316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649316 prefixEnd_1649316 := by exact prefixLift 1649316
  have htrace : WordTrace (prefixWord ++ tailWord_1649316) baseStart_1649316 baseEnd_1649316 := by
    simpa [prefixWord, tailWord_1649316, baseEnd_1649316] using wordTrace_append hprefix tailTrace_1649316
  have hstable : (prefixWord ++ tailWord_1649316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649316).length < 2 ^ (prefixWord ++ tailWord_1649316).sum := by decide
  have hdescent : baseEnd_1649316 < baseStart_1649316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649361 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1649361 : Nat := 118140960795 + 1649361 * 2 ^ 59
def prefixEnd_1649361 : Nat := 4983230072969 + 3 ^ 40 * 1649361 * 2
def baseEnd_1649361 : Nat := 564609977186951067468155

theorem tailTrace_1649361 : CollatzResearch.WordTrace tailWord_1649361 prefixEnd_1649361 564609977186951067468155 := by
  unfold tailWord_1649361
  simp only [CollatzResearch.WordTrace]
  refine ⟨60157137777654260277547937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40104758518436173518365291 60157137777654260277547937)
  ·
    refine ⟨45117853333240695208160953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60157137777654260277547937 45117853333240695208160953)
    ·
      refine ⟨33838389999930521406120715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45117853333240695208160953 33838389999930521406120715)
      ·
        refine ⟨50757584999895782109181073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33838389999930521406120715 50757584999895782109181073)
        ·
          refine ⟨38068188749921836581885805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50757584999895782109181073 38068188749921836581885805)
          ·
            refine ⟨14275570781220688718207177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38068188749921836581885805 14275570781220688718207177)
            ·
              refine ⟨10706678085915516538655383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14275570781220688718207177 10706678085915516538655383)
              ·
                refine ⟨16060017128873274807983075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10706678085915516538655383 16060017128873274807983075)
                ·
                  refine ⟨24090025693309912211974613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16060017128873274807983075 24090025693309912211974613)
                  ·
                    refine ⟨564609977186951067468155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24090025693309912211974613 564609977186951067468155)
                    ·
                      rfl

theorem cell22_1649361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1649361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649361 prefixEnd_1649361 := by exact prefixLift 1649361
  have htrace : WordTrace (prefixWord ++ tailWord_1649361) baseStart_1649361 baseEnd_1649361 := by
    simpa [prefixWord, tailWord_1649361, baseEnd_1649361] using wordTrace_append hprefix tailTrace_1649361
  have hstable : (prefixWord ++ tailWord_1649361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649361).length < 2 ^ (prefixWord ++ tailWord_1649361).sum := by decide
  have hdescent : baseEnd_1649361 < baseStart_1649361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649410 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1649410 : Nat := 118140960795 + 1649410 * 2 ^ 59
def prefixEnd_1649410 : Nat := 4983230072969 + 3 ^ 40 * 1649410 * 2
def baseEnd_1649410 : Nat := 564626750888331272993005

theorem tailTrace_1649410 : CollatzResearch.WordTrace tailWord_1649410 prefixEnd_1649410 564626750888331272993005 := by
  unfold tailWord_1649410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15039731238619185411520421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40105949969651161097387789 15039731238619185411520421)
  ·
    refine ⟨2819949607241097264660079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15039731238619185411520421 2819949607241097264660079)
    ·
      refine ⟨4229924410861645896990119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819949607241097264660079 4229924410861645896990119)
      ·
        refine ⟨6344886616292468845485179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229924410861645896990119 6344886616292468845485179)
        ·
          refine ⟨9517329924438703268227769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344886616292468845485179 9517329924438703268227769)
          ·
            refine ⟨7137997443329027451170827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517329924438703268227769 7137997443329027451170827)
            ·
              refine ⟨10706996164993541176756241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137997443329027451170827 10706996164993541176756241)
              ·
                refine ⟨8030247123745155882567181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10706996164993541176756241 8030247123745155882567181)
                ·
                  refine ⟨3011342671404433455962693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8030247123745155882567181 3011342671404433455962693)
                  ·
                    refine ⟨564626750888331272993005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011342671404433455962693 564626750888331272993005)
                    ·
                      rfl

theorem cell22_1649410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1649410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649410 prefixEnd_1649410 := by exact prefixLift 1649410
  have htrace : WordTrace (prefixWord ++ tailWord_1649410) baseStart_1649410 baseEnd_1649410 := by
    simpa [prefixWord, tailWord_1649410, baseEnd_1649410] using wordTrace_append hprefix tailTrace_1649410
  have hstable : (prefixWord ++ tailWord_1649410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649410).length < 2 ^ (prefixWord ++ tailWord_1649410).sum := by decide
  have hdescent : baseEnd_1649410 < baseStart_1649410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649423 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 1, 5]
def baseStart_1649423 : Nat := 118140960795 + 1649423 * 2 ^ 59
def prefixEnd_1649423 : Nat := 4983230072969 + 3 ^ 40 * 1649423 * 2
def baseEnd_1649423 : Nat := 564631201054003572417965

theorem tailTrace_1649423 : CollatzResearch.WordTrace tailWord_1649423 prefixEnd_1649423 564631201054003572417965 := by
  unfold tailWord_1649423
  simp only [CollatzResearch.WordTrace]
  refine ⟨60159399103429644866304923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40106266068953096577536615 60159399103429644866304923)
  ·
    refine ⟨90239098655144467299457385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60159399103429644866304923 90239098655144467299457385)
    ·
      refine ⟨67679323991358350474593039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90239098655144467299457385 67679323991358350474593039)
      ·
        refine ⟨101518985987037525711889559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67679323991358350474593039 101518985987037525711889559)
        ·
          refine ⟨152278478980556288567834339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101518985987037525711889559 152278478980556288567834339)
          ·
            refine ⟨228417718470834432851751509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152278478980556288567834339 228417718470834432851751509)
            ·
              refine ⟨2676770138330091009981463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 228417718470834432851751509 2676770138330091009981463)
              ·
                refine ⟨4015155207495136514972195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676770138330091009981463 4015155207495136514972195)
                ·
                  refine ⟨6022732811242704772458293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015155207495136514972195 6022732811242704772458293)
                  ·
                    refine ⟨564631201054003572417965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6022732811242704772458293 564631201054003572417965)
                    ·
                      rfl

theorem cell22_1649423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_1649423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649423 prefixEnd_1649423 := by exact prefixLift 1649423
  have htrace : WordTrace (prefixWord ++ tailWord_1649423) baseStart_1649423 baseEnd_1649423 := by
    simpa [prefixWord, tailWord_1649423, baseEnd_1649423] using wordTrace_append hprefix tailTrace_1649423
  have hstable : (prefixWord ++ tailWord_1649423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649423).length < 2 ^ (prefixWord ++ tailWord_1649423).sum := by decide
  have hdescent : baseEnd_1649423 < baseStart_1649423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649442 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1649442 : Nat := 118140960795 + 1649442 * 2 ^ 59
def prefixEnd_1649442 : Nat := 4983230072969 + 3 ^ 40 * 1649442 * 2
def baseEnd_1649442 : Nat := 188212568380764618730969

theorem tailTrace_1649442 : CollatzResearch.WordTrace tailWord_1649442 prefixEnd_1649442 188212568380764618730969 := by
  unfold tailWord_1649442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040023022590202777811645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40106728060240540740831053 15040023022590202777811645)
  ·
    refine ⟨5640008633471326041679367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15040023022590202777811645 5640008633471326041679367)
    ·
      refine ⟨8460012950206989062519051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640008633471326041679367 8460012950206989062519051)
      ·
        refine ⟨12690019425310483593778577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460012950206989062519051 12690019425310483593778577)
        ·
          refine ⟨9517514568982862695333933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690019425310483593778577 9517514568982862695333933)
          ·
            refine ⟨3569067963368573510750225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9517514568982862695333933 3569067963368573510750225)
            ·
              refine ⟨2676800972526430133062669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569067963368573510750225 2676800972526430133062669)
              ·
                refine ⟨1003800364697411299898501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2676800972526430133062669 1003800364697411299898501)
                ·
                  refine ⟨188212568380764618730969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003800364697411299898501 188212568380764618730969)
                  ·
                    rfl

theorem cell22_1649442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1649442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649442 prefixEnd_1649442 := by exact prefixLift 1649442
  have htrace : WordTrace (prefixWord ++ tailWord_1649442) baseStart_1649442 baseEnd_1649442 := by
    simpa [prefixWord, tailWord_1649442, baseEnd_1649442] using wordTrace_append hprefix tailTrace_1649442
  have hstable : (prefixWord ++ tailWord_1649442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649442).length < 2 ^ (prefixWord ++ tailWord_1649442).sum := by decide
  have hdescent : baseEnd_1649442 < baseStart_1649442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649444 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1649444 : Nat := 118140960795 + 1649444 * 2 ^ 59
def prefixEnd_1649444 : Nat := 4983230072969 + 3 ^ 40 * 1649444 * 2
def baseEnd_1649444 : Nat := 564638389783166517642901

theorem tailTrace_1649444 : CollatzResearch.WordTrace tailWord_1649444 prefixEnd_1649444 564638389783166517642901 := by
  unfold tailWord_1649444
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080082518176782726409693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40106776690902376968546257 30080082518176782726409693)
  ·
    refine ⟨11280030944316293522403635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30080082518176782726409693 11280030944316293522403635)
    ·
      refine ⟨16920046416474440283605453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280030944316293522403635 16920046416474440283605453)
      ·
        refine ⟨6345017406177915106352045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16920046416474440283605453 6345017406177915106352045)
        ·
          refine ⟨2379381527316718164882017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6345017406177915106352045 2379381527316718164882017)
          ·
            refine ⟨1784536145487538623661513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379381527316718164882017 1784536145487538623661513)
            ·
              refine ⟨1338402109115653967746135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784536145487538623661513 1338402109115653967746135)
              ·
                refine ⟨2007603163673480951619203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338402109115653967746135 2007603163673480951619203)
                ·
                  refine ⟨3011404745510221427428805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007603163673480951619203 3011404745510221427428805)
                  ·
                    refine ⟨564638389783166517642901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011404745510221427428805 564638389783166517642901)
                    ·
                      rfl

theorem cell22_1649444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1649444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649444 prefixEnd_1649444 := by exact prefixLift 1649444
  have htrace : WordTrace (prefixWord ++ tailWord_1649444) baseStart_1649444 baseEnd_1649444 := by
    simpa [prefixWord, tailWord_1649444, baseEnd_1649444] using wordTrace_append hprefix tailTrace_1649444
  have hstable : (prefixWord ++ tailWord_1649444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649444).length < 2 ^ (prefixWord ++ tailWord_1649444).sum := by decide
  have hdescent : baseEnd_1649444 < baseStart_1649444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649498 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_1649498 : Nat := 118140960795 + 1649498 * 2 ^ 59
def prefixEnd_1649498 : Nat := 4983230072969 + 3 ^ 40 * 1649498 * 2
def baseEnd_1649498 : Nat := 188218958362242792264245

theorem tailTrace_1649498 : CollatzResearch.WordTrace tailWord_1649498 prefixEnd_1649498 188218958362242792264245 := by
  unfold tailWord_1649498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040533644539483168821287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40108089718771955116856765 15040533644539483168821287)
  ·
    refine ⟨22560800466809224753231931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15040533644539483168821287 22560800466809224753231931)
    ·
      refine ⟨33841200700213837129847897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22560800466809224753231931 33841200700213837129847897)
      ·
        refine ⟨25380900525160377847385923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33841200700213837129847897 25380900525160377847385923)
        ·
          refine ⟨38071350787740566771078885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25380900525160377847385923 38071350787740566771078885)
          ·
            refine ⟨7138378272701356269577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38071350787740566771078885 7138378272701356269577291)
            ·
              refine ⟨10707567409052034404365937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138378272701356269577291 10707567409052034404365937)
              ·
                refine ⟨8030675556789025803274453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10707567409052034404365937 8030675556789025803274453)
                ·
                  refine ⟨188218958362242792264245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8030675556789025803274453 188218958362242792264245)
                  ·
                    rfl

theorem cell22_1649498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_1649498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649498 prefixEnd_1649498 := by exact prefixLift 1649498
  have htrace : WordTrace (prefixWord ++ tailWord_1649498) baseStart_1649498 baseEnd_1649498 := by
    simpa [prefixWord, tailWord_1649498, baseEnd_1649498] using wordTrace_append hprefix tailTrace_1649498
  have hstable : (prefixWord ++ tailWord_1649498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649498).length < 2 ^ (prefixWord ++ tailWord_1649498).sum := by decide
  have hdescent : baseEnd_1649498 < baseStart_1649498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649545 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_1649545 : Nat := 118140960795 + 1649545 * 2 ^ 59
def prefixEnd_1649545 : Nat := 4983230072969 + 3 ^ 40 * 1649545 * 2
def baseEnd_1649545 : Nat := 564672964147235920867591

theorem tailTrace_1649545 : CollatzResearch.WordTrace tailWord_1649545 prefixEnd_1649545 564672964147235920867591 := by
  unfold tailWord_1649545
  simp only [CollatzResearch.WordTrace]
  refine ⟨60163848808987659702246089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40109232539325106468164059 60163848808987659702246089)
  ·
    refine ⟨45122886606740744776684567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60163848808987659702246089 45122886606740744776684567)
    ·
      refine ⟨67684329910111117165026851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45122886606740744776684567 67684329910111117165026851)
      ·
        refine ⟨101526494865166675747540277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67684329910111117165026851 101526494865166675747540277)
        ·
          refine ⟨9518108893609375851331901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101526494865166675747540277 9518108893609375851331901)
          ·
            refine ⟨3569290835103515944249463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9518108893609375851331901 3569290835103515944249463)
            ·
              refine ⟨5353936252655273916374195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569290835103515944249463 5353936252655273916374195)
              ·
                refine ⟨8030904378982910874561293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353936252655273916374195 8030904378982910874561293)
                ·
                  refine ⟨3011589142118591577960485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8030904378982910874561293 3011589142118591577960485)
                  ·
                    refine ⟨564672964147235920867591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011589142118591577960485 564672964147235920867591)
                    ·
                      rfl

theorem cell22_1649545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_1649545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649545 prefixEnd_1649545 := by exact prefixLift 1649545
  have htrace : WordTrace (prefixWord ++ tailWord_1649545) baseStart_1649545 baseEnd_1649545 := by
    simpa [prefixWord, tailWord_1649545, baseEnd_1649545] using wordTrace_append hprefix tailTrace_1649545
  have hstable : (prefixWord ++ tailWord_1649545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649545).length < 2 ^ (prefixWord ++ tailWord_1649545).sum := by decide
  have hdescent : baseEnd_1649545 < baseStart_1649545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649573 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_1649573 : Nat := 118140960795 + 1649573 * 2 ^ 59
def prefixEnd_1649573 : Nat := 4983230072969 + 3 ^ 40 * 1649573 * 2
def baseEnd_1649573 : Nat := 564682549119453181167505

theorem tailTrace_1649573 : CollatzResearch.WordTrace tailWord_1649573 prefixEnd_1649573 564682549119453181167505 := by
  unfold tailWord_1649573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60164870052886220484265373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40109913368590813656176915 60164870052886220484265373)
  ·
    refine ⟨22561826269832332681599515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60164870052886220484265373 22561826269832332681599515)
    ·
      refine ⟨33842739404748499022399273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22561826269832332681599515 33842739404748499022399273)
      ·
        refine ⟨25382054553561374266799455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33842739404748499022399273 25382054553561374266799455)
        ·
          refine ⟨38073081830342061400199183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25382054553561374266799455 38073081830342061400199183)
          ·
            refine ⟨57109622745513092100298775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38073081830342061400199183 57109622745513092100298775)
            ·
              refine ⟨85664434118269638150448163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57109622745513092100298775 85664434118269638150448163)
              ·
                refine ⟨128496651177404457225672245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85664434118269638150448163 128496651177404457225672245)
                ·
                  refine ⟨12046561047881667864906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128496651177404457225672245 12046561047881667864906773)
                  ·
                    refine ⟨564682549119453181167505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12046561047881667864906773 564682549119453181167505)
                    ·
                      rfl

theorem cell22_1649573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_1649573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649573 prefixEnd_1649573 := by exact prefixLift 1649573
  have htrace : WordTrace (prefixWord ++ tailWord_1649573) baseStart_1649573 baseEnd_1649573 := by
    simpa [prefixWord, tailWord_1649573, baseEnd_1649573] using wordTrace_append hprefix tailTrace_1649573
  have hstable : (prefixWord ++ tailWord_1649573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649573).length < 2 ^ (prefixWord ++ tailWord_1649573).sum := by decide
  have hdescent : baseEnd_1649573 < baseStart_1649573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649592 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_1649592 : Nat := 118140960795 + 1649592 * 2 ^ 59
def prefixEnd_1649592 : Nat := 4983230072969 + 3 ^ 40 * 1649592 * 2
def baseEnd_1649592 : Nat := 564689053207743464942447

theorem tailTrace_1649592 : CollatzResearch.WordTrace tailWord_1649592 prefixEnd_1649592 564689053207743464942447 := by
  unfold tailWord_1649592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30082781519908693364603515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40110375359878257819471353 30082781519908693364603515)
  ·
    refine ⟨45124172279863040046905273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30082781519908693364603515 45124172279863040046905273)
    ·
      refine ⟨33843129209897280035178955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45124172279863040046905273 33843129209897280035178955)
      ·
        refine ⟨50764693814845920052768433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33843129209897280035178955 50764693814845920052768433)
        ·
          refine ⟨38073520361134440039576325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50764693814845920052768433 38073520361134440039576325)
          ·
            refine ⟨7138785067712707507420561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38073520361134440039576325 7138785067712707507420561)
            ·
              refine ⟨5354088800784530630565421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7138785067712707507420561 5354088800784530630565421)
              ·
                refine ⟨2007783300294198986462033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354088800784530630565421 2007783300294198986462033)
                ·
                  refine ⟨1505837475220649239846525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2007783300294198986462033 1505837475220649239846525)
                  ·
                    refine ⟨564689053207743464942447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505837475220649239846525 564689053207743464942447)
                    ·
                      rfl

theorem cell22_1649592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_1649592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649592 prefixEnd_1649592 := by exact prefixLift 1649592
  have htrace : WordTrace (prefixWord ++ tailWord_1649592) baseStart_1649592 baseEnd_1649592 := by
    simpa [prefixWord, tailWord_1649592, baseEnd_1649592] using wordTrace_append hprefix tailTrace_1649592
  have hstable : (prefixWord ++ tailWord_1649592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649592).length < 2 ^ (prefixWord ++ tailWord_1649592).sum := by decide
  have hdescent : baseEnd_1649592 < baseStart_1649592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_1649603 : Nat := 118140960795 + 1649603 * 2 ^ 59
def prefixEnd_1649603 : Nat := 4983230072969 + 3 ^ 40 * 1649603 * 2
def baseEnd_1649603 : Nat := 564692818732543102917413

theorem tailTrace_1649603 : CollatzResearch.WordTrace tailWord_1649603 prefixEnd_1649603 564692818732543102917413 := by
  unfold tailWord_1649603
  simp only [CollatzResearch.WordTrace]
  refine ⟨60165964242777535607857463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40110642828518357071904975 60165964242777535607857463)
  ·
    refine ⟨90248946364166303411786195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60165964242777535607857463 90248946364166303411786195)
    ·
      refine ⟨135373419546249455117679293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90248946364166303411786195 135373419546249455117679293)
      ·
        refine ⟨50765032329843545669129735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135373419546249455117679293 50765032329843545669129735)
        ·
          refine ⟨76147548494765318503694603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50765032329843545669129735 76147548494765318503694603)
          ·
            refine ⟨114221322742147977755541905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76147548494765318503694603 114221322742147977755541905)
            ·
              refine ⟨85665992056610983316656429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114221322742147977755541905 85665992056610983316656429)
              ·
                refine ⟨32124747021229118743746161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85665992056610983316656429 32124747021229118743746161)
                ·
                  refine ⟨24093560265921839057809621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32124747021229118743746161 24093560265921839057809621)
                  ·
                    refine ⟨564692818732543102917413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24093560265921839057809621 564692818732543102917413)
                    ·
                      rfl

theorem cell22_1649603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_1649603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649603 prefixEnd_1649603 := by exact prefixLift 1649603
  have htrace : WordTrace (prefixWord ++ tailWord_1649603) baseStart_1649603 baseEnd_1649603 := by
    simpa [prefixWord, tailWord_1649603, baseEnd_1649603] using wordTrace_append hprefix tailTrace_1649603
  have hstable : (prefixWord ++ tailWord_1649603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649603).length < 2 ^ (prefixWord ++ tailWord_1649603).sum := by decide
  have hdescent : baseEnd_1649603 < baseStart_1649603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649613 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1649613 : Nat := 118140960795 + 1649613 * 2 ^ 59
def prefixEnd_1649613 : Nat := 4983230072969 + 3 ^ 40 * 1649613 * 2
def baseEnd_1649613 : Nat := 564696241936906410167383

theorem tailTrace_1649613 : CollatzResearch.WordTrace tailWord_1649613 prefixEnd_1649613 564696241936906410167383 := by
  unfold tailWord_1649613
  simp only [CollatzResearch.WordTrace]
  refine ⟨60166328972741307315721493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40110885981827538210480995 60166328972741307315721493)
  ·
    refine ⟨2820296670597248780424445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60166328972741307315721493 2820296670597248780424445)
    ·
      refine ⟨1057611251473968292659167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2820296670597248780424445 1057611251473968292659167)
      ·
        refine ⟨1586416877210952438988751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057611251473968292659167 1586416877210952438988751)
        ·
          refine ⟨2379625315816428658483127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586416877210952438988751 2379625315816428658483127)
          ·
            refine ⟨3569437973724642987724691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379625315816428658483127 3569437973724642987724691)
            ·
              refine ⟨5354156960586964481587037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569437973724642987724691 5354156960586964481587037)
              ·
                refine ⟨2007808860220111680595139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354156960586964481587037 2007808860220111680595139)
                ·
                  refine ⟨3011713290330167520892709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007808860220111680595139 3011713290330167520892709)
                  ·
                    refine ⟨564696241936906410167383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011713290330167520892709 564696241936906410167383)
                    ·
                      rfl

theorem cell22_1649613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1649613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649613 prefixEnd_1649613 := by exact prefixLift 1649613
  have htrace : WordTrace (prefixWord ++ tailWord_1649613) baseStart_1649613 baseEnd_1649613 := by
    simpa [prefixWord, tailWord_1649613, baseEnd_1649613] using wordTrace_append hprefix tailTrace_1649613
  have hstable : (prefixWord ++ tailWord_1649613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649613).length < 2 ^ (prefixWord ++ tailWord_1649613).sum := by decide
  have hdescent : baseEnd_1649613 < baseStart_1649613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649622 : List Nat := [5, 2, 1, 1, 2, 2, 9]
def baseStart_1649622 : Nat := 118140960795 + 1649622 * 2 ^ 59
def prefixEnd_1649622 : Nat := 4983230072969 + 3 ^ 40 * 1649622 * 2
def baseEnd_1649622 : Nat := 20914789734104940247865

theorem tailTrace_1649622 : CollatzResearch.WordTrace tailWord_1649622 prefixEnd_1649622 20914789734104940247865 := by
  unfold tailWord_1649622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760416076856793865799945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40111104819805801235199413 3760416076856793865799945)
  ·
    refine ⟨2820312057642595399349959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3760416076856793865799945 2820312057642595399349959)
    ·
      refine ⟨4230468086463893099024939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820312057642595399349959 4230468086463893099024939)
      ·
        refine ⟨6345702129695839648537409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230468086463893099024939 6345702129695839648537409)
        ·
          refine ⟨4759276597271879736403057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345702129695839648537409 4759276597271879736403057)
          ·
            refine ⟨3569457447953909802302293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759276597271879736403057 3569457447953909802302293)
            ·
              refine ⟨20914789734104940247865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3569457447953909802302293 20914789734104940247865)
              ·
                rfl

theorem cell22_1649622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 9].length) (baseStart_1649622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649622 prefixEnd_1649622 := by exact prefixLift 1649622
  have htrace : WordTrace (prefixWord ++ tailWord_1649622) baseStart_1649622 baseEnd_1649622 := by
    simpa [prefixWord, tailWord_1649622, baseEnd_1649622] using wordTrace_append hprefix tailTrace_1649622
  have hstable : (prefixWord ++ tailWord_1649622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649622).length < 2 ^ (prefixWord ++ tailWord_1649622).sum := by decide
  have hdescent : baseEnd_1649622 < baseStart_1649622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649654 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1649654 : Nat := 118140960795 + 1649654 * 2 ^ 59
def prefixEnd_1649654 : Nat := 4983230072969 + 3 ^ 40 * 1649654 * 2
def baseEnd_1649654 : Nat := 564710277074795969892257

theorem tailTrace_1649654 : CollatzResearch.WordTrace tailWord_1649654 prefixEnd_1649654 564710277074795969892257 := by
  unfold tailWord_1649654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760489022849548207372751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40111882910395180878642677 3760489022849548207372751)
  ·
    refine ⟨5640733534274322311059127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760489022849548207372751 5640733534274322311059127)
    ·
      refine ⟨8461100301411483466588691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640733534274322311059127 8461100301411483466588691)
      ·
        refine ⟨12691650452117225199883037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8461100301411483466588691 12691650452117225199883037)
        ·
          refine ⟨4759368919543959449956139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12691650452117225199883037 4759368919543959449956139)
          ·
            refine ⟨7139053379315939174934209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759368919543959449956139 7139053379315939174934209)
            ·
              refine ⟨5354290034486954381200657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139053379315939174934209 5354290034486954381200657)
              ·
                refine ⟨4015717525865215785900493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354290034486954381200657 4015717525865215785900493)
                ·
                  refine ⟨1505894072199455919712685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4015717525865215785900493 1505894072199455919712685)
                  ·
                    refine ⟨564710277074795969892257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505894072199455919712685 564710277074795969892257)
                    ·
                      rfl

theorem cell22_1649654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1649654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649654 prefixEnd_1649654 := by exact prefixLift 1649654
  have htrace : WordTrace (prefixWord ++ tailWord_1649654) baseStart_1649654 baseEnd_1649654 := by
    simpa [prefixWord, tailWord_1649654, baseEnd_1649654] using wordTrace_append hprefix tailTrace_1649654
  have hstable : (prefixWord ++ tailWord_1649654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649654).length < 2 ^ (prefixWord ++ tailWord_1649654).sum := by decide
  have hdescent : baseEnd_1649654 < baseStart_1649654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649742 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1649742 : Nat := 118140960795 + 1649742 * 2 ^ 59
def prefixEnd_1649742 : Nat := 4983230072969 + 3 ^ 40 * 1649742 * 2
def baseEnd_1649742 : Nat := 564740401273193073691987

theorem tailTrace_1649742 : CollatzResearch.WordTrace tailWord_1649742 prefixEnd_1649742 564740401273193073691987 := by
  unfold tailWord_1649742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521379248659245293395935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40114022659515974898111653 7521379248659245293395935)
  ·
    refine ⟨11282068872988867940093903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521379248659245293395935 11282068872988867940093903)
    ·
      refine ⟨16923103309483301910140855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11282068872988867940093903 16923103309483301910140855)
      ·
        refine ⟨25384654964224952865211283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16923103309483301910140855 25384654964224952865211283)
        ·
          refine ⟨38076982446337429297816925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25384654964224952865211283 38076982446337429297816925)
          ·
            refine ⟨14278868417376535986681347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38076982446337429297816925 14278868417376535986681347)
            ·
              refine ⟨21418302626064803980022021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14278868417376535986681347 21418302626064803980022021)
              ·
                refine ⟨4015931742387150746254129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21418302626064803980022021 4015931742387150746254129)
                ·
                  refine ⟨3011948806790363059690597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015931742387150746254129 3011948806790363059690597)
                  ·
                    refine ⟨564740401273193073691987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011948806790363059690597 564740401273193073691987)
                    ·
                      rfl

theorem cell22_1649742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1649742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649742 prefixEnd_1649742 := by exact prefixLift 1649742
  have htrace : WordTrace (prefixWord ++ tailWord_1649742) baseStart_1649742 baseEnd_1649742 := by
    simpa [prefixWord, tailWord_1649742, baseEnd_1649742] using wordTrace_append hprefix tailTrace_1649742
  have hstable : (prefixWord ++ tailWord_1649742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649742).length < 2 ^ (prefixWord ++ tailWord_1649742).sum := by decide
  have hdescent : baseEnd_1649742 < baseStart_1649742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649746 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1649746 : Nat := 118140960795 + 1649746 * 2 ^ 59
def prefixEnd_1649746 : Nat := 4983230072969 + 3 ^ 40 * 1649746 * 2
def baseEnd_1649746 : Nat := 188247256851646132197325

theorem tailTrace_1649746 : CollatzResearch.WordTrace tailWord_1649746 prefixEnd_1649746 188247256851646132197325 := by
  unfold tailWord_1649746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15042794970314867757578273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40114119920839647353542061 15042794970314867757578273)
  ·
    refine ⟨11282096227736150818183705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15042794970314867757578273 11282096227736150818183705)
    ·
      refine ⟨8461572170802113113637779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11282096227736150818183705 8461572170802113113637779)
      ·
        refine ⟨12692358256203169670456669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8461572170802113113637779 12692358256203169670456669)
        ·
          refine ⟨4759634346076188626421251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12692358256203169670456669 4759634346076188626421251)
          ·
            refine ⟨7139451519114282939631877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759634346076188626421251 7139451519114282939631877)
            ·
              refine ⟨1338647159833928051180977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7139451519114282939631877 1338647159833928051180977)
              ·
                refine ⟨1003985369875446038385733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338647159833928051180977 1003985369875446038385733)
                ·
                  refine ⟨188247256851646132197325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003985369875446038385733 188247256851646132197325)
                  ·
                    rfl

theorem cell22_1649746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1649746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649746 prefixEnd_1649746 := by exact prefixLift 1649746
  have htrace : WordTrace (prefixWord ++ tailWord_1649746) baseStart_1649746 baseEnd_1649746 := by
    simpa [prefixWord, tailWord_1649746, baseEnd_1649746] using wordTrace_append hprefix tailTrace_1649746
  have hstable : (prefixWord ++ tailWord_1649746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649746).length < 2 ^ (prefixWord ++ tailWord_1649746).sum := by decide
  have hdescent : baseEnd_1649746 < baseStart_1649746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649774 : List Nat := [4, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1649774 : Nat := 118140960795 + 1649774 * 2 ^ 59
def prefixEnd_1649774 : Nat := 4983230072969 + 3 ^ 40 * 1649774 * 2
def baseEnd_1649774 : Nat := 62750150614128406321321

theorem tailTrace_1649774 : CollatzResearch.WordTrace tailWord_1649774 prefixEnd_1649774 62750150614128406321321 := by
  unfold tailWord_1649774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521525140644753976541547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40114800750105354541554917 7521525140644753976541547)
  ·
    refine ⟨11282287710967130964812321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521525140644753976541547 11282287710967130964812321)
    ·
      refine ⟨8461715783225348223609241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11282287710967130964812321 8461715783225348223609241)
      ·
        refine ⟨6346286837419011167706931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8461715783225348223609241 6346286837419011167706931)
        ·
          refine ⟨9519430256128516751560397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346286837419011167706931 9519430256128516751560397)
          ·
            refine ⟨3569786346048193781835149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9519430256128516751560397 3569786346048193781835149)
            ·
              refine ⟨1338669879768072668188181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3569786346048193781835149 1338669879768072668188181)
              ·
                refine ⟨62750150614128406321321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1338669879768072668188181 62750150614128406321321)
                ·
                  rfl

theorem cell22_1649774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1649774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649774 prefixEnd_1649774 := by exact prefixLift 1649774
  have htrace : WordTrace (prefixWord ++ tailWord_1649774) baseStart_1649774 baseEnd_1649774 := by
    simpa [prefixWord, tailWord_1649774, baseEnd_1649774] using wordTrace_append hprefix tailTrace_1649774
  have hstable : (prefixWord ++ tailWord_1649774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649774).length < 2 ^ (prefixWord ++ tailWord_1649774).sum := by decide
  have hdescent : baseEnd_1649774 < baseStart_1649774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649802 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_1649802 : Nat := 118140960795 + 1649802 * 2 ^ 59
def prefixEnd_1649802 : Nat := 4983230072969 + 3 ^ 40 * 1649802 * 2
def baseEnd_1649802 : Nat := 188253646833124305730601

theorem tailTrace_1649802 : CollatzResearch.WordTrace tailWord_1649802 prefixEnd_1649802 188253646833124305730601 := by
  unfold tailWord_1649802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15043305592264148148587915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40115481579371061729567773 15043305592264148148587915)
  ·
    refine ⟨22564958388396222222881873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15043305592264148148587915 22564958388396222222881873)
    ·
      refine ⟨16923718791297166667161405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22564958388396222222881873 16923718791297166667161405)
      ·
        refine ⟨6346394546736437500185527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16923718791297166667161405 6346394546736437500185527)
        ·
          refine ⟨9519591820104656250278291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346394546736437500185527 9519591820104656250278291)
          ·
            refine ⟨14279387730156984375417437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9519591820104656250278291 14279387730156984375417437)
            ·
              refine ⟨5354770398808869140781539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14279387730156984375417437 5354770398808869140781539)
              ·
                refine ⟨8032155598213303711172309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354770398808869140781539 8032155598213303711172309)
                ·
                  refine ⟨188253646833124305730601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8032155598213303711172309 188253646833124305730601)
                  ·
                    rfl

theorem cell22_1649802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_1649802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649802 prefixEnd_1649802 := by exact prefixLift 1649802
  have htrace : WordTrace (prefixWord ++ tailWord_1649802) baseStart_1649802 baseEnd_1649802 := by
    simpa [prefixWord, tailWord_1649802, baseEnd_1649802] using wordTrace_append hprefix tailTrace_1649802
  have hstable : (prefixWord ++ tailWord_1649802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649802).length < 2 ^ (prefixWord ++ tailWord_1649802).sum := by decide
  have hdescent : baseEnd_1649802 < baseStart_1649802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649806 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1649806 : Nat := 118140960795 + 1649806 * 2 ^ 59
def prefixEnd_1649806 : Nat := 4983230072969 + 3 ^ 40 * 1649806 * 2
def baseEnd_1649806 : Nat := 564762309781118240091791

theorem tailTrace_1649806 : CollatzResearch.WordTrace tailWord_1649806 prefixEnd_1649806 564762309781118240091791 := by
  unfold tailWord_1649806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521671032630262659687159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40115578840694734184998181 7521671032630262659687159)
  ·
    refine ⟨11282506548945393989530739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521671032630262659687159 11282506548945393989530739)
    ·
      refine ⟨16923759823418090984296109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11282506548945393989530739 16923759823418090984296109)
      ·
        refine ⟨6346409933781784119111041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16923759823418090984296109 6346409933781784119111041)
        ·
          refine ⟨4759807450336338089333281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6346409933781784119111041 4759807450336338089333281)
          ·
            refine ⟨3569855587752253566999961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759807450336338089333281 3569855587752253566999961)
            ·
              refine ⟨2677391690814190175249971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569855587752253566999961 2677391690814190175249971)
              ·
                refine ⟨4016087536221285262874957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677391690814190175249971 4016087536221285262874957)
                ·
                  refine ⟨1506032826082981973578109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4016087536221285262874957 1506032826082981973578109)
                  ·
                    refine ⟨564762309781118240091791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506032826082981973578109 564762309781118240091791)
                    ·
                      rfl

theorem cell22_1649806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1649806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649806 prefixEnd_1649806 := by exact prefixLift 1649806
  have htrace : WordTrace (prefixWord ++ tailWord_1649806) baseStart_1649806 baseEnd_1649806 := by
    simpa [prefixWord, tailWord_1649806, baseEnd_1649806] using wordTrace_append hprefix tailTrace_1649806
  have hstable : (prefixWord ++ tailWord_1649806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649806).length < 2 ^ (prefixWord ++ tailWord_1649806).sum := by decide
  have hdescent : baseEnd_1649806 < baseStart_1649806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649849 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_1649849 : Nat := 118140960795 + 1649849 * 2 ^ 59
def prefixEnd_1649849 : Nat := 4983230072969 + 3 ^ 40 * 1649849 * 2
def baseEnd_1649849 : Nat := 564777029559880461266659

theorem tailTrace_1649849 : CollatzResearch.WordTrace tailWord_1649849 prefixEnd_1649849 564777029559880461266659 := by
  unfold tailWord_1649849
  simp only [CollatzResearch.WordTrace]
  refine ⟨60174936599886319621312601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40116624399924213080875067 60174936599886319621312601)
  ·
    refine ⟨45131202449914739715984451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60174936599886319621312601 45131202449914739715984451)
    ·
      refine ⟨67696803674872109573976677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45131202449914739715984451 67696803674872109573976677)
      ·
        refine ⟨12693150689038520545120627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67696803674872109573976677 12693150689038520545120627)
        ·
          refine ⟨19039726033557780817680941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693150689038520545120627 19039726033557780817680941)
          ·
            refine ⟨7139897262584167806630353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19039726033557780817680941 7139897262584167806630353)
            ·
              refine ⟨5354922946938125854972765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139897262584167806630353 5354922946938125854972765)
              ·
                refine ⟨2008096105101797195614787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354922946938125854972765 2008096105101797195614787)
                ·
                  refine ⟨3012144157652695793422181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008096105101797195614787 3012144157652695793422181)
                  ·
                    refine ⟨564777029559880461266659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012144157652695793422181 564777029559880461266659)
                    ·
                      rfl

theorem cell22_1649849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_1649849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649849 prefixEnd_1649849 := by exact prefixLift 1649849
  have htrace : WordTrace (prefixWord ++ tailWord_1649849) baseStart_1649849 baseEnd_1649849 := by
    simpa [prefixWord, tailWord_1649849, baseEnd_1649849] using wordTrace_append hprefix tailTrace_1649849
  have hstable : (prefixWord ++ tailWord_1649849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649849).length < 2 ^ (prefixWord ++ tailWord_1649849).sum := by decide
  have hdescent : baseEnd_1649849 < baseStart_1649849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649864 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_1649864 : Nat := 118140960795 + 1649864 * 2 ^ 59
def prefixEnd_1649864 : Nat := 4983230072969 + 3 ^ 40 * 1649864 * 2
def baseEnd_1649864 : Nat := 188260721455475140713871

theorem tailTrace_1649864 : CollatzResearch.WordTrace tailWord_1649864 prefixEnd_1649864 188260721455475140713871 := by
  unfold tailWord_1649864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30087741847415988591554323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40116989129887984788739097 30087741847415988591554323)
  ·
    refine ⟨45131612771123982887331485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30087741847415988591554323 45131612771123982887331485)
    ·
      refine ⟨16924354789171493582749307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45131612771123982887331485 16924354789171493582749307)
      ·
        refine ⟨25386532183757240374123961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16924354789171493582749307 25386532183757240374123961)
        ·
          refine ⟨19039899137817930280592971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25386532183757240374123961 19039899137817930280592971)
          ·
            refine ⟨28559848706726895420889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19039899137817930280592971 28559848706726895420889457)
            ·
              refine ⟨21419886530045171565667093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28559848706726895420889457 21419886530045171565667093)
              ·
                refine ⟨1004057181095867417140645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21419886530045171565667093 1004057181095867417140645)
                ·
                  refine ⟨188260721455475140713871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004057181095867417140645 188260721455475140713871)
                  ·
                    rfl

theorem cell22_1649864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_1649864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649864 prefixEnd_1649864 := by exact prefixLift 1649864
  have htrace : WordTrace (prefixWord ++ tailWord_1649864) baseStart_1649864 baseEnd_1649864 := by
    simpa [prefixWord, tailWord_1649864, baseEnd_1649864] using wordTrace_append hprefix tailTrace_1649864
  have hstable : (prefixWord ++ tailWord_1649864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649864).length < 2 ^ (prefixWord ++ tailWord_1649864).sum := by decide
  have hdescent : baseEnd_1649864 < baseStart_1649864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649892 : List Nat := [2, 3, 1, 1, 1, 2, 4, 8]
def baseStart_1649892 : Nat := 118140960795 + 1649892 * 2 ^ 59
def prefixEnd_1649892 : Nat := 4983230072969 + 3 ^ 40 * 1649892 * 2
def baseEnd_1649892 : Nat := 62754638815404742493503

theorem tailTrace_1649892 : CollatzResearch.WordTrace tailWord_1649892 prefixEnd_1649892 62754638815404742493503 := by
  unfold tailWord_1649892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30088252469365268982563965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40117669959153691976751953 30088252469365268982563965)
  ·
    refine ⟨11283094676011975868461487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30088252469365268982563965 11283094676011975868461487)
    ·
      refine ⟨16924642014017963802692231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11283094676011975868461487 16924642014017963802692231)
      ·
        refine ⟨25386963021026945704038347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16924642014017963802692231 25386963021026945704038347)
        ·
          refine ⟨38080444531540418556057521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25386963021026945704038347 38080444531540418556057521)
          ·
            refine ⟨28560333398655313917043141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38080444531540418556057521 28560333398655313917043141)
            ·
              refine ⟨5355062512247871359445589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28560333398655313917043141 5355062512247871359445589)
              ·
                refine ⟨62754638815404742493503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5355062512247871359445589 62754638815404742493503)
                ·
                  rfl

theorem cell22_1649892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_1649892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649892 prefixEnd_1649892 := by exact prefixLift 1649892
  have htrace : WordTrace (prefixWord ++ tailWord_1649892) baseStart_1649892 baseEnd_1649892 := by
    simpa [prefixWord, tailWord_1649892, baseEnd_1649892] using wordTrace_append hprefix tailTrace_1649892
  have hstable : (prefixWord ++ tailWord_1649892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649892).length < 2 ^ (prefixWord ++ tailWord_1649892).sum := by decide
  have hdescent : baseEnd_1649892 < baseStart_1649892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649969 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1649969 : Nat := 118140960795 + 1649969 * 2 ^ 59
def prefixEnd_1649969 : Nat := 4983230072969 + 3 ^ 40 * 1649969 * 2
def baseEnd_1649969 : Nat := 564818108012240148266291

theorem tailTrace_1649969 : CollatzResearch.WordTrace tailWord_1649969 prefixEnd_1649969 564818108012240148266291 := by
  unfold tailWord_1649969
  simp only [CollatzResearch.WordTrace]
  refine ⟨60179313359451580115680961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40119542239634386743787307 60179313359451580115680961)
  ·
    refine ⟨45134485019588685086760721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60179313359451580115680961 45134485019588685086760721)
    ·
      refine ⟨33850863764691513815070541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45134485019588685086760721 33850863764691513815070541)
      ·
        refine ⟨12694073911759317680651453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33850863764691513815070541 12694073911759317680651453)
        ·
          refine ⟨4760277716909744130244295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12694073911759317680651453 4760277716909744130244295)
          ·
            refine ⟨7140416575364616195366443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760277716909744130244295 7140416575364616195366443)
            ·
              refine ⟨10710624863046924293049665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140416575364616195366443 10710624863046924293049665)
              ·
                refine ⟨8032968647285193219787249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10710624863046924293049665 8032968647285193219787249)
                ·
                  refine ⟨6024726485463894914840437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8032968647285193219787249 6024726485463894914840437)
                  ·
                    refine ⟨564818108012240148266291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6024726485463894914840437 564818108012240148266291)
                    ·
                      rfl

theorem cell22_1649969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1649969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649969 prefixEnd_1649969 := by exact prefixLift 1649969
  have htrace : WordTrace (prefixWord ++ tailWord_1649969) baseStart_1649969 baseEnd_1649969 := by
    simpa [prefixWord, tailWord_1649969, baseEnd_1649969] using wordTrace_append hprefix tailTrace_1649969
  have hstable : (prefixWord ++ tailWord_1649969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649969).length < 2 ^ (prefixWord ++ tailWord_1649969).sum := by decide
  have hdescent : baseEnd_1649969 < baseStart_1649969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649971 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 5]
def baseStart_1649971 : Nat := 118140960795 + 1649971 * 2 ^ 59
def prefixEnd_1649971 : Nat := 4983230072969 + 3 ^ 40 * 1649971 * 2
def baseEnd_1649971 : Nat := 188272930884370936572095

theorem tailTrace_1649971 : CollatzResearch.WordTrace tailWord_1649971 prefixEnd_1649971 188272930884370936572095 := by
  unfold tailWord_1649971
  simp only [CollatzResearch.WordTrace]
  refine ⟨60179386305444334457253767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40119590870296222971502511 60179386305444334457253767)
  ·
    refine ⟨90269079458166501685880651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60179386305444334457253767 90269079458166501685880651)
    ·
      refine ⟨135403619187249752528820977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90269079458166501685880651 135403619187249752528820977)
      ·
        refine ⟨101552714390437314396615733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135403619187249752528820977 101552714390437314396615733)
        ·
          refine ⟨9520566974103498224682725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101552714390437314396615733 9520566974103498224682725)
          ·
            refine ⟨1785106307644405917128011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9520566974103498224682725 1785106307644405917128011)
            ·
              refine ⟨2677659461466608875692017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785106307644405917128011 2677659461466608875692017)
              ·
                refine ⟨2008244596099956656769013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677659461466608875692017 2008244596099956656769013)
                ·
                  refine ⟨188272930884370936572095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2008244596099956656769013 188272930884370936572095)
                  ·
                    rfl

theorem cell22_1649971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 5].length) (baseStart_1649971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1649971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1649971 prefixEnd_1649971 := by exact prefixLift 1649971
  have htrace : WordTrace (prefixWord ++ tailWord_1649971) baseStart_1649971 baseEnd_1649971 := by
    simpa [prefixWord, tailWord_1649971, baseEnd_1649971] using wordTrace_append hprefix tailTrace_1649971
  have hstable : (prefixWord ++ tailWord_1649971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649971).length < 2 ^ (prefixWord ++ tailWord_1649971).sum := by decide
  have hdescent : baseEnd_1649971 < baseStart_1649971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650001 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_1650001 : Nat := 118140960795 + 1650001 * 2 ^ 59
def prefixEnd_1650001 : Nat := 4983230072969 + 3 ^ 40 * 1650001 * 2
def baseEnd_1650001 : Nat := 564829062266202731466193

theorem tailTrace_1650001 : CollatzResearch.WordTrace tailWord_1650001 prefixEnd_1650001 564829062266202731466193 := by
  unfold tailWord_1650001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60180480495335649580845857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40120320330223766387230571 60180480495335649580845857)
  ·
    refine ⟨45135360371501737185634393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60180480495335649580845857 45135360371501737185634393)
    ·
      refine ⟨33851520278626302889225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45135360371501737185634393 33851520278626302889225795)
      ·
        refine ⟨50777280417939454333838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33851520278626302889225795 50777280417939454333838693)
        ·
          refine ⟨9520740078363647687594755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50777280417939454333838693 9520740078363647687594755)
          ·
            refine ⟨14281110117545471531392133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520740078363647687594755 14281110117545471531392133)
            ·
              refine ⟨2677708147039775912136025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14281110117545471531392133 2677708147039775912136025)
              ·
                refine ⟨2008281110279831934102019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677708147039775912136025 2008281110279831934102019)
                ·
                  refine ⟨3012421665419747901153029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008281110279831934102019 3012421665419747901153029)
                  ·
                    refine ⟨564829062266202731466193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012421665419747901153029 564829062266202731466193)
                    ·
                      rfl

theorem cell22_1650001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_1650001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650001 prefixEnd_1650001 := by exact prefixLift 1650001
  have htrace : WordTrace (prefixWord ++ tailWord_1650001) baseStart_1650001 baseEnd_1650001 := by
    simpa [prefixWord, tailWord_1650001, baseEnd_1650001] using wordTrace_append hprefix tailTrace_1650001
  have hstable : (prefixWord ++ tailWord_1650001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650001).length < 2 ^ (prefixWord ++ tailWord_1650001).sum := by decide
  have hdescent : baseEnd_1650001 < baseStart_1650001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650031 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 2, 3]
def baseStart_1650031 : Nat := 118140960795 + 1650031 * 2 ^ 59
def prefixEnd_1650031 : Nat := 4983230072969 + 3 ^ 40 * 1650031 * 2
def baseEnd_1650031 : Nat := 564839331879292653216101

theorem tailTrace_1650031 : CollatzResearch.WordTrace tailWord_1650031 prefixEnd_1650031 564839331879292653216101 := by
  unfold tailWord_1650031
  simp only [CollatzResearch.WordTrace]
  refine ⟨60181574685226964704437947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40121049790151309802958631 60181574685226964704437947)
  ·
    refine ⟨90272362027840447056656921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60181574685226964704437947 90272362027840447056656921)
    ·
      refine ⟨67704271520880335292492691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90272362027840447056656921 67704271520880335292492691)
      ·
        refine ⟨101556407281320502938739037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67704271520880335292492691 101556407281320502938739037)
        ·
          refine ⟨38083652730495188602027139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101556407281320502938739037 38083652730495188602027139)
          ·
            refine ⟨57125479095742782903040709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38083652730495188602027139 57125479095742782903040709)
            ·
              refine ⟨10711027330451771794320133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57125479095742782903040709 10711027330451771794320133)
              ·
                refine ⟨2008317624459707211435025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10711027330451771794320133 2008317624459707211435025)
                ·
                  refine ⟨1506238218344780408576269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2008317624459707211435025 1506238218344780408576269)
                  ·
                    refine ⟨564839331879292653216101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506238218344780408576269 564839331879292653216101)
                    ·
                      rfl

theorem cell22_1650031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_1650031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650031 prefixEnd_1650031 := by exact prefixLift 1650031
  have htrace : WordTrace (prefixWord ++ tailWord_1650031) baseStart_1650031 baseEnd_1650031 := by
    simpa [prefixWord, tailWord_1650031, baseEnd_1650031] using wordTrace_append hprefix tailTrace_1650031
  have hstable : (prefixWord ++ tailWord_1650031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650031).length < 2 ^ (prefixWord ++ tailWord_1650031).sum := by decide
  have hdescent : baseEnd_1650031 < baseStart_1650031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650044 : List Nat := [2, 2, 2, 1, 1, 1, 6, 7]
def baseStart_1650044 : Nat := 118140960795 + 1650044 * 2 ^ 59
def prefixEnd_1650044 : Nat := 4983230072969 + 3 ^ 40 * 1650044 * 2
def baseEnd_1650044 : Nat := 62760420227218328071229

theorem tailTrace_1650044 : CollatzResearch.WordTrace tailWord_1650044 prefixEnd_1650044 62760420227218328071229 := by
  unfold tailWord_1650044
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091024417089933962330593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40121365889453245283107457 30091024417089933962330593)
  ·
    refine ⟨22568268312817450471747945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30091024417089933962330593 22568268312817450471747945)
    ·
      refine ⟨16926201234613087853810959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22568268312817450471747945 16926201234613087853810959)
      ·
        refine ⟨25389301851919631780716439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16926201234613087853810959 25389301851919631780716439)
        ·
          refine ⟨38083952777879447671074659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25389301851919631780716439 38083952777879447671074659)
          ·
            refine ⟨57125929166819171506611989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38083952777879447671074659 57125929166819171506611989)
            ·
              refine ⟨2677777929694648664372437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57125929166819171506611989 2677777929694648664372437)
              ·
                refine ⟨62760420227218328071229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2677777929694648664372437 62760420227218328071229)
                ·
                  rfl

theorem cell22_1650044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_1650044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650044 prefixEnd_1650044 := by exact prefixLift 1650044
  have htrace : WordTrace (prefixWord ++ tailWord_1650044) baseStart_1650044 baseEnd_1650044 := by
    simpa [prefixWord, tailWord_1650044, baseEnd_1650044] using wordTrace_append hprefix tailTrace_1650044
  have hstable : (prefixWord ++ tailWord_1650044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650044).length < 2 ^ (prefixWord ++ tailWord_1650044).sum := by decide
  have hdescent : baseEnd_1650044 < baseStart_1650044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
