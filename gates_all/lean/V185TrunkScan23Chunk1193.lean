import V185TrunkScan23Chunk1192

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7068348 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7068348 : Nat := 118140960795 + 7068348 * 2 ^ 59
def prefixEnd_7068348 : Nat := 4983230072969 + 3 ^ 40 * 7068348 * 2
def baseEnd_7068348 : Nat := 3629459957246216289643265

theorem tailTrace_7068348 : CollatzResearch.WordTrace tailWord_7068348 prefixEnd_7068348 3629459957246216289643265 := by
  unfold tailWord_7068348
  simp only [CollatzResearch.WordTrace]
  refine ⟨128901915498294924287590849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171869220664393232383454465 128901915498294924287590849)
  ·
    refine ⟨96676436623721193215693137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128901915498294924287590849 96676436623721193215693137)
    ·
      refine ⟨72507327467790894911769853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96676436623721193215693137 72507327467790894911769853)
      ·
        refine ⟨27190247800421585591913695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72507327467790894911769853 27190247800421585591913695)
        ·
          refine ⟨40785371700632378387870543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190247800421585591913695 40785371700632378387870543)
          ·
            refine ⟨61178057550948567581805815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40785371700632378387870543 61178057550948567581805815)
            ·
              refine ⟨91767086326422851372708723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61178057550948567581805815 91767086326422851372708723)
              ·
                refine ⟨137650629489634277059063085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91767086326422851372708723 137650629489634277059063085)
                ·
                  refine ⟨51618986058612853897148657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137650629489634277059063085 51618986058612853897148657)
                  ·
                    refine ⟨38714239543959640422861493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51618986058612853897148657 38714239543959640422861493)
                    ·
                      refine ⟨3629459957246216289643265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38714239543959640422861493 3629459957246216289643265)
                      ·
                        rfl

theorem cell23_7068348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7068348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068348 prefixEnd_7068348 := by exact prefixLift 7068348
  have htrace : WordTrace (prefixWord ++ tailWord_7068348) baseStart_7068348 baseEnd_7068348 := by
    simpa [prefixWord, tailWord_7068348, baseEnd_7068348] using wordTrace_append hprefix tailTrace_7068348
  have hstable : (prefixWord ++ tailWord_7068348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068348).length < 2 ^ (prefixWord ++ tailWord_7068348).sum := by decide
  have hdescent : baseEnd_7068348 < baseStart_7068348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068353 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7068353 : Nat := 118140960795 + 7068353 * 2 ^ 59
def prefixEnd_7068353 : Nat := 4983230072969 + 3 ^ 40 * 7068353 * 2
def baseEnd_7068353 : Nat := 3629462524649488770080743

theorem tailTrace_7068353 : CollatzResearch.WordTrace tailWord_7068353 prefixEnd_7068353 3629462524649488770080743 := by
  unfold tailWord_7068353
  simp only [CollatzResearch.WordTrace]
  refine ⟨257804013361571734429113713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171869342241047822952742475 257804013361571734429113713)
  ·
    refine ⟨193353010021178800821835285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257804013361571734429113713 193353010021178800821835285)
    ·
      refine ⟨9063422344742756288523529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193353010021178800821835285 9063422344742756288523529)
      ·
        refine ⟨6797566758557067216392647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063422344742756288523529 6797566758557067216392647)
        ·
          refine ⟨10196350137835600824588971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797566758557067216392647 10196350137835600824588971)
          ·
            refine ⟨15294525206753401236883457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196350137835600824588971 15294525206753401236883457)
            ·
              refine ⟨11470893905065050927662593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15294525206753401236883457 11470893905065050927662593)
              ·
                refine ⟨8603170428798788195746945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11470893905065050927662593 8603170428798788195746945)
                ·
                  refine ⟨6452377821599091146810209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603170428798788195746945 6452377821599091146810209)
                  ·
                    refine ⟨4839283366199318360107657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452377821599091146810209 4839283366199318360107657)
                    ·
                      refine ⟨3629462524649488770080743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839283366199318360107657 3629462524649488770080743)
                      ·
                        rfl

theorem cell23_7068353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7068353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068353 prefixEnd_7068353 := by exact prefixLift 7068353
  have htrace : WordTrace (prefixWord ++ tailWord_7068353) baseStart_7068353 baseEnd_7068353 := by
    simpa [prefixWord, tailWord_7068353, baseEnd_7068353] using wordTrace_append hprefix tailTrace_7068353
  have hstable : (prefixWord ++ tailWord_7068353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068353).length < 2 ^ (prefixWord ++ tailWord_7068353).sum := by decide
  have hdescent : baseEnd_7068353 < baseStart_7068353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068375 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_7068375 : Nat := 118140960795 + 7068375 * 2 ^ 59
def prefixEnd_7068375 : Nat := 4983230072969 + 3 ^ 40 * 7068375 * 2
def baseEnd_7068375 : Nat := 3629473821223887684005641

theorem tailTrace_7068375 : CollatzResearch.WordTrace tailWord_7068375 prefixEnd_7068375 3629473821223887684005641 := by
  unfold tailWord_7068375
  simp only [CollatzResearch.WordTrace]
  refine ⟨257804815767492032186414579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171869877178328021457609719 257804815767492032186414579)
  ·
    refine ⟨386707223651238048279621869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257804815767492032186414579 386707223651238048279621869)
    ·
      refine ⟨145015208869214268104858201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386707223651238048279621869 145015208869214268104858201)
      ·
        refine ⟨108761406651910701078643651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145015208869214268104858201 108761406651910701078643651)
        ·
          refine ⟨163142109977866051617965477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108761406651910701078643651 163142109977866051617965477)
          ·
            refine ⟨30589145620849884678368527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163142109977866051617965477 30589145620849884678368527)
            ·
              refine ⟨45883718431274827017552791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30589145620849884678368527 45883718431274827017552791)
              ·
                refine ⟨68825577646912240526329187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45883718431274827017552791 68825577646912240526329187)
                ·
                  refine ⟨103238366470368360789493781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68825577646912240526329187 103238366470368360789493781)
                  ·
                    refine ⟨4839298428298516912007521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103238366470368360789493781 4839298428298516912007521)
                    ·
                      refine ⟨3629473821223887684005641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839298428298516912007521 3629473821223887684005641)
                      ·
                        rfl

theorem cell23_7068375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_7068375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068375 prefixEnd_7068375 := by exact prefixLift 7068375
  have htrace : WordTrace (prefixWord ++ tailWord_7068375) baseStart_7068375 baseEnd_7068375 := by
    simpa [prefixWord, tailWord_7068375, baseEnd_7068375] using wordTrace_append hprefix tailTrace_7068375
  have hstable : (prefixWord ++ tailWord_7068375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068375).length < 2 ^ (prefixWord ++ tailWord_7068375).sum := by decide
  have hdescent : baseEnd_7068375 < baseStart_7068375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068385 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_7068385 : Nat := 118140960795 + 7068385 * 2 ^ 59
def prefixEnd_7068385 : Nat := 4983230072969 + 3 ^ 40 * 7068385 * 2
def baseEnd_7068385 : Nat := 1209826318676810881626865

theorem tailTrace_7068385 : CollatzResearch.WordTrace tailWord_7068385 prefixEnd_7068385 1209826318676810881626865 := by
  unfold tailWord_7068385
  simp only [CollatzResearch.WordTrace]
  refine ⟨257805180497455803894278609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171870120331637202596185739 257805180497455803894278609)
  ·
    refine ⟨193353885373091852920708957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257805180497455803894278609 193353885373091852920708957)
    ·
      refine ⟨72507707014909444845265859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193353885373091852920708957 72507707014909444845265859)
      ·
        refine ⟨108761560522364167267898789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72507707014909444845265859 108761560522364167267898789)
        ·
          refine ⟨20392792597943281362731023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108761560522364167267898789 20392792597943281362731023)
          ·
            refine ⟨30589188896914922044096535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20392792597943281362731023 30589188896914922044096535)
            ·
              refine ⟨45883783345372383066144803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30589188896914922044096535 45883783345372383066144803)
              ·
                refine ⟨68825675018058574599217205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45883783345372383066144803 68825675018058574599217205)
                ·
                  refine ⟨6452407032942991368676613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68825675018058574599217205 6452407032942991368676613)
                  ·
                    refine ⟨1209826318676810881626865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6452407032942991368676613 1209826318676810881626865)
                    ·
                      rfl

theorem cell23_7068385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_7068385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068385 prefixEnd_7068385 := by exact prefixLift 7068385
  have htrace : WordTrace (prefixWord ++ tailWord_7068385) baseStart_7068385 baseEnd_7068385 := by
    simpa [prefixWord, tailWord_7068385, baseEnd_7068385] using wordTrace_append hprefix tailTrace_7068385
  have hstable : (prefixWord ++ tailWord_7068385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068385).length < 2 ^ (prefixWord ++ tailWord_7068385).sum := by decide
  have hdescent : baseEnd_7068385 < baseStart_7068385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068435 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 5, 2]
def baseStart_7068435 : Nat := 118140960795 + 7068435 * 2 ^ 59
def prefixEnd_7068435 : Nat := 4983230072969 + 3 ^ 40 * 7068435 * 2
def baseEnd_7068435 : Nat := 3629504630063157449255365

theorem tailTrace_7068435 : CollatzResearch.WordTrace tailWord_7068435 prefixEnd_7068435 3629504630063157449255365 := by
  unfold tailWord_7068435
  simp only [CollatzResearch.WordTrace]
  refine ⟨257807004147274662433598759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171871336098183108289065839 257807004147274662433598759)
  ·
    refine ⟨386710506220911993650398139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257807004147274662433598759 386710506220911993650398139)
    ·
      refine ⟨580065759331367990475597209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386710506220911993650398139 580065759331367990475597209)
      ·
        refine ⟨435049319498525992856697907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580065759331367990475597209 435049319498525992856697907)
        ·
          refine ⟨652573979247788989285046861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435049319498525992856697907 652573979247788989285046861)
          ·
            refine ⟨244715242217920870981892573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652573979247788989285046861 244715242217920870981892573)
            ·
              refine ⟨91768215831720326618209715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244715242217920870981892573 91768215831720326618209715)
              ·
                refine ⟨137652323747580489927314573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91768215831720326618209715 137652323747580489927314573)
                ·
                  refine ⟨51619621405342683722742965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137652323747580489927314573 51619621405342683722742965)
                  ·
                    refine ⟨4839339506750876599007153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51619621405342683722742965 4839339506750876599007153)
                    ·
                      refine ⟨3629504630063157449255365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839339506750876599007153 3629504630063157449255365)
                      ·
                        rfl

theorem cell23_7068435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5, 2].length) (baseStart_7068435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068435 prefixEnd_7068435 := by exact prefixLift 7068435
  have htrace : WordTrace (prefixWord ++ tailWord_7068435) baseStart_7068435 baseEnd_7068435 := by
    simpa [prefixWord, tailWord_7068435, baseEnd_7068435] using wordTrace_append hprefix tailTrace_7068435
  have hstable : (prefixWord ++ tailWord_7068435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068435).length < 2 ^ (prefixWord ++ tailWord_7068435).sum := by decide
  have hdescent : baseEnd_7068435 < baseStart_7068435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068442 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_7068442 : Nat := 118140960795 + 7068442 * 2 ^ 59
def prefixEnd_7068442 : Nat := 4983230072969 + 3 ^ 40 * 7068442 * 2
def baseEnd_7068442 : Nat := 3629508224427738921867833

theorem tailTrace_7068442 : CollatzResearch.WordTrace tailWord_7068442 prefixEnd_7068442 3629508224427738921867833 := by
  unfold tailWord_7068442
  simp only [CollatzResearch.WordTrace]
  refine ⟨64451814864562325657275895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171871506305499535086069053 64451814864562325657275895)
  ·
    refine ⟨96677722296843488485913843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64451814864562325657275895 96677722296843488485913843)
    ·
      refine ⟨145016583445265232728870765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96677722296843488485913843 145016583445265232728870765)
      ·
        refine ⟨54381218791974462273326537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145016583445265232728870765 54381218791974462273326537)
        ·
          refine ⟨40785914093980846704994903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54381218791974462273326537 40785914093980846704994903)
          ·
            refine ⟨61178871140971270057492355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40785914093980846704994903 61178871140971270057492355)
            ·
              refine ⟨91768306711456905086238533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61178871140971270057492355 91768306711456905086238533)
              ·
                refine ⟨17206557508398169703669725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91768306711456905086238533 17206557508398169703669725)
                ·
                  refine ⟨6452459065649313638876147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17206557508398169703669725 6452459065649313638876147)
                  ·
                    refine ⟨9678688598473970458314221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6452459065649313638876147 9678688598473970458314221)
                    ·
                      refine ⟨3629508224427738921867833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9678688598473970458314221 3629508224427738921867833)
                      ·
                        rfl

theorem cell23_7068442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_7068442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068442 prefixEnd_7068442 := by exact prefixLift 7068442
  have htrace : WordTrace (prefixWord ++ tailWord_7068442) baseStart_7068442 baseEnd_7068442 := by
    simpa [prefixWord, tailWord_7068442, baseEnd_7068442] using wordTrace_append hprefix tailTrace_7068442
  have hstable : (prefixWord ++ tailWord_7068442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068442).length < 2 ^ (prefixWord ++ tailWord_7068442).sum := by decide
  have hdescent : baseEnd_7068442 < baseStart_7068442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068469 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_7068469 : Nat := 118140960795 + 7068469 * 2 ^ 59
def prefixEnd_7068469 : Nat := 4983230072969 + 3 ^ 40 * 7068469 * 2
def baseEnd_7068469 : Nat := 3629522088405410316230209

theorem tailTrace_7068469 : CollatzResearch.WordTrace tailWord_7068469 prefixEnd_7068469 3629522088405410316230209 := by
  unfold tailWord_7068469
  simp only [CollatzResearch.WordTrace]
  refine ⟨257808244229151486240336461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171872162819434324160224307 257808244229151486240336461)
  ·
    refine ⟨96678091585931807340126173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257808244229151486240336461 96678091585931807340126173)
    ·
      refine ⟨36254284344724427752547315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96678091585931807340126173 36254284344724427752547315)
      ·
        refine ⟨54381426517086641628820973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36254284344724427752547315 54381426517086641628820973)
        ·
          refine ⟨20393034943907490610807865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54381426517086641628820973 20393034943907490610807865)
          ·
            refine ⟨15294776207930617958105899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20393034943907490610807865 15294776207930617958105899)
            ·
              refine ⟨22942164311895926937158849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294776207930617958105899 22942164311895926937158849)
              ·
                refine ⟨17206623233921945202869137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22942164311895926937158849 17206623233921945202869137)
                ·
                  refine ⟨12904967425441458902151853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17206623233921945202869137 12904967425441458902151853)
                  ·
                    refine ⟨4839362784540547088306945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12904967425441458902151853 4839362784540547088306945)
                    ·
                      refine ⟨3629522088405410316230209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839362784540547088306945 3629522088405410316230209)
                      ·
                        rfl

theorem cell23_7068469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_7068469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068469 prefixEnd_7068469 := by exact prefixLift 7068469
  have htrace : WordTrace (prefixWord ++ tailWord_7068469) baseStart_7068469 baseEnd_7068469 := by
    simpa [prefixWord, tailWord_7068469, baseEnd_7068469] using wordTrace_append hprefix tailTrace_7068469
  have hstable : (prefixWord ++ tailWord_7068469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068469).length < 2 ^ (prefixWord ++ tailWord_7068469).sum := by decide
  have hdescent : baseEnd_7068469 < baseStart_7068469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068526 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7068526 : Nat := 118140960795 + 7068526 * 2 ^ 59
def prefixEnd_7068526 : Nat := 4983230072969 + 3 ^ 40 * 7068526 * 2
def baseEnd_7068526 : Nat := 1209850452267572197739149

theorem tailTrace_7068526 : CollatzResearch.WordTrace tailWord_7068526 prefixEnd_7068526 1209850452267572197739149 := by
  unfold tailWord_7068526
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226290398743123121895179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171873548793296656650107621 32226290398743123121895179)
  ·
    refine ⟨48339435598114684682842769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32226290398743123121895179 48339435598114684682842769)
    ·
      refine ⟨36254576698586013512132077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48339435598114684682842769 36254576698586013512132077)
      ·
        refine ⟨13595466261969755067049529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36254576698586013512132077 13595466261969755067049529)
        ·
          refine ⟨10196599696477316300287147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13595466261969755067049529 10196599696477316300287147)
          ·
            refine ⟨15294899544715974450430721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196599696477316300287147 15294899544715974450430721)
            ·
              refine ⟨11471174658536980837823041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15294899544715974450430721 11471174658536980837823041)
              ·
                refine ⟨8603380993902735628367281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471174658536980837823041 8603380993902735628367281)
                ·
                  refine ⟨6452535745427051721275461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603380993902735628367281 6452535745427051721275461)
                  ·
                    refine ⟨1209850452267572197739149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6452535745427051721275461 1209850452267572197739149)
                    ·
                      rfl

theorem cell23_7068526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7068526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068526 prefixEnd_7068526 := by exact prefixLift 7068526
  have htrace : WordTrace (prefixWord ++ tailWord_7068526) baseStart_7068526 baseEnd_7068526 := by
    simpa [prefixWord, tailWord_7068526, baseEnd_7068526] using wordTrace_append hprefix tailTrace_7068526
  have hstable : (prefixWord ++ tailWord_7068526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068526).length < 2 ^ (prefixWord ++ tailWord_7068526).sum := by decide
  have hdescent : baseEnd_7068526 < baseStart_7068526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068533 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_7068533 : Nat := 118140960795 + 7068533 * 2 ^ 59
def prefixEnd_7068533 : Nat := 4983230072969 + 3 ^ 40 * 7068533 * 2
def baseEnd_7068533 : Nat := 3629554951167298065829915

theorem tailTrace_7068533 : CollatzResearch.WordTrace tailWord_7068533 prefixEnd_7068533 3629554951167298065829915 := by
  unfold tailWord_7068533
  simp only [CollatzResearch.WordTrace]
  refine ⟨257810578500919625170666253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171873719000613083447110835 257810578500919625170666253)
  ·
    refine ⟨96678966937844859438999845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257810578500919625170666253 96678966937844859438999845)
    ·
      refine ⟨18127306300845911144812471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96678966937844859438999845 18127306300845911144812471)
      ·
        refine ⟨27190959451268866717218707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127306300845911144812471 27190959451268866717218707)
        ·
          refine ⟨40786439176903300075828061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190959451268866717218707 40786439176903300075828061)
          ·
            refine ⟨15294914691338737528435523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40786439176903300075828061 15294914691338737528435523)
            ·
              refine ⟨22942372037008106292653285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294914691338737528435523 22942372037008106292653285)
              ·
                refine ⟨4301694756939019929872491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22942372037008106292653285 4301694756939019929872491)
                ·
                  refine ⟨6452542135408529894808737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301694756939019929872491 6452542135408529894808737)
                  ·
                    refine ⟨4839406601556397421106553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452542135408529894808737 4839406601556397421106553)
                    ·
                      refine ⟨3629554951167298065829915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839406601556397421106553 3629554951167298065829915)
                      ·
                        rfl

theorem cell23_7068533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_7068533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068533 prefixEnd_7068533 := by exact prefixLift 7068533
  have htrace : WordTrace (prefixWord ++ tailWord_7068533) baseStart_7068533 baseEnd_7068533 := by
    simpa [prefixWord, tailWord_7068533, baseEnd_7068533] using wordTrace_append hprefix tailTrace_7068533
  have hstable : (prefixWord ++ tailWord_7068533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068533).length < 2 ^ (prefixWord ++ tailWord_7068533).sum := by decide
  have hdescent : baseEnd_7068533 < baseStart_7068533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068549 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_7068549 : Nat := 118140960795 + 7068549 * 2 ^ 59
def prefixEnd_7068549 : Nat := 4983230072969 + 3 ^ 40 * 7068549 * 2
def baseEnd_7068549 : Nat := 3629563166857770003229841

theorem tailTrace_7068549 : CollatzResearch.WordTrace tailWord_7068549 prefixEnd_7068549 3629563166857770003229841 := by
  unfold tailWord_7068549
  simp only [CollatzResearch.WordTrace]
  refine ⟨257811162068861659903248701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171874108045907773268832467 257811162068861659903248701)
  ·
    refine ⟨96679185775823122463718263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257811162068861659903248701 96679185775823122463718263)
    ·
      refine ⟨145018778663734683695577395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96679185775823122463718263 145018778663734683695577395)
      ·
        refine ⟨217528167995602025543366093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145018778663734683695577395 217528167995602025543366093)
        ·
          refine ⟨81573062998350759578762285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217528167995602025543366093 81573062998350759578762285)
          ·
            refine ⟨30589898624381534842035857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81573062998350759578762285 30589898624381534842035857)
            ·
              refine ⟨22942423968286151131526893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30589898624381534842035857 22942423968286151131526893)
              ·
                refine ⟨8603408988107306674322585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22942423968286151131526893 8603408988107306674322585)
                ·
                  refine ⟨6452556741080480005741939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603408988107306674322585 6452556741080480005741939)
                  ·
                    refine ⟨9678835111620720008612909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6452556741080480005741939 9678835111620720008612909)
                    ·
                      refine ⟨3629563166857770003229841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9678835111620720008612909 3629563166857770003229841)
                      ·
                        rfl

theorem cell23_7068549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_7068549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068549 prefixEnd_7068549 := by exact prefixLift 7068549
  have htrace : WordTrace (prefixWord ++ tailWord_7068549) baseStart_7068549 baseEnd_7068549 := by
    simpa [prefixWord, tailWord_7068549, baseEnd_7068549] using wordTrace_append hprefix tailTrace_7068549
  have hstable : (prefixWord ++ tailWord_7068549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068549).length < 2 ^ (prefixWord ++ tailWord_7068549).sum := by decide
  have hdescent : baseEnd_7068549 < baseStart_7068549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068576 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2]
def baseStart_7068576 : Nat := 118140960795 + 7068576 * 2 ^ 59
def prefixEnd_7068576 : Nat := 4983230072969 + 3 ^ 40 * 7068576 * 2
def baseEnd_7068576 : Nat := 3629577030835441397592217

theorem tailTrace_7068576 : CollatzResearch.WordTrace tailWord_7068576 prefixEnd_7068576 3629577030835441397592217 := by
  unfold tailWord_7068576
  simp only [CollatzResearch.WordTrace]
  refine ⟨128906073419881921757240791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171874764559842562342987721 128906073419881921757240791)
  ·
    refine ⟨193359110129822882635861187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128906073419881921757240791 193359110129822882635861187)
    ·
      refine ⟨290038665194734323953791781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193359110129822882635861187 290038665194734323953791781)
      ·
        refine ⟨54382249724012685741335959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290038665194734323953791781 54382249724012685741335959)
        ·
          refine ⟨81573374586019028612003939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54382249724012685741335959 81573374586019028612003939)
          ·
            refine ⟨122360061879028542918005909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81573374586019028612003939 122360061879028542918005909)
            ·
              refine ⟨5735627900579462949281527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122360061879028542918005909 5735627900579462949281527)
              ·
                refine ⟨8603441850869194423922291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735627900579462949281527 8603441850869194423922291)
                ·
                  refine ⟨12905162776303791635883437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603441850869194423922291 12905162776303791635883437)
                  ·
                    refine ⟨4839436041113921863456289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12905162776303791635883437 4839436041113921863456289)
                    ·
                      refine ⟨3629577030835441397592217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839436041113921863456289 3629577030835441397592217)
                      ·
                        rfl

theorem cell23_7068576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_7068576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068576 prefixEnd_7068576 := by exact prefixLift 7068576
  have htrace : WordTrace (prefixWord ++ tailWord_7068576) baseStart_7068576 baseEnd_7068576 := by
    simpa [prefixWord, tailWord_7068576, baseEnd_7068576] using wordTrace_append hprefix tailTrace_7068576
  have hstable : (prefixWord ++ tailWord_7068576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068576).length < 2 ^ (prefixWord ++ tailWord_7068576).sum := by decide
  have hdescent : baseEnd_7068576 < baseStart_7068576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068583 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_7068583 : Nat := 118140960795 + 7068583 * 2 ^ 59
def prefixEnd_7068583 : Nat := 4983230072969 + 3 ^ 40 * 7068583 * 2
def baseEnd_7068583 : Nat := 3629580625200022870204685

theorem tailTrace_7068583 : CollatzResearch.WordTrace tailWord_7068583 prefixEnd_7068583 3629580625200022870204685 := by
  unfold tailWord_7068583
  simp only [CollatzResearch.WordTrace]
  refine ⟨257812402150738483709986403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171874934767158989139990935 257812402150738483709986403)
  ·
    refine ⟨386718603226107725564979605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257812402150738483709986403 386718603226107725564979605)
    ·
      refine ⟨18127434526223799635858419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 386718603226107725564979605 18127434526223799635858419)
      ·
        refine ⟨27191151789335699453787629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127434526223799635858419 27191151789335699453787629)
        ·
          refine ⟨10196681921000887295170361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27191151789335699453787629 10196681921000887295170361)
          ·
            refine ⟨7647511440750665471377771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10196681921000887295170361 7647511440750665471377771)
            ·
              refine ⟨11471267161125998207066657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647511440750665471377771 11471267161125998207066657)
              ·
                refine ⟨8603450370844498655299993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471267161125998207066657 8603450370844498655299993)
                ·
                  refine ⟨6452587778133373991474995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603450370844498655299993 6452587778133373991474995)
                  ·
                    refine ⟨9678881667200060987212493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6452587778133373991474995 9678881667200060987212493)
                    ·
                      refine ⟨3629580625200022870204685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9678881667200060987212493 3629580625200022870204685)
                      ·
                        rfl

theorem cell23_7068583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_7068583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068583 prefixEnd_7068583 := by exact prefixLift 7068583
  have htrace : WordTrace (prefixWord ++ tailWord_7068583) baseStart_7068583 baseEnd_7068583 := by
    simpa [prefixWord, tailWord_7068583, baseEnd_7068583] using wordTrace_append hprefix tailTrace_7068583
  have hstable : (prefixWord ++ tailWord_7068583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068583).length < 2 ^ (prefixWord ++ tailWord_7068583).sum := by decide
  have hdescent : baseEnd_7068583 < baseStart_7068583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068585 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_7068585 : Nat := 118140960795 + 7068585 * 2 ^ 59
def prefixEnd_7068585 : Nat := 4983230072969 + 3 ^ 40 * 7068585 * 2
def baseEnd_7068585 : Nat := 3629581652161331862379675

theorem tailTrace_7068585 : CollatzResearch.WordTrace tailWord_7068585 prefixEnd_7068585 3629581652161331862379675 := by
  unfold tailWord_7068585
  simp only [CollatzResearch.WordTrace]
  refine ⟨257812475096731238051559209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171874983397820825367706139 257812475096731238051559209)
  ·
    refine ⟨193359356322548428538669407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257812475096731238051559209 193359356322548428538669407)
    ·
      refine ⟨290039034483822642808004111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193359356322548428538669407 290039034483822642808004111)
      ·
        refine ⟨435058551725733964212006167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290039034483822642808004111 435058551725733964212006167)
        ·
          refine ⟨652587827588600946318009251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435058551725733964212006167 652587827588600946318009251)
          ·
            refine ⟨978881741382901419477013877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652587827588600946318009251 978881741382901419477013877)
            ·
              refine ⟨91770163254647008075970051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 978881741382901419477013877 91770163254647008075970051)
              ·
                refine ⟨137655244881970512113955077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91770163254647008075970051 137655244881970512113955077)
                ·
                  refine ⟨25810358415369471021366577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137655244881970512113955077 25810358415369471021366577)
                  ·
                    refine ⟨19357768811527103266024933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25810358415369471021366577 19357768811527103266024933)
                    ·
                      refine ⟨3629581652161331862379675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19357768811527103266024933 3629581652161331862379675)
                      ·
                        rfl

theorem cell23_7068585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_7068585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068585 prefixEnd_7068585 := by exact prefixLift 7068585
  have htrace : WordTrace (prefixWord ++ tailWord_7068585) baseStart_7068585 baseEnd_7068585 := by
    simpa [prefixWord, tailWord_7068585, baseEnd_7068585] using wordTrace_append hprefix tailTrace_7068585
  have hstable : (prefixWord ++ tailWord_7068585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068585).length < 2 ^ (prefixWord ++ tailWord_7068585).sum := by decide
  have hdescent : baseEnd_7068585 < baseStart_7068585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068625 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_7068625 : Nat := 118140960795 + 7068625 * 2 ^ 59
def prefixEnd_7068625 : Nat := 4983230072969 + 3 ^ 40 * 7068625 * 2
def baseEnd_7068625 : Nat := 1209867397129170568626497

theorem tailTrace_7068625 : CollatzResearch.WordTrace tailWord_7068625 prefixEnd_7068625 1209867397129170568626497 := by
  unfold tailWord_7068625
  simp only [CollatzResearch.WordTrace]
  refine ⟨257813934016586324883015329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171875956011057549922010219 257813934016586324883015329)
  ·
    refine ⟨193360450512439743662261497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257813934016586324883015329 193360450512439743662261497)
    ·
      refine ⟨145020337884329807746696123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193360450512439743662261497 145020337884329807746696123)
      ·
        refine ⟨217530506826494711620044185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145020337884329807746696123 217530506826494711620044185)
        ·
          refine ⟨163147880119871033715033139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217530506826494711620044185 163147880119871033715033139)
          ·
            refine ⟨244721820179806550572549709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163147880119871033715033139 244721820179806550572549709)
            ·
              refine ⟨91770682567427456464706141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244721820179806550572549709 91770682567427456464706141)
              ·
                refine ⟨34414005962785296174264803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91770682567427456464706141 34414005962785296174264803)
                ·
                  refine ⟨51621008944177944261397205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34414005962785296174264803 51621008944177944261397205)
                  ·
                    refine ⟨1209867397129170568626497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51621008944177944261397205 1209867397129170568626497)
                    ·
                      rfl

theorem cell23_7068625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_7068625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068625 prefixEnd_7068625 := by exact prefixLift 7068625
  have htrace : WordTrace (prefixWord ++ tailWord_7068625) baseStart_7068625 baseEnd_7068625 := by
    simpa [prefixWord, tailWord_7068625, baseEnd_7068625] using wordTrace_append hprefix tailTrace_7068625
  have hstable : (prefixWord ++ tailWord_7068625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068625).length < 2 ^ (prefixWord ++ tailWord_7068625).sum := by decide
  have hdescent : baseEnd_7068625 < baseStart_7068625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068675 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_7068675 : Nat := 118140960795 + 7068675 * 2 ^ 59
def prefixEnd_7068675 : Nat := 4983230072969 + 3 ^ 40 * 7068675 * 2
def baseEnd_7068675 : Nat := 3629627865420236510254261

theorem tailTrace_7068675 : CollatzResearch.WordTrace tailWord_7068675 prefixEnd_7068675 3629627865420236510254261 := by
  unfold tailWord_7068675
  simp only [CollatzResearch.WordTrace]
  refine ⟨257815757666405183422335479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171877171777603455614890319 257815757666405183422335479)
  ·
    refine ⟨386723636499607775133503219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257815757666405183422335479 386723636499607775133503219)
    ·
      refine ⟨580085454749411662700254829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386723636499607775133503219 580085454749411662700254829)
      ·
        refine ⟨217532045531029373512595561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580085454749411662700254829 217532045531029373512595561)
        ·
          refine ⟨163149034148272030134446671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217532045531029373512595561 163149034148272030134446671)
          ·
            refine ⟨244723551222408045201670007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163149034148272030134446671 244723551222408045201670007)
            ·
              refine ⟨367085326833612067802505011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244723551222408045201670007 367085326833612067802505011)
              ·
                refine ⟨550627990250418101703757517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367085326833612067802505011 550627990250418101703757517)
                ·
                  refine ⟨206485496343906788138909069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550627990250418101703757517 206485496343906788138909069)
                  ·
                    refine ⟨77432061128965045552090901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206485496343906788138909069 77432061128965045552090901)
                    ·
                      refine ⟨3629627865420236510254261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77432061128965045552090901 3629627865420236510254261)
                      ·
                        rfl

theorem cell23_7068675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_7068675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068675 prefixEnd_7068675 := by exact prefixLift 7068675
  have htrace : WordTrace (prefixWord ++ tailWord_7068675) baseStart_7068675 baseEnd_7068675 := by
    simpa [prefixWord, tailWord_7068675, baseEnd_7068675] using wordTrace_append hprefix tailTrace_7068675
  have hstable : (prefixWord ++ tailWord_7068675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068675).length < 2 ^ (prefixWord ++ tailWord_7068675).sum := by decide
  have hdescent : baseEnd_7068675 < baseStart_7068675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068679 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7068679 : Nat := 118140960795 + 7068679 * 2 ^ 59
def prefixEnd_7068679 : Nat := 4983230072969 + 3 ^ 40 * 7068679 * 2
def baseEnd_7068679 : Nat := 3629629919342854494604243

theorem tailTrace_7068679 : CollatzResearch.WordTrace tailWord_7068679 prefixEnd_7068679 3629629919342854494604243 := by
  unfold tailWord_7068679
  simp only [CollatzResearch.WordTrace]
  refine ⟨257815903558390692105481091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171877269038927128070320727 257815903558390692105481091)
  ·
    refine ⟨386723855337586038158221637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257815903558390692105481091 386723855337586038158221637)
    ·
      refine ⟨72510722875797382154666557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386723855337586038158221637 72510722875797382154666557)
      ·
        refine ⟨27191521078424018307999959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72510722875797382154666557 27191521078424018307999959)
        ·
          refine ⟨40787281617636027461999939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27191521078424018307999959 40787281617636027461999939)
          ·
            refine ⟨61180922426454041192999909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40787281617636027461999939 61180922426454041192999909)
            ·
              refine ⟨11471422954960132723687483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61180922426454041192999909 11471422954960132723687483)
              ·
                refine ⟨17207134432440199085531225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11471422954960132723687483 17207134432440199085531225)
                ·
                  refine ⟨12905350824330149314148419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17207134432440199085531225 12905350824330149314148419)
                  ·
                    refine ⟨19358026236495223971222629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12905350824330149314148419 19358026236495223971222629)
                    ·
                      refine ⟨3629629919342854494604243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19358026236495223971222629 3629629919342854494604243)
                      ·
                        rfl

theorem cell23_7068679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7068679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068679 prefixEnd_7068679 := by exact prefixLift 7068679
  have htrace : WordTrace (prefixWord ++ tailWord_7068679) baseStart_7068679 baseEnd_7068679 := by
    simpa [prefixWord, tailWord_7068679, baseEnd_7068679] using wordTrace_append hprefix tailTrace_7068679
  have hstable : (prefixWord ++ tailWord_7068679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068679).length < 2 ^ (prefixWord ++ tailWord_7068679).sum := by decide
  have hdescent : baseEnd_7068679 < baseStart_7068679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068739 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 5, 2]
def baseStart_7068739 : Nat := 118140960795 + 7068739 * 2 ^ 59
def prefixEnd_7068739 : Nat := 4983230072969 + 3 ^ 40 * 7068739 * 2
def baseEnd_7068739 : Nat := 3629660728182124259853967

theorem tailTrace_7068739 : CollatzResearch.WordTrace tailWord_7068739 prefixEnd_7068739 3629660728182124259853967 := by
  unfold tailWord_7068739
  simp only [CollatzResearch.WordTrace]
  refine ⟨257818091938173322352665271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171878727958782214901776847 257818091938173322352665271)
  ·
    refine ⟨386727137907259983528997907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257818091938173322352665271 386727137907259983528997907)
    ·
      refine ⟨580090706860889975293496861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386727137907259983528997907 580090706860889975293496861)
      ·
        refine ⟨217534015072833740735061323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580090706860889975293496861 217534015072833740735061323)
        ·
          refine ⟨326301022609250611102591985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217534015072833740735061323 326301022609250611102591985)
          ·
            refine ⟨244725766956937958326943989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326301022609250611102591985 244725766956937958326943989)
            ·
              refine ⟨22943040652212933593150999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244725766956937958326943989 22943040652212933593150999)
              ·
                refine ⟨34414560978319400389726499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22943040652212933593150999 34414560978319400389726499)
                ·
                  refine ⟨51621841467479100584589749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34414560978319400389726499 51621841467479100584589749)
                  ·
                    refine ⟨4839547637576165679805289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51621841467479100584589749 4839547637576165679805289)
                    ·
                      refine ⟨3629660728182124259853967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839547637576165679805289 3629660728182124259853967)
                      ·
                        rfl

theorem cell23_7068739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_7068739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068739 prefixEnd_7068739 := by exact prefixLift 7068739
  have htrace : WordTrace (prefixWord ++ tailWord_7068739) baseStart_7068739 baseEnd_7068739 := by
    simpa [prefixWord, tailWord_7068739, baseEnd_7068739] using wordTrace_append hprefix tailTrace_7068739
  have hstable : (prefixWord ++ tailWord_7068739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068739).length < 2 ^ (prefixWord ++ tailWord_7068739).sum := by decide
  have hdescent : baseEnd_7068739 < baseStart_7068739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068756 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_7068756 : Nat := 118140960795 + 7068756 * 2 ^ 59
def prefixEnd_7068756 : Nat := 4983230072969 + 3 ^ 40 * 7068756 * 2
def baseEnd_7068756 : Nat := 3629669457353250693341389

theorem tailTrace_7068756 : CollatzResearch.WordTrace tailWord_7068756 prefixEnd_7068756 3629669457353250693341389 := by
  unfold tailWord_7068756
  simp only [CollatzResearch.WordTrace]
  refine ⟨128909355989555867128017061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171879141319407822837356081 128909355989555867128017061)
  ·
    refine ⟨24170504248041725086503199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128909355989555867128017061 24170504248041725086503199)
    ·
      refine ⟨36255756372062587629754799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24170504248041725086503199 36255756372062587629754799)
      ·
        refine ⟨54383634558093881444632199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36255756372062587629754799 54383634558093881444632199)
        ·
          refine ⟨81575451837140822166948299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54383634558093881444632199 81575451837140822166948299)
          ·
            refine ⟨122363177755711233250422449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81575451837140822166948299 122363177755711233250422449)
            ·
              refine ⟨91772383316783424937816837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122363177755711233250422449 91772383316783424937816837)
              ·
                refine ⟨17207321871896892175840657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91772383316783424937816837 17207321871896892175840657)
                ·
                  refine ⟨12905491403922669131880493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17207321871896892175840657 12905491403922669131880493)
                  ·
                    refine ⟨4839559276471000924455185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12905491403922669131880493 4839559276471000924455185)
                    ·
                      refine ⟨3629669457353250693341389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839559276471000924455185 3629669457353250693341389)
                      ·
                        rfl

theorem cell23_7068756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_7068756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068756 prefixEnd_7068756 := by exact prefixLift 7068756
  have htrace : WordTrace (prefixWord ++ tailWord_7068756) baseStart_7068756 baseEnd_7068756 := by
    simpa [prefixWord, tailWord_7068756, baseEnd_7068756] using wordTrace_append hprefix tailTrace_7068756
  have hstable : (prefixWord ++ tailWord_7068756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068756).length < 2 ^ (prefixWord ++ tailWord_7068756).sum := by decide
  have hdescent : baseEnd_7068756 < baseStart_7068756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068786 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7068786 : Nat := 118140960795 + 7068786 * 2 ^ 59
def prefixEnd_7068786 : Nat := 4983230072969 + 3 ^ 40 * 7068786 * 2
def baseEnd_7068786 : Nat := 3629684861772885575966251

theorem tailTrace_7068786 : CollatzResearch.WordTrace tailWord_7068786 prefixEnd_7068786 3629684861772885575966251 := by
  unfold tailWord_7068786
  simp only [CollatzResearch.WordTrace]
  refine ⟨64454951542250762344906553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171879870779335366253084141 64454951542250762344906553)
  ·
    refine ⟨48341213656688071758679915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64454951542250762344906553 48341213656688071758679915)
    ·
      refine ⟨72511820485032107638019873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48341213656688071758679915 72511820485032107638019873)
      ·
        refine ⟨54383865363774080728514905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72511820485032107638019873 54383865363774080728514905)
        ·
          refine ⟨40787899022830560546386179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54383865363774080728514905 40787899022830560546386179)
          ·
            refine ⟨61181848534245840819579269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40787899022830560546386179 61181848534245840819579269)
            ·
              refine ⟨11471596600171095153671113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61181848534245840819579269 11471596600171095153671113)
              ·
                refine ⟨8603697450128321365253335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471596600171095153671113 8603697450128321365253335)
                ·
                  refine ⟨12905546175192482047880003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603697450128321365253335 12905546175192482047880003)
                  ·
                    refine ⟨19358319262788723071820005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12905546175192482047880003 19358319262788723071820005)
                    ·
                      refine ⟨3629684861772885575966251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19358319262788723071820005 3629684861772885575966251)
                      ·
                        rfl

theorem cell23_7068786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7068786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068786 prefixEnd_7068786 := by exact prefixLift 7068786
  have htrace : WordTrace (prefixWord ++ tailWord_7068786) baseStart_7068786 baseEnd_7068786 := by
    simpa [prefixWord, tailWord_7068786, baseEnd_7068786] using wordTrace_append hprefix tailTrace_7068786
  have hstable : (prefixWord ++ tailWord_7068786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068786).length < 2 ^ (prefixWord ++ tailWord_7068786).sum := by decide
  have hdescent : baseEnd_7068786 < baseStart_7068786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068830 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7068830 : Nat := 118140960795 + 7068830 * 2 ^ 59
def prefixEnd_7068830 : Nat := 4983230072969 + 3 ^ 40 * 7068830 * 2
def baseEnd_7068830 : Nat := 1209902484973894467938683

theorem tailTrace_7068830 : CollatzResearch.WordTrace tailWord_7068830 prefixEnd_7068830 1209902484973894467938683 := by
  unfold tailWord_7068830
  simp only [CollatzResearch.WordTrace]
  refine ⟨32227676372605455611778493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171880940653895763262818629 32227676372605455611778493)
  ·
    refine ⟨12085378639727045854416935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32227676372605455611778493 12085378639727045854416935)
    ·
      refine ⟨18128067959590568781625403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12085378639727045854416935 18128067959590568781625403)
      ·
        refine ⟨27192101939385853172438105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18128067959590568781625403 27192101939385853172438105)
        ·
          refine ⟨20394076454539389879328579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27192101939385853172438105 20394076454539389879328579)
          ·
            refine ⟨30591114681809084818992869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20394076454539389879328579 30591114681809084818992869)
            ·
              refine ⟨5735834002839203403561163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30591114681809084818992869 5735834002839203403561163)
              ·
                refine ⟨8603751004258805105341745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735834002839203403561163 8603751004258805105341745)
                ·
                  refine ⟨6452813253194103829006309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603751004258805105341745 6452813253194103829006309)
                  ·
                    refine ⟨1209902484973894467938683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6452813253194103829006309 1209902484973894467938683)
                    ·
                      rfl

theorem cell23_7068830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7068830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068830 prefixEnd_7068830 := by exact prefixLift 7068830
  have htrace : WordTrace (prefixWord ++ tailWord_7068830) baseStart_7068830 baseEnd_7068830 := by
    simpa [prefixWord, tailWord_7068830, baseEnd_7068830] using wordTrace_append hprefix tailTrace_7068830
  have hstable : (prefixWord ++ tailWord_7068830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068830).length < 2 ^ (prefixWord ++ tailWord_7068830).sum := by decide
  have hdescent : baseEnd_7068830 < baseStart_7068830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7068914 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7068914 : Nat := 118140960795 + 7068914 * 2 ^ 59
def prefixEnd_7068914 : Nat := 4983230072969 + 3 ^ 40 * 7068914 * 2
def baseEnd_7068914 : Nat := 3629750587296661075165663

theorem tailTrace_7068914 : CollatzResearch.WordTrace tailWord_7068914 prefixEnd_7068914 3629750587296661075165663 := by
  unfold tailWord_7068914
  simp only [CollatzResearch.WordTrace]
  refine ⟨64456118678134831810071449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171882983141692884826857197 64456118678134831810071449)
  ·
    refine ⟨48342089008601123857553587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64456118678134831810071449 48342089008601123857553587)
    ·
      refine ⟨72513133512901685786330381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48342089008601123857553587 72513133512901685786330381)
      ·
        refine ⟨27192425067338132169873893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72513133512901685786330381 27192425067338132169873893)
        ·
          refine ⟨5098579700125899781851355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27192425067338132169873893 5098579700125899781851355)
          ·
            refine ⟨7647869550188849672777033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098579700125899781851355 7647869550188849672777033)
            ·
              refine ⟨5735902162641637254582775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647869550188849672777033 5735902162641637254582775)
              ·
                refine ⟨8603853243962455881874163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735902162641637254582775 8603853243962455881874163)
                ·
                  refine ⟨12905779865943683822811245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603853243962455881874163 12905779865943683822811245)
                  ·
                    refine ⟨4839667449728881433554217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12905779865943683822811245 4839667449728881433554217)
                    ·
                      refine ⟨3629750587296661075165663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839667449728881433554217 3629750587296661075165663)
                      ·
                        rfl

theorem cell23_7068914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7068914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7068914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7068914 prefixEnd_7068914 := by exact prefixLift 7068914
  have htrace : WordTrace (prefixWord ++ tailWord_7068914) baseStart_7068914 baseEnd_7068914 := by
    simpa [prefixWord, tailWord_7068914, baseEnd_7068914] using wordTrace_append hprefix tailTrace_7068914
  have hstable : (prefixWord ++ tailWord_7068914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7068914).length < 2 ^ (prefixWord ++ tailWord_7068914).sum := by decide
  have hdescent : baseEnd_7068914 < baseStart_7068914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7068914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069006 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_7069006 : Nat := 118140960795 + 7069006 * 2 ^ 59
def prefixEnd_7069006 : Nat := 4983230072969 + 3 ^ 40 * 7069006 * 2
def baseEnd_7069006 : Nat := 403310869724097190579471

theorem tailTrace_7069006 : CollatzResearch.WordTrace tailWord_7069006 prefixEnd_7069006 403310869724097190579471 := by
  unfold tailWord_7069006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32228478778525753369079359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171885220152137351301756581 32228478778525753369079359)
  ·
    refine ⟨48342718167788630053619039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32228478778525753369079359 48342718167788630053619039)
    ·
      refine ⟨72514077251682945080428559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48342718167788630053619039 72514077251682945080428559)
      ·
        refine ⟨108771115877524417620642839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72514077251682945080428559 108771115877524417620642839)
        ·
          refine ⟨163156673816286626430964259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108771115877524417620642839 163156673816286626430964259)
          ·
            refine ⟨244735010724429939646446389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163156673816286626430964259 244735010724429939646446389)
            ·
              refine ⟨22943907255415306841854349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244735010724429939646446389 22943907255415306841854349)
              ·
                refine ⟨8603965220780740065695381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22943907255415306841854349 8603965220780740065695381)
                ·
                  refine ⟨403310869724097190579471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8603965220780740065695381 403310869724097190579471)
                  ·
                    rfl

theorem cell23_7069006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_7069006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069006 prefixEnd_7069006 := by exact prefixLift 7069006
  have htrace : WordTrace (prefixWord ++ tailWord_7069006) baseStart_7069006 baseEnd_7069006 := by
    simpa [prefixWord, tailWord_7069006, baseEnd_7069006] using wordTrace_append hprefix tailTrace_7069006
  have hstable : (prefixWord ++ tailWord_7069006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069006).length < 2 ^ (prefixWord ++ tailWord_7069006).sum := by decide
  have hdescent : baseEnd_7069006 < baseStart_7069006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069014 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7069014 : Nat := 118140960795 + 7069014 * 2 ^ 59
def prefixEnd_7069014 : Nat := 4983230072969 + 3 ^ 40 * 7069014 * 2
def baseEnd_7069014 : Nat := 1209933978454036894638401

theorem tailTrace_7069014 : CollatzResearch.WordTrace tailWord_7069014 prefixEnd_7069014 1209933978454036894638401 := by
  unfold tailWord_7069014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114257625761065269932881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171885414674784696212617397 16114257625761065269932881)
  ·
    refine ⟨12085693219320798952449661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16114257625761065269932881 12085693219320798952449661)
    ·
      refine ⟨4532134957245299607168623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12085693219320798952449661 4532134957245299607168623)
      ·
        refine ⟨6798202435867949410752935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4532134957245299607168623 6798202435867949410752935)
        ·
          refine ⟨10197303653801924116129403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6798202435867949410752935 10197303653801924116129403)
          ·
            refine ⟨15295955480702886174194105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197303653801924116129403 15295955480702886174194105)
            ·
              refine ⟨11471966610527164630645579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15295955480702886174194105 11471966610527164630645579)
              ·
                refine ⟨17207949915790746945968369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11471966610527164630645579 17207949915790746945968369)
                ·
                  refine ⟨12905962436843060209476277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17207949915790746945968369 12905962436843060209476277)
                  ·
                    refine ⟨1209933978454036894638401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12905962436843060209476277 1209933978454036894638401)
                    ·
                      rfl

theorem cell23_7069014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7069014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069014 prefixEnd_7069014 := by exact prefixLift 7069014
  have htrace : WordTrace (prefixWord ++ tailWord_7069014) baseStart_7069014 baseEnd_7069014 := by
    simpa [prefixWord, tailWord_7069014, baseEnd_7069014] using wordTrace_append hprefix tailTrace_7069014
  have hstable : (prefixWord ++ tailWord_7069014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069014).length < 2 ^ (prefixWord ++ tailWord_7069014).sum := by decide
  have hdescent : baseEnd_7069014 < baseStart_7069014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069050 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3]
def baseStart_7069050 : Nat := 118140960795 + 7069050 * 2 ^ 59
def prefixEnd_7069050 : Nat := 4983230072969 + 3 ^ 40 * 7069050 * 2
def baseEnd_7069050 : Nat := 3629820420665672543065037

theorem tailTrace_7069050 : CollatzResearch.WordTrace tailWord_7069050 prefixEnd_7069050 3629820420665672543065037 := by
  unfold tailWord_7069050
  simp only [CollatzResearch.WordTrace]
  refine ⟨64457358760011655616809151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171886290026697748311491069 64457358760011655616809151)
  ·
    refine ⟨96686038140017483425213727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64457358760011655616809151 96686038140017483425213727)
    ·
      refine ⟨145029057210026225137820591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96686038140017483425213727 145029057210026225137820591)
      ·
        refine ⟨217543585815039337706730887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145029057210026225137820591 217543585815039337706730887)
        ·
          refine ⟨326315378722559006560096331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217543585815039337706730887 326315378722559006560096331)
          ·
            refine ⟨489473068083838509840144497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326315378722559006560096331 489473068083838509840144497)
            ·
              refine ⟨367104801062878882380108373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489473068083838509840144497 367104801062878882380108373)
              ·
                refine ⟨4302009387455611902891895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 367104801062878882380108373 4302009387455611902891895)
                ·
                  refine ⟨6453014081183417854337843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302009387455611902891895 6453014081183417854337843)
                  ·
                    refine ⟨9679521121775126781506765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453014081183417854337843 9679521121775126781506765)
                    ·
                      refine ⟨3629820420665672543065037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9679521121775126781506765 3629820420665672543065037)
                      ·
                        rfl

theorem cell23_7069050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_7069050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069050 prefixEnd_7069050 := by exact prefixLift 7069050
  have htrace : WordTrace (prefixWord ++ tailWord_7069050) baseStart_7069050 baseEnd_7069050 := by
    simpa [prefixWord, tailWord_7069050, baseEnd_7069050] using wordTrace_append hprefix tailTrace_7069050
  have hstable : (prefixWord ++ tailWord_7069050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069050).length < 2 ^ (prefixWord ++ tailWord_7069050).sum := by decide
  have hdescent : baseEnd_7069050 < baseStart_7069050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069090 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_7069090 : Nat := 118140960795 + 7069090 * 2 ^ 59
def prefixEnd_7069090 : Nat := 4983230072969 + 3 ^ 40 * 7069090 * 2
def baseEnd_7069090 : Nat := 3629840959891852386564853

theorem tailTrace_7069090 : CollatzResearch.WordTrace tailWord_7069090 prefixEnd_7069090 3629840959891852386564853 := by
  unfold tailWord_7069090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64457723489975427324673181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171887262639934472865795149 64457723489975427324673181)
  ·
    refine ⟨24171646308740785246752443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64457723489975427324673181 24171646308740785246752443)
    ·
      refine ⟨36257469463111177870128665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24171646308740785246752443 36257469463111177870128665)
      ·
        refine ⟨27193102097333383402596499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36257469463111177870128665 27193102097333383402596499)
        ·
          refine ⟨40789653146000075103894749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27193102097333383402596499 40789653146000075103894749)
          ·
            refine ⟨15296119929750028163960531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40789653146000075103894749 15296119929750028163960531)
            ·
              refine ⟨22944179894625042245940797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296119929750028163960531 22944179894625042245940797)
              ·
                refine ⟨8604067460484390842227799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22944179894625042245940797 8604067460484390842227799)
                ·
                  refine ⟨12906101190726586263341699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604067460484390842227799 12906101190726586263341699)
                  ·
                    refine ⟨19359151786089879395012549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12906101190726586263341699 19359151786089879395012549)
                    ·
                      refine ⟨3629840959891852386564853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19359151786089879395012549 3629840959891852386564853)
                      ·
                        rfl

theorem cell23_7069090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_7069090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069090 prefixEnd_7069090 := by exact prefixLift 7069090
  have htrace : WordTrace (prefixWord ++ tailWord_7069090) baseStart_7069090 baseEnd_7069090 := by
    simpa [prefixWord, tailWord_7069090, baseEnd_7069090] using wordTrace_append hprefix tailTrace_7069090
  have hstable : (prefixWord ++ tailWord_7069090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069090).length < 2 ^ (prefixWord ++ tailWord_7069090).sum := by decide
  have hdescent : baseEnd_7069090 < baseStart_7069090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069123 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3]
def baseStart_7069123 : Nat := 118140960795 + 7069123 * 2 ^ 59
def prefixEnd_7069123 : Nat := 4983230072969 + 3 ^ 40 * 7069123 * 2
def baseEnd_7069123 : Nat := 3629857904753450757452201

theorem tailTrace_7069123 : CollatzResearch.WordTrace tailWord_7069123 prefixEnd_7069123 3629857904753450757452201 := by
  unfold tailWord_7069123
  simp only [CollatzResearch.WordTrace]
  refine ⟨257832097568782155934644023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171888065045854770623096015 257832097568782155934644023)
  ·
    refine ⟨386748146353173233901966035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257832097568782155934644023 386748146353173233901966035)
    ·
      refine ⟨580122219529759850852949053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386748146353173233901966035 580122219529759850852949053)
      ·
        refine ⟨217545832323659944069855895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580122219529759850852949053 217545832323659944069855895)
        ·
          refine ⟨326318748485489916104783843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217545832323659944069855895 326318748485489916104783843)
          ·
            refine ⟨489478122728234874157175765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326318748485489916104783843 489478122728234874157175765)
            ·
              refine ⟨11472143501443004863058807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 489478122728234874157175765 11472143501443004863058807)
              ·
                refine ⟨17208215252164507294588211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472143501443004863058807 17208215252164507294588211)
                ·
                  refine ⟨25812322878246760941882317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17208215252164507294588211 25812322878246760941882317)
                  ·
                    refine ⟨9679621079342535353205869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25812322878246760941882317 9679621079342535353205869)
                    ·
                      refine ⟨3629857904753450757452201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9679621079342535353205869 3629857904753450757452201)
                      ·
                        rfl

theorem cell23_7069123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_7069123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069123 prefixEnd_7069123 := by exact prefixLift 7069123
  have htrace : WordTrace (prefixWord ++ tailWord_7069123) baseStart_7069123 baseEnd_7069123 := by
    simpa [prefixWord, tailWord_7069123, baseEnd_7069123] using wordTrace_append hprefix tailTrace_7069123
  have hstable : (prefixWord ++ tailWord_7069123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069123).length < 2 ^ (prefixWord ++ tailWord_7069123).sum := by decide
  have hdescent : baseEnd_7069123 < baseStart_7069123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069156 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_7069156 : Nat := 118140960795 + 7069156 * 2 ^ 59
def prefixEnd_7069156 : Nat := 4983230072969 + 3 ^ 40 * 7069156 * 2
def baseEnd_7069156 : Nat := 1209958283205016376113183

theorem tailTrace_7069156 : CollatzResearch.WordTrace tailWord_7069156 prefixEnd_7069156 1209958283205016376113183 := by
  unfold tailWord_7069156
  simp only [CollatzResearch.WordTrace]
  refine ⟨128916650588831301285297661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171888867451775068380396881 128916650588831301285297661)
  ·
    refine ⟨48343743970811737981986623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128916650588831301285297661 48343743970811737981986623)
    ·
      refine ⟨72515615956217606972979935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48343743970811737981986623 72515615956217606972979935)
      ·
        refine ⟨108773423934326410459469903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72515615956217606972979935 108773423934326410459469903)
        ·
          refine ⟨163160135901489615689204855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108773423934326410459469903 163160135901489615689204855)
          ·
            refine ⟨244740203852234423533807283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163160135901489615689204855 244740203852234423533807283)
            ·
              refine ⟨367110305778351635300710925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244740203852234423533807283 367110305778351635300710925)
              ·
                refine ⟨137666364666881863237766597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367110305778351635300710925 137666364666881863237766597)
                ·
                  refine ⟨25812443375040349357081237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137666364666881863237766597 25812443375040349357081237)
                  ·
                    refine ⟨1209958283205016376113183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25812443375040349357081237 1209958283205016376113183)
                    ·
                      rfl

theorem cell23_7069156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_7069156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069156 prefixEnd_7069156 := by exact prefixLift 7069156
  have htrace : WordTrace (prefixWord ++ tailWord_7069156) baseStart_7069156 baseEnd_7069156 := by
    simpa [prefixWord, tailWord_7069156, baseEnd_7069156] using wordTrace_append hprefix tailTrace_7069156
  have hstable : (prefixWord ++ tailWord_7069156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069156).length < 2 ^ (prefixWord ++ tailWord_7069156).sum := by decide
  have hdescent : baseEnd_7069156 < baseStart_7069156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069163 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 5, 4, 2]
def baseStart_7069163 : Nat := 118140960795 + 7069163 * 2 ^ 59
def prefixEnd_7069163 : Nat := 4983230072969 + 3 ^ 40 * 7069163 * 2
def baseEnd_7069163 : Nat := 3629878443979630600952017

theorem tailTrace_7069163 : CollatzResearch.WordTrace tailWord_7069163 prefixEnd_7069163 3629878443979630600952017 := by
  unfold tailWord_7069163
  simp only [CollatzResearch.WordTrace]
  refine ⟨257833556488637242766100143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171889037659091495177400095 257833556488637242766100143)
  ·
    refine ⟨386750334732955864149150215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257833556488637242766100143 386750334732955864149150215)
    ·
      refine ⟨580125502099433796223725323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386750334732955864149150215 580125502099433796223725323)
      ·
        refine ⟨870188253149150694335587985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580125502099433796223725323 870188253149150694335587985)
        ·
          refine ⟨652641189861863020751690989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870188253149150694335587985 652641189861863020751690989)
          ·
            refine ⟨244740446198198632781884121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652641189861863020751690989 244740446198198632781884121)
            ·
              refine ⟨183555334648648974586413091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244740446198198632781884121 183555334648648974586413091)
              ·
                refine ⟨275333001972973461879619637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183555334648648974586413091 275333001972973461879619637)
                ·
                  refine ⟨25812468934966262051214341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275333001972973461879619637 25812468934966262051214341)
                  ·
                    refine ⟨4839837925306174134602689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25812468934966262051214341 4839837925306174134602689)
                    ·
                      refine ⟨3629878443979630600952017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839837925306174134602689 3629878443979630600952017)
                      ·
                        rfl

theorem cell23_7069163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4, 2].length) (baseStart_7069163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069163 prefixEnd_7069163 := by exact prefixLift 7069163
  have htrace : WordTrace (prefixWord ++ tailWord_7069163) baseStart_7069163 baseEnd_7069163 := by
    simpa [prefixWord, tailWord_7069163, baseEnd_7069163] using wordTrace_append hprefix tailTrace_7069163
  have hstable : (prefixWord ++ tailWord_7069163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069163).length < 2 ^ (prefixWord ++ tailWord_7069163).sum := by decide
  have hdescent : baseEnd_7069163 < baseStart_7069163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069174 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_7069174 : Nat := 118140960795 + 7069174 * 2 ^ 59
def prefixEnd_7069174 : Nat := 4983230072969 + 3 ^ 40 * 7069174 * 2
def baseEnd_7069174 : Nat := 3629884092266830057914467

theorem tailTrace_7069174 : CollatzResearch.WordTrace tailWord_7069174 prefixEnd_7069174 3629884092266830057914467 := by
  unfold tailWord_7069174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114622355724836977796911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171889305127731594429833717 16114622355724836977796911)
  ·
    refine ⟨24171933533587255466695367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114622355724836977796911 24171933533587255466695367)
    ·
      refine ⟨36257900300380883200043051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24171933533587255466695367 36257900300380883200043051)
      ·
        refine ⟨54386850450571324800064577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36257900300380883200043051 54386850450571324800064577)
        ·
          refine ⟨40790137837928493600048433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54386850450571324800064577 40790137837928493600048433)
          ·
            refine ⟨30592603378446370200036325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40790137837928493600048433 30592603378446370200036325)
            ·
              refine ⟨5736113133458694412506811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30592603378446370200036325 5736113133458694412506811)
              ·
                refine ⟨8604169700188041618760217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736113133458694412506811 8604169700188041618760217)
                ·
                  refine ⟨6453127275141031214070163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604169700188041618760217 6453127275141031214070163)
                  ·
                    refine ⟨9679690912711546821105245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453127275141031214070163 9679690912711546821105245)
                    ·
                      refine ⟨3629884092266830057914467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9679690912711546821105245 3629884092266830057914467)
                      ·
                        rfl

theorem cell23_7069174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_7069174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069174 prefixEnd_7069174 := by exact prefixLift 7069174
  have htrace : WordTrace (prefixWord ++ tailWord_7069174) baseStart_7069174 baseEnd_7069174 := by
    simpa [prefixWord, tailWord_7069174, baseEnd_7069174] using wordTrace_append hprefix tailTrace_7069174
  have hstable : (prefixWord ++ tailWord_7069174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069174).length < 2 ^ (prefixWord ++ tailWord_7069174).sum := by decide
  have hdescent : baseEnd_7069174 < baseStart_7069174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069230 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7069230 : Nat := 118140960795 + 7069230 * 2 ^ 59
def prefixEnd_7069230 : Nat := 4983230072969 + 3 ^ 40 * 7069230 * 2
def baseEnd_7069230 : Nat := 3629912847183481838814209

theorem tailTrace_7069230 : CollatzResearch.WordTrace tailWord_7069230 prefixEnd_7069230 3629912847183481838814209 := by
  unfold tailWord_7069230
  simp only [CollatzResearch.WordTrace]
  refine ⟨32229500022424314151098643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171890666786263008805859429 32229500022424314151098643)
  ·
    refine ⟨48344250033636471226647965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32229500022424314151098643 48344250033636471226647965)
    ·
      refine ⟨18129093762613676709992987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48344250033636471226647965 18129093762613676709992987)
      ·
        refine ⟨27193640643920515064989481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18129093762613676709992987 27193640643920515064989481)
        ·
          refine ⟨20395230482940386298742111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27193640643920515064989481 20395230482940386298742111)
          ·
            refine ⟨30592845724410579448113167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20395230482940386298742111 30592845724410579448113167)
            ·
              refine ⟨45889268586615869172169751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30592845724410579448113167 45889268586615869172169751)
              ·
                refine ⟨68833902879923803758254627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45889268586615869172169751 68833902879923803758254627)
                ·
                  refine ⟨103250854319885705637381941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68833902879923803758254627 103250854319885705637381941)
                  ·
                    refine ⟨9679767592489284903504557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103250854319885705637381941 9679767592489284903504557)
                    ·
                      refine ⟨3629912847183481838814209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9679767592489284903504557 3629912847183481838814209)
                      ·
                        rfl

theorem cell23_7069230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7069230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069230 prefixEnd_7069230 := by exact prefixLift 7069230
  have htrace : WordTrace (prefixWord ++ tailWord_7069230) baseStart_7069230 baseEnd_7069230 := by
    simpa [prefixWord, tailWord_7069230, baseEnd_7069230] using wordTrace_append hprefix tailTrace_7069230
  have hstable : (prefixWord ++ tailWord_7069230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069230).length < 2 ^ (prefixWord ++ tailWord_7069230).sum := by decide
  have hdescent : baseEnd_7069230 < baseStart_7069230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069253 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_7069253 : Nat := 118140960795 + 7069253 * 2 ^ 59
def prefixEnd_7069253 : Nat := 4983230072969 + 3 ^ 40 * 7069253 * 2
def baseEnd_7069253 : Nat := 3629924657238535248826603

theorem tailTrace_7069253 : CollatzResearch.WordTrace tailWord_7069253 prefixEnd_7069253 3629924657238535248826603 := by
  unfold tailWord_7069253
  simp only [CollatzResearch.WordTrace]
  refine ⟨257836839058311188136876413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171891226038874125424584275 257836839058311188136876413)
  ·
    refine ⟨96688814646866695551328655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257836839058311188136876413 96688814646866695551328655)
    ·
      refine ⟨145033221970300043326992983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96688814646866695551328655 145033221970300043326992983)
      ·
        refine ⟨217549832955450064990489475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145033221970300043326992983 217549832955450064990489475)
        ·
          refine ⟨326324749433175097485734213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217549832955450064990489475 326324749433175097485734213)
          ·
            refine ⟨61185890518720330778575165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326324749433175097485734213 61185890518720330778575165)
            ·
              refine ⟨22944708944520124041965687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61185890518720330778575165 22944708944520124041965687)
              ·
                refine ⟨34417063416780186062948531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22944708944520124041965687 34417063416780186062948531)
                ·
                  refine ⟨51625595125170279094422797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34417063416780186062948531 51625595125170279094422797)
                  ·
                    refine ⟨19359598171938854660408549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51625595125170279094422797 19359598171938854660408549)
                    ·
                      refine ⟨3629924657238535248826603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19359598171938854660408549 3629924657238535248826603)
                      ·
                        rfl

theorem cell23_7069253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_7069253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069253 prefixEnd_7069253 := by exact prefixLift 7069253
  have htrace : WordTrace (prefixWord ++ tailWord_7069253) baseStart_7069253 baseEnd_7069253 := by
    simpa [prefixWord, tailWord_7069253, baseEnd_7069253] using wordTrace_append hprefix tailTrace_7069253
  have hstable : (prefixWord ++ tailWord_7069253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069253).length < 2 ^ (prefixWord ++ tailWord_7069253).sum := by decide
  have hdescent : baseEnd_7069253 < baseStart_7069253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069263 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 7, 4]
def baseStart_7069263 : Nat := 118140960795 + 7069263 * 2 ^ 59
def prefixEnd_7069263 : Nat := 4983230072969 + 3 ^ 40 * 7069263 * 2
def baseEnd_7069263 : Nat := 1209976597348360069900519

theorem tailTrace_7069263 : CollatzResearch.WordTrace tailWord_7069263 prefixEnd_7069263 1209976597348360069900519 := by
  unfold tailWord_7069263
  simp only [CollatzResearch.WordTrace]
  refine ⟨257837203788274959844740443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171891469192183306563160295 257837203788274959844740443)
  ·
    refine ⟨386755805682412439767110665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257837203788274959844740443 386755805682412439767110665)
    ·
      refine ⟨290066854261809329825332999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386755805682412439767110665 290066854261809329825332999)
      ·
        refine ⟨435100281392713994737999499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290066854261809329825332999 435100281392713994737999499)
        ·
          refine ⟨652650422089070992106999249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435100281392713994737999499 652650422089070992106999249)
          ·
            refine ⟨489487816566803244080249437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652650422089070992106999249 489487816566803244080249437)
            ·
              refine ⟨183557931212551216530093539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489487816566803244080249437 183557931212551216530093539)
              ·
                refine ⟨275336896818826824795140309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183557931212551216530093539 275336896818826824795140309)
                ·
                  refine ⟨6453208519191253706136101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 275336896818826824795140309 6453208519191253706136101)
                  ·
                    refine ⟨1209976597348360069900519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453208519191253706136101 1209976597348360069900519)
                    ·
                      rfl

theorem cell23_7069263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_7069263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069263 prefixEnd_7069263 := by exact prefixLift 7069263
  have htrace : WordTrace (prefixWord ++ tailWord_7069263) baseStart_7069263 baseEnd_7069263 := by
    simpa [prefixWord, tailWord_7069263, baseEnd_7069263] using wordTrace_append hprefix tailTrace_7069263
  have hstable : (prefixWord ++ tailWord_7069263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069263).length < 2 ^ (prefixWord ++ tailWord_7069263).sum := by decide
  have hdescent : baseEnd_7069263 < baseStart_7069263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069290 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7069290 : Nat := 118140960795 + 7069290 * 2 ^ 59
def prefixEnd_7069290 : Nat := 4983230072969 + 3 ^ 40 * 7069290 * 2
def baseEnd_7069290 : Nat := 3629943656022751604063933

theorem tailTrace_7069290 : CollatzResearch.WordTrace tailWord_7069290 prefixEnd_7069290 3629943656022751604063933 := by
  unfold tailWord_7069290
  simp only [CollatzResearch.WordTrace]
  refine ⟨64459547139794285863993331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171892125706118095637315549 64459547139794285863993331)
  ·
    refine ⟨96689320709691428795989997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64459547139794285863993331 96689320709691428795989997)
    ·
      refine ⟨36258495266134285798496249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96689320709691428795989997 36258495266134285798496249)
      ·
        refine ⟨27193871449600714348872187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36258495266134285798496249 27193871449600714348872187)
        ·
          refine ⟨40790807174401071523308281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27193871449600714348872187 40790807174401071523308281)
          ·
            refine ⟨30593105380800803642481211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40790807174401071523308281 30593105380800803642481211)
            ·
              refine ⟨45889658071201205463721817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30593105380800803642481211 45889658071201205463721817)
              ·
                refine ⟨34417243553400904097791363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45889658071201205463721817 34417243553400904097791363)
                ·
                  refine ⟨51625865330101356146687045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34417243553400904097791363 51625865330101356146687045)
                  ·
                    refine ⟨9679849749394004277503821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51625865330101356146687045 9679849749394004277503821)
                    ·
                      refine ⟨3629943656022751604063933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9679849749394004277503821 3629943656022751604063933)
                      ·
                        rfl

theorem cell23_7069290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7069290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069290 prefixEnd_7069290 := by exact prefixLift 7069290
  have htrace : WordTrace (prefixWord ++ tailWord_7069290) baseStart_7069290 baseEnd_7069290 := by
    simpa [prefixWord, tailWord_7069290, baseEnd_7069290] using wordTrace_append hprefix tailTrace_7069290
  have hstable : (prefixWord ++ tailWord_7069290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069290).length < 2 ^ (prefixWord ++ tailWord_7069290).sum := by decide
  have hdescent : baseEnd_7069290 < baseStart_7069290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069303 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_7069303 : Nat := 118140960795 + 7069303 * 2 ^ 59
def prefixEnd_7069303 : Nat := 4983230072969 + 3 ^ 40 * 7069303 * 2
def baseEnd_7069303 : Nat := 3629950331271260053201373

theorem tailTrace_7069303 : CollatzResearch.WordTrace tailWord_7069303 prefixEnd_7069303 3629950331271260053201373 := by
  unfold tailWord_7069303
  simp only [CollatzResearch.WordTrace]
  refine ⟨257838662708130046676196563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171892441805420031117464375 257838662708130046676196563)
  ·
    refine ⟨386757994062195070014294845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257838662708130046676196563 386757994062195070014294845)
    ·
      refine ⟨145034247773323151255360567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386757994062195070014294845 145034247773323151255360567)
      ·
        refine ⟨217551371659984726883040851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145034247773323151255360567 217551371659984726883040851)
        ·
          refine ⟨326327057489977090324561277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217551371659984726883040851 326327057489977090324561277)
          ·
            refine ⟨122372646558741408871710479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326327057489977090324561277 122372646558741408871710479)
            ·
              refine ⟨183558969838112113307565719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122372646558741408871710479 183558969838112113307565719)
              ·
                refine ⟨275338454757168169961348579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183558969838112113307565719 275338454757168169961348579)
                ·
                  refine ⟨413007682135752254942022869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275338454757168169961348579 413007682135752254942022869)
                  ·
                    refine ⟨9679867550056693475203661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 413007682135752254942022869 9679867550056693475203661)
                    ·
                      refine ⟨3629950331271260053201373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9679867550056693475203661 3629950331271260053201373)
                      ·
                        rfl

theorem cell23_7069303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_7069303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069303 prefixEnd_7069303 := by exact prefixLift 7069303
  have htrace : WordTrace (prefixWord ++ tailWord_7069303) baseStart_7069303 baseEnd_7069303 := by
    simpa [prefixWord, tailWord_7069303, baseEnd_7069303] using wordTrace_append hprefix tailTrace_7069303
  have hstable : (prefixWord ++ tailWord_7069303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069303).length < 2 ^ (prefixWord ++ tailWord_7069303).sum := by decide
  have hdescent : baseEnd_7069303 < baseStart_7069303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069360 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2]
def baseStart_7069360 : Nat := 118140960795 + 7069360 * 2 ^ 59
def prefixEnd_7069360 : Nat := 4983230072969 + 3 ^ 40 * 7069360 * 2
def baseEnd_7069360 : Nat := 3629979599668566330188611

theorem tailTrace_7069360 : CollatzResearch.WordTrace tailWord_7069360 prefixEnd_7069360 3629979599668566330188611 := by
  unfold tailWord_7069360
  simp only [CollatzResearch.WordTrace]
  refine ⟨128920370834461772705510767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171893827779282363607347689 128920370834461772705510767)
  ·
    refine ⟨193380556251692659058266151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128920370834461772705510767 193380556251692659058266151)
    ·
      refine ⟨290070834377538988587399227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193380556251692659058266151 290070834377538988587399227)
      ·
        refine ⟨435106251566308482881098841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290070834377538988587399227 435106251566308482881098841)
        ·
          refine ⟨326329688674731362160824131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435106251566308482881098841 326329688674731362160824131)
          ·
            refine ⟨489494533012097043241236197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326329688674731362160824131 489494533012097043241236197)
            ·
              refine ⟨91780224939768195607731787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489494533012097043241236197 91780224939768195607731787)
              ·
                refine ⟨137670337409652293411597681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91780224939768195607731787 137670337409652293411597681)
                ·
                  refine ⟨103252753057239220058698261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137670337409652293411597681 103252753057239220058698261)
                  ·
                    refine ⟨4839972799558088440251481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103252753057239220058698261 4839972799558088440251481)
                    ·
                      refine ⟨3629979599668566330188611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4839972799558088440251481 3629979599668566330188611)
                      ·
                        rfl

theorem cell23_7069360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2].length) (baseStart_7069360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069360 prefixEnd_7069360 := by exact prefixLift 7069360
  have htrace : WordTrace (prefixWord ++ tailWord_7069360) baseStart_7069360 baseEnd_7069360 := by
    simpa [prefixWord, tailWord_7069360, baseEnd_7069360] using wordTrace_append hprefix tailTrace_7069360
  have hstable : (prefixWord ++ tailWord_7069360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069360).length < 2 ^ (prefixWord ++ tailWord_7069360).sum := by decide
  have hdescent : baseEnd_7069360 < baseStart_7069360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069370 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_7069370 : Nat := 118140960795 + 7069370 * 2 ^ 59
def prefixEnd_7069370 : Nat := 4983230072969 + 3 ^ 40 * 7069370 * 2
def baseEnd_7069370 : Nat := 1209994911491703763687855

theorem tailTrace_7069370 : CollatzResearch.WordTrace tailWord_7069370 prefixEnd_7069370 1209994911491703763687855 := by
  unfold tailWord_7069370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64460276599721829279721391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171894070932591544745923709 64460276599721829279721391)
  ·
    refine ⟨96690414899582743919582087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64460276599721829279721391 96690414899582743919582087)
    ·
      refine ⟨145035622349374115879373131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96690414899582743919582087 145035622349374115879373131)
      ·
        refine ⟨217553433524061173819059697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145035622349374115879373131 217553433524061173819059697)
        ·
          refine ⟨163165075143045880364294773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217553433524061173819059697 163165075143045880364294773)
          ·
            refine ⟨15296725794660551284152635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163165075143045880364294773 15296725794660551284152635)
            ·
              refine ⟨22945088691990826926228953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296725794660551284152635 22945088691990826926228953)
              ·
                refine ⟨17208816518993120194671715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22945088691990826926228953 17208816518993120194671715)
                ·
                  refine ⟨25813224778489680292007573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17208816518993120194671715 25813224778489680292007573)
                  ·
                    refine ⟨1209994911491703763687855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25813224778489680292007573 1209994911491703763687855)
                    ·
                      rfl

theorem cell23_7069370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_7069370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069370 prefixEnd_7069370 := by exact prefixLift 7069370
  have htrace : WordTrace (prefixWord ++ tailWord_7069370) baseStart_7069370 baseEnd_7069370 := by
    simpa [prefixWord, tailWord_7069370, baseEnd_7069370] using wordTrace_append hprefix tailTrace_7069370
  have hstable : (prefixWord ++ tailWord_7069370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069370).length < 2 ^ (prefixWord ++ tailWord_7069370).sum := by decide
  have hdescent : baseEnd_7069370 < baseStart_7069370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069374 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_7069374 : Nat := 118140960795 + 7069374 * 2 ^ 59
def prefixEnd_7069374 : Nat := 4983230072969 + 3 ^ 40 * 7069374 * 2
def baseEnd_7069374 : Nat := 1209995596132576425137849

theorem tailTrace_7069374 : CollatzResearch.WordTrace tailWord_7069374 prefixEnd_7069374 1209995596132576425137849 := by
  unfold tailWord_7069374
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230156536359103225253897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171894168193915217201354117 32230156536359103225253897)
  ·
    refine ⟨24172617402269327418940423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32230156536359103225253897 24172617402269327418940423)
    ·
      refine ⟨36258926103403991128410635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24172617402269327418940423 36258926103403991128410635)
      ·
        refine ⟨54388389155105986692615953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36258926103403991128410635 54388389155105986692615953)
        ·
          refine ⟨40791291866329490019461965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54388389155105986692615953 40791291866329490019461965)
          ·
            refine ⟨15296734449873558757298237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40791291866329490019461965 15296734449873558757298237)
            ·
              refine ⟨5736275418702584533986839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15296734449873558757298237 5736275418702584533986839)
              ·
                refine ⟨8604413128053876800980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736275418702584533986839 8604413128053876800980259)
                ·
                  refine ⟨12906619692080815201470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604413128053876800980259 12906619692080815201470389)
                  ·
                    refine ⟨1209995596132576425137849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12906619692080815201470389 1209995596132576425137849)
                    ·
                      rfl

theorem cell23_7069374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_7069374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069374 prefixEnd_7069374 := by exact prefixLift 7069374
  have htrace : WordTrace (prefixWord ++ tailWord_7069374) baseStart_7069374 baseEnd_7069374 := by
    simpa [prefixWord, tailWord_7069374, baseEnd_7069374] using wordTrace_append hprefix tailTrace_7069374
  have hstable : (prefixWord ++ tailWord_7069374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069374).length < 2 ^ (prefixWord ++ tailWord_7069374).sum := by decide
  have hdescent : baseEnd_7069374 < baseStart_7069374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069390 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_7069390 : Nat := 118140960795 + 7069390 * 2 ^ 59
def prefixEnd_7069390 : Nat := 4983230072969 + 3 ^ 40 * 7069390 * 2
def baseEnd_7069390 : Nat := 3629995004088201212813473

theorem tailTrace_7069390 : CollatzResearch.WordTrace tailWord_7069390 prefixEnd_7069390 3629995004088201212813473 := by
  unfold tailWord_7069390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230229482351857566826703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171894557239209907023075749 32230229482351857566826703)
  ·
    refine ⟨48345344223527786350240055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32230229482351857566826703 48345344223527786350240055)
    ·
      refine ⟨72518016335291679525360083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48345344223527786350240055 72518016335291679525360083)
      ·
        refine ⟨108777024502937519288040125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72518016335291679525360083 108777024502937519288040125)
        ·
          refine ⟨40791384188601569733015047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108777024502937519288040125 40791384188601569733015047)
          ·
            refine ⟨61187076282902354599522571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40791384188601569733015047 61187076282902354599522571)
            ·
              refine ⟨91780614424353531899283857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61187076282902354599522571 91780614424353531899283857)
              ·
                refine ⟨68835460818265148924462893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91780614424353531899283857 68835460818265148924462893)
                ·
                  refine ⟨25813297806849430846673585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68835460818265148924462893 25813297806849430846673585)
                  ·
                    refine ⟨19359973355137073135005189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25813297806849430846673585 19359973355137073135005189)
                    ·
                      refine ⟨3629995004088201212813473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19359973355137073135005189 3629995004088201212813473)
                      ·
                        rfl

theorem cell23_7069390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_7069390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069390 prefixEnd_7069390 := by exact prefixLift 7069390
  have htrace : WordTrace (prefixWord ++ tailWord_7069390) baseStart_7069390 baseEnd_7069390 := by
    simpa [prefixWord, tailWord_7069390, baseEnd_7069390] using wordTrace_append hprefix tailTrace_7069390
  have hstable : (prefixWord ++ tailWord_7069390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069390).length < 2 ^ (prefixWord ++ tailWord_7069390).sum := by decide
  have hdescent : baseEnd_7069390 < baseStart_7069390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069404 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7069404 : Nat := 118140960795 + 7069404 * 2 ^ 59
def prefixEnd_7069404 : Nat := 4983230072969 + 3 ^ 40 * 7069404 * 2
def baseEnd_7069404 : Nat := 1210000730939121386012803

theorem tailTrace_7069404 : CollatzResearch.WordTrace tailWord_7069404 prefixEnd_7069404 1210000730939121386012803 := by
  unfold tailWord_7069404
  simp only [CollatzResearch.WordTrace]
  refine ⟨128921173240382070462811633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171894897653842760617082177 128921173240382070462811633)
  ·
    refine ⟨96690879930286552847108725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128921173240382070462811633 96690879930286552847108725)
    ·
      refine ⟨9064769993464364329416443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96690879930286552847108725 9064769993464364329416443)
      ·
        refine ⟨13597154990196546494124665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064769993464364329416443 13597154990196546494124665)
        ·
          refine ⟨10197866242647409870593499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597154990196546494124665 10197866242647409870593499)
          ·
            refine ⟨15296799363971114805890249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197866242647409870593499 15296799363971114805890249)
            ·
              refine ⟨11472599522978336104417687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15296799363971114805890249 11472599522978336104417687)
              ·
                refine ⟨17208899284467504156626531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472599522978336104417687 17208899284467504156626531)
                ·
                  refine ⟨25813348926701256234939797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17208899284467504156626531 25813348926701256234939797)
                  ·
                    refine ⟨1210000730939121386012803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25813348926701256234939797 1210000730939121386012803)
                    ·
                      rfl

theorem cell23_7069404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7069404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069404 prefixEnd_7069404 := by exact prefixLift 7069404
  have htrace : WordTrace (prefixWord ++ tailWord_7069404) baseStart_7069404 baseEnd_7069404 := by
    simpa [prefixWord, tailWord_7069404, baseEnd_7069404] using wordTrace_append hprefix tailTrace_7069404
  have hstable : (prefixWord ++ tailWord_7069404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069404).length < 2 ^ (prefixWord ++ tailWord_7069404).sum := by decide
  have hdescent : baseEnd_7069404 < baseStart_7069404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069411 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7069411 : Nat := 118140960795 + 7069411 * 2 ^ 59
def prefixEnd_7069411 : Nat := 4983230072969 + 3 ^ 40 * 7069411 * 2
def baseEnd_7069411 : Nat := 3630005787181945630650877

theorem tailTrace_7069411 : CollatzResearch.WordTrace tailWord_7069411 prefixEnd_7069411 3630005787181945630650877 := by
  unfold tailWord_7069411
  simp only [CollatzResearch.WordTrace]
  refine ⟨257842601791738781121128087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171895067861159187414085391 257842601791738781121128087)
  ·
    refine ⟨386763902687608171681692131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257842601791738781121128087 386763902687608171681692131)
    ·
      refine ⟨580145854031412257522538197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386763902687608171681692131 580145854031412257522538197)
      ·
        refine ⟨13597168453861224785684489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 580145854031412257522538197 13597168453861224785684489)
        ·
          refine ⟨10197876340395918589263367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597168453861224785684489 10197876340395918589263367)
          ·
            refine ⟨15296814510593877883895051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197876340395918589263367 15296814510593877883895051)
            ·
              refine ⟨22945221765890816825842577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296814510593877883895051 22945221765890816825842577)
              ·
                refine ⟨17208916324418112619381933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22945221765890816825842577 17208916324418112619381933)
                ·
                  refine ⟨6453343621656792232268225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17208916324418112619381933 6453343621656792232268225)
                  ·
                    refine ⟨4840007716242594174201169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453343621656792232268225 4840007716242594174201169)
                    ·
                      refine ⟨3630005787181945630650877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840007716242594174201169 3630005787181945630650877)
                      ·
                        rfl

theorem cell23_7069411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7069411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069411 prefixEnd_7069411 := by exact prefixLift 7069411
  have htrace : WordTrace (prefixWord ++ tailWord_7069411) baseStart_7069411 baseEnd_7069411 := by
    simpa [prefixWord, tailWord_7069411, baseEnd_7069411] using wordTrace_append hprefix tailTrace_7069411
  have hstable : (prefixWord ++ tailWord_7069411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069411).length < 2 ^ (prefixWord ++ tailWord_7069411).sum := by decide
  have hdescent : baseEnd_7069411 < baseStart_7069411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069428 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7069428 : Nat := 118140960795 + 7069428 * 2 ^ 59
def prefixEnd_7069428 : Nat := 4983230072969 + 3 ^ 40 * 7069428 * 2
def baseEnd_7069428 : Nat := 3630014516353072064138299

theorem tailTrace_7069428 : CollatzResearch.WordTrace tailWord_7069428 prefixEnd_7069428 3630014516353072064138299 := by
  unfold tailWord_7069428
  simp only [CollatzResearch.WordTrace]
  refine ⟨128921610916338596512248469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171895481221784795349664625 128921610916338596512248469)
  ·
    refine ⟨6043200511703371711511647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128921610916338596512248469 6043200511703371711511647)
    ·
      refine ⟨9064800767555057567267471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043200511703371711511647 9064800767555057567267471)
      ·
        refine ⟨13597201151332586350901207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064800767555057567267471 13597201151332586350901207)
        ·
          refine ⟨20395801726998879526351811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13597201151332586350901207 20395801726998879526351811)
          ·
            refine ⟨30593702590498319289527717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20395801726998879526351811 30593702590498319289527717)
            ·
              refine ⟨5736319235718434866786447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30593702590498319289527717 5736319235718434866786447)
              ·
                refine ⟨8604478853577652300179671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736319235718434866786447 8604478853577652300179671)
                ·
                  refine ⟨12906718280366478450269507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604478853577652300179671 12906718280366478450269507)
                  ·
                    refine ⟨19360077420549717675404261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12906718280366478450269507 19360077420549717675404261)
                    ·
                      refine ⟨3630014516353072064138299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19360077420549717675404261 3630014516353072064138299)
                      ·
                        rfl

theorem cell23_7069428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7069428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069428 prefixEnd_7069428 := by exact prefixLift 7069428
  have htrace : WordTrace (prefixWord ++ tailWord_7069428) baseStart_7069428 baseEnd_7069428 := by
    simpa [prefixWord, tailWord_7069428, baseEnd_7069428] using wordTrace_append hprefix tailTrace_7069428
  have hstable : (prefixWord ++ tailWord_7069428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069428).length < 2 ^ (prefixWord ++ tailWord_7069428).sum := by decide
  have hdescent : baseEnd_7069428 < baseStart_7069428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069437 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_7069437 : Nat := 118140960795 + 7069437 * 2 ^ 59
def prefixEnd_7069437 : Nat := 4983230072969 + 3 ^ 40 * 7069437 * 2
def baseEnd_7069437 : Nat := 3630019137678962528925757

theorem tailTrace_7069437 : CollatzResearch.WordTrace tailWord_7069437 prefixEnd_7069437 3630019137678962528925757 := by
  unfold tailWord_7069437
  simp only [CollatzResearch.WordTrace]
  refine ⟨257843550089644587561574565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171895700059763058374383043 257843550089644587561574565)
  ·
    refine ⟨48345665641808360167795231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257843550089644587561574565 48345665641808360167795231)
    ·
      refine ⟨72518498462712540251692847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48345665641808360167795231 72518498462712540251692847)
      ·
        refine ⟨108777747694068810377539271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72518498462712540251692847 108777747694068810377539271)
        ·
          refine ⟨163166621541103215566308907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108777747694068810377539271 163166621541103215566308907)
          ·
            refine ⟨244749932311654823349463361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163166621541103215566308907 244749932311654823349463361)
            ·
              refine ⟨183562449233741117512097521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244749932311654823349463361 183562449233741117512097521)
              ·
                refine ⟨137671836925305838134073141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183562449233741117512097521 137671836925305838134073141)
                ·
                  refine ⟨12906734711747422325069357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137671836925305838134073141 12906734711747422325069357)
                  ·
                    refine ⟨4840025516905283371901009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12906734711747422325069357 4840025516905283371901009)
                    ·
                      refine ⟨3630019137678962528925757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840025516905283371901009 3630019137678962528925757)
                      ·
                        rfl

theorem cell23_7069437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_7069437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069437 prefixEnd_7069437 := by exact prefixLift 7069437
  have htrace : WordTrace (prefixWord ++ tailWord_7069437) baseStart_7069437 baseEnd_7069437 := by
    simpa [prefixWord, tailWord_7069437, baseEnd_7069437] using wordTrace_append hprefix tailTrace_7069437
  have hstable : (prefixWord ++ tailWord_7069437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069437).length < 2 ^ (prefixWord ++ tailWord_7069437).sum := by decide
  have hdescent : baseEnd_7069437 < baseStart_7069437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069438 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_7069438 : Nat := 118140960795 + 7069438 * 2 ^ 59
def prefixEnd_7069438 : Nat := 4983230072969 + 3 ^ 40 * 7069438 * 2
def baseEnd_7069438 : Nat := 1210006550386539008337751

theorem tailTrace_7069438 : CollatzResearch.WordTrace tailWord_7069438 prefixEnd_7069438 1210006550386539008337751 := by
  unfold tailWord_7069438
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230448320330120591545121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171895724375093976488240645 32230448320330120591545121)
  ·
    refine ⟨24172836240247590443658841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32230448320330120591545121 24172836240247590443658841)
    ·
      refine ⟨18129627180185692832744131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24172836240247590443658841 18129627180185692832744131)
      ·
        refine ⟨27194440770278539249116197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18129627180185692832744131 27194440770278539249116197)
        ·
          refine ⟨5098957644427226109209287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27194440770278539249116197 5098957644427226109209287)
          ·
            refine ⟨7648436466640839163813931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098957644427226109209287 7648436466640839163813931)
            ·
              refine ⟨11472654699961258745720897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648436466640839163813931 11472654699961258745720897)
              ·
                refine ⟨8604491024970944059290673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11472654699961258745720897 8604491024970944059290673)
                ·
                  refine ⟨6453368268728208044468005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604491024970944059290673 6453368268728208044468005)
                  ·
                    refine ⟨1210006550386539008337751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453368268728208044468005 1210006550386539008337751)
                    ·
                      rfl

theorem cell23_7069438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_7069438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069438 prefixEnd_7069438 := by exact prefixLift 7069438
  have htrace : WordTrace (prefixWord ++ tailWord_7069438) baseStart_7069438 baseEnd_7069438 := by
    simpa [prefixWord, tailWord_7069438, baseEnd_7069438] using wordTrace_append hprefix tailTrace_7069438
  have hstable : (prefixWord ++ tailWord_7069438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069438).length < 2 ^ (prefixWord ++ tailWord_7069438).sum := by decide
  have hdescent : baseEnd_7069438 < baseStart_7069438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069444 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7069444 : Nat := 118140960795 + 7069444 * 2 ^ 59
def prefixEnd_7069444 : Nat := 4983230072969 + 3 ^ 40 * 7069444 * 2
def baseEnd_7069444 : Nat := 3630022732043544001538225

theorem tailTrace_7069444 : CollatzResearch.WordTrace tailWord_7069444 prefixEnd_7069444 3630022732043544001538225 := by
  unfold tailWord_7069444
  simp only [CollatzResearch.WordTrace]
  refine ⟨128921902700309613878539693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171895870267079485171386257 128921902700309613878539693)
  ·
    refine ⟨48345713512616105204452385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128921902700309613878539693 48345713512616105204452385)
    ·
      refine ⟨36259285134462078903339289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48345713512616105204452385 36259285134462078903339289)
      ·
        refine ⟨27194463850846559177504467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36259285134462078903339289 27194463850846559177504467)
        ·
          refine ⟨40791695776269838766256701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27194463850846559177504467 40791695776269838766256701)
          ·
            refine ⟨15296885916101189537346263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40791695776269838766256701 15296885916101189537346263)
            ·
              refine ⟨22945328874151784306019395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296885916101189537346263 22945328874151784306019395)
              ·
                refine ⟨34417993311227676459029093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22945328874151784306019395 34417993311227676459029093)
                ·
                  refine ⟨6453373745855189336067955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34417993311227676459029093 6453373745855189336067955)
                  ·
                    refine ⟨9680060618782784004101933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453373745855189336067955 9680060618782784004101933)
                    ·
                      refine ⟨3630022732043544001538225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680060618782784004101933 3630022732043544001538225)
                      ·
                        rfl

theorem cell23_7069444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7069444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069444 prefixEnd_7069444 := by exact prefixLift 7069444
  have htrace : WordTrace (prefixWord ++ tailWord_7069444) baseStart_7069444 baseEnd_7069444 := by
    simpa [prefixWord, tailWord_7069444, baseEnd_7069444] using wordTrace_append hprefix tailTrace_7069444
  have hstable : (prefixWord ++ tailWord_7069444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069444).length < 2 ^ (prefixWord ++ tailWord_7069444).sum := by decide
  have hdescent : baseEnd_7069444 < baseStart_7069444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069461 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_7069461 : Nat := 118140960795 + 7069461 * 2 ^ 59
def prefixEnd_7069461 : Nat := 4983230072969 + 3 ^ 40 * 7069461 * 2
def baseEnd_7069461 : Nat := 3630031461214670435025647

theorem tailTrace_7069461 : CollatzResearch.WordTrace tailWord_7069461 prefixEnd_7069461 3630031461214670435025647 := by
  unfold tailWord_7069461
  simp only [CollatzResearch.WordTrace]
  refine ⟨257844425441557639660448237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171896283627705093106965491 257844425441557639660448237)
  ·
    refine ⟨96691659540584114872668089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257844425441557639660448237 96691659540584114872668089)
    ·
      refine ⟨72518744655438086154501067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96691659540584114872668089 72518744655438086154501067)
      ·
        refine ⟨108778116983157129231751601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72518744655438086154501067 108778116983157129231751601)
        ·
          refine ⟨81583587737367846923813701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108778116983157129231751601 81583587737367846923813701)
          ·
            refine ⟨15296922700756471298215069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81583587737367846923813701 15296922700756471298215069)
            ·
              refine ⟨5736346012783676736830651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15296922700756471298215069 5736346012783676736830651)
              ·
                refine ⟨8604519019175515105245977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736346012783676736830651 8604519019175515105245977)
                ·
                  refine ⟨6453389264381636328934483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604519019175515105245977 6453389264381636328934483)
                  ·
                    refine ⟨9680083896572454493401725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453389264381636328934483 9680083896572454493401725)
                    ·
                      refine ⟨3630031461214670435025647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680083896572454493401725 3630031461214670435025647)
                      ·
                        rfl

theorem cell23_7069461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_7069461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069461 prefixEnd_7069461 := by exact prefixLift 7069461
  have htrace : WordTrace (prefixWord ++ tailWord_7069461) baseStart_7069461 baseEnd_7069461 := by
    simpa [prefixWord, tailWord_7069461, baseEnd_7069461] using wordTrace_append hprefix tailTrace_7069461
  have hstable : (prefixWord ++ tailWord_7069461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069461).length < 2 ^ (prefixWord ++ tailWord_7069461).sum := by decide
  have hdescent : baseEnd_7069461 < baseStart_7069461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069484 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_7069484 : Nat := 118140960795 + 7069484 * 2 ^ 59
def prefixEnd_7069484 : Nat := 4983230072969 + 3 ^ 40 * 7069484 * 2
def baseEnd_7069484 : Nat := 3630043271269723845038041

theorem tailTrace_7069484 : CollatzResearch.WordTrace tailWord_7069484 prefixEnd_7069484 3630043271269723845038041 := by
  unfold tailWord_7069484
  simp only [CollatzResearch.WordTrace]
  refine ⟨128922632160237157294267753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171896842880316209725690337 128922632160237157294267753)
  ·
    refine ⟨96691974120177867970700815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128922632160237157294267753 96691974120177867970700815)
    ·
      refine ⟨145037961180266801956051223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96691974120177867970700815 145037961180266801956051223)
      ·
        refine ⟨217556941770400202934076835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145037961180266801956051223 217556941770400202934076835)
        ·
          refine ⟨326335412655600304401115253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217556941770400202934076835 326335412655600304401115253)
          ·
            refine ⟨30593944936462528537604555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326335412655600304401115253 30593944936462528537604555)
            ·
              refine ⟨45890917404693792806406833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30593944936462528537604555 45890917404693792806406833)
              ·
                refine ⟨34418188053520344604805125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45890917404693792806406833 34418188053520344604805125)
                ·
                  refine ⟨6453410260035064613400961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34418188053520344604805125 6453410260035064613400961)
                  ·
                    refine ⟨4840057695026298460050721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453410260035064613400961 4840057695026298460050721)
                    ·
                      refine ⟨3630043271269723845038041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840057695026298460050721 3630043271269723845038041)
                      ·
                        rfl

theorem cell23_7069484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_7069484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069484 prefixEnd_7069484 := by exact prefixLift 7069484
  have htrace : WordTrace (prefixWord ++ tailWord_7069484) baseStart_7069484 baseEnd_7069484 := by
    simpa [prefixWord, tailWord_7069484, baseEnd_7069484] using wordTrace_append hprefix tailTrace_7069484
  have hstable : (prefixWord ++ tailWord_7069484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069484).length < 2 ^ (prefixWord ++ tailWord_7069484).sum := by decide
  have hdescent : baseEnd_7069484 < baseStart_7069484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069501 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7069501 : Nat := 118140960795 + 7069501 * 2 ^ 59
def prefixEnd_7069501 : Nat := 4983230072969 + 3 ^ 40 * 7069501 * 2
def baseEnd_7069501 : Nat := 3630052000440850278525463

theorem tailTrace_7069501 : CollatzResearch.WordTrace tailWord_7069501 prefixEnd_7069501 3630052000440850278525463 := by
  unfold tailWord_7069501
  simp only [CollatzResearch.WordTrace]
  refine ⟨257845884361412726491904357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171897256240941817661269571 257845884361412726491904357)
  ·
    refine ⟨48346103317764886217232067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257845884361412726491904357 48346103317764886217232067)
    ·
      refine ⟨72519154976647329325848101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48346103317764886217232067 72519154976647329325848101)
      ·
        refine ⟨13597341558121374248596519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72519154976647329325848101 13597341558121374248596519)
        ·
          refine ⟨20396012337182061372894779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13597341558121374248596519 20396012337182061372894779)
          ·
            refine ⟨30594018505773092059342169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20396012337182061372894779 30594018505773092059342169)
            ·
              refine ⟨22945513879329819044506627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30594018505773092059342169 22945513879329819044506627)
              ·
                refine ⟨34418270818994728566759941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22945513879329819044506627 34418270818994728566759941)
                ·
                  refine ⟨6453425778561511606267489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34418270818994728566759941 6453425778561511606267489)
                  ·
                    refine ⟨4840069333921133704700617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453425778561511606267489 4840069333921133704700617)
                    ·
                      refine ⟨3630052000440850278525463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840069333921133704700617 3630052000440850278525463)
                      ·
                        rfl

theorem cell23_7069501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7069501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069501 prefixEnd_7069501 := by exact prefixLift 7069501
  have htrace : WordTrace (prefixWord ++ tailWord_7069501) baseStart_7069501 baseEnd_7069501 := by
    simpa [prefixWord, tailWord_7069501, baseEnd_7069501] using wordTrace_append hprefix tailTrace_7069501
  have hstable : (prefixWord ++ tailWord_7069501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069501).length < 2 ^ (prefixWord ++ tailWord_7069501).sum := by decide
  have hdescent : baseEnd_7069501 < baseStart_7069501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069507 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 7]
def baseStart_7069507 : Nat := 118140960795 + 7069507 * 2 ^ 59
def prefixEnd_7069507 : Nat := 4983230072969 + 3 ^ 40 * 7069507 * 2
def baseEnd_7069507 : Nat := 403339453480530806116715

theorem tailTrace_7069507 : CollatzResearch.WordTrace tailWord_7069507 prefixEnd_7069507 403339453480530806116715 := by
  unfold tailWord_7069507
  simp only [CollatzResearch.WordTrace]
  refine ⟨257846103199390989516622775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171897402132927326344415183 257846103199390989516622775)
  ·
    refine ⟨386769154799086484274934163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257846103199390989516622775 386769154799086484274934163)
    ·
      refine ⟨580153732198629726412401245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386769154799086484274934163 580153732198629726412401245)
      ·
        refine ⟨217557649574486147404650467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580153732198629726412401245 217557649574486147404650467)
        ·
          refine ⟨326336474361729221106975701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217557649574486147404650467 326336474361729221106975701)
          ·
            refine ⟨7648511117853028619694743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 326336474361729221106975701 7648511117853028619694743)
            ·
              refine ⟨11472766676779542929542115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648511117853028619694743 11472766676779542929542115)
              ·
                refine ⟨17209150015169314394313173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472766676779542929542115 17209150015169314394313173)
                ·
                  refine ⟨403339453480530806116715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17209150015169314394313173 403339453480530806116715)
                  ·
                    rfl

theorem cell23_7069507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 7].length) (baseStart_7069507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069507 prefixEnd_7069507 := by exact prefixLift 7069507
  have htrace : WordTrace (prefixWord ++ tailWord_7069507) baseStart_7069507 baseEnd_7069507 := by
    simpa [prefixWord, tailWord_7069507, baseEnd_7069507] using wordTrace_append hprefix tailTrace_7069507
  have hstable : (prefixWord ++ tailWord_7069507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069507).length < 2 ^ (prefixWord ++ tailWord_7069507).sum := by decide
  have hdescent : baseEnd_7069507 < baseStart_7069507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069520 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_7069520 : Nat := 118140960795 + 7069520 * 2 ^ 59
def prefixEnd_7069520 : Nat := 4983230072969 + 3 ^ 40 * 7069520 * 2
def baseEnd_7069520 : Nat := 1210020585524428568062625

theorem tailTrace_7069520 : CollatzResearch.WordTrace tailWord_7069520 prefixEnd_7069520 1210020585524428568062625 := by
  unfold tailWord_7069520
  simp only [CollatzResearch.WordTrace]
  refine ⟨128923288674171946368423007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171897718232229261824564009 128923288674171946368423007)
  ·
    refine ⟨193384933011257919552634511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128923288674171946368423007 193384933011257919552634511)
    ·
      refine ⟨290077399516886879328951767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193384933011257919552634511 290077399516886879328951767)
      ·
        refine ⟨435116099275330318993427651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290077399516886879328951767 435116099275330318993427651)
        ·
          refine ⟨652674148912995478490141477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435116099275330318993427651 652674148912995478490141477)
          ·
            refine ⟨122376402921186652216901527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 652674148912995478490141477 122376402921186652216901527)
            ·
              refine ⟨183564604381779978325352291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122376402921186652216901527 183564604381779978325352291)
              ·
                refine ⟨275346906572669967488028437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183564604381779978325352291 275346906572669967488028437)
                ·
                  refine ⟨12906886245593904726001333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 275346906572669967488028437 12906886245593904726001333)
                  ·
                    refine ⟨1210020585524428568062625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12906886245593904726001333 1210020585524428568062625)
                    ·
                      rfl

theorem cell23_7069520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_7069520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069520 prefixEnd_7069520 := by exact prefixLift 7069520
  have htrace : WordTrace (prefixWord ++ tailWord_7069520) baseStart_7069520 baseEnd_7069520 := by
    simpa [prefixWord, tailWord_7069520, baseEnd_7069520] using wordTrace_append hprefix tailTrace_7069520
  have hstable : (prefixWord ++ tailWord_7069520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069520).length < 2 ^ (prefixWord ++ tailWord_7069520).sum := by decide
  have hdescent : baseEnd_7069520 < baseStart_7069520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069530 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_7069530 : Nat := 118140960795 + 7069530 * 2 ^ 59
def prefixEnd_7069530 : Nat := 4983230072969 + 3 ^ 40 * 7069530 * 2
def baseEnd_7069530 : Nat := 3630066891379830665062829

theorem tailTrace_7069530 : CollatzResearch.WordTrace tailWord_7069530 prefixEnd_7069530 3630066891379830665062829 := by
  unfold tailWord_7069530
  simp only [CollatzResearch.WordTrace]
  refine ⟨64461735519576916111177511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171897961385538442963140029 64461735519576916111177511)
  ·
    refine ⟨96692603279365374166766267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64461735519576916111177511 96692603279365374166766267)
    ·
      refine ⟨145038904919048061250149401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96692603279365374166766267 145038904919048061250149401)
      ·
        refine ⟨108779178689286045937612051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145038904919048061250149401 108779178689286045937612051)
        ·
          refine ⟨163168768033929068906418077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108779178689286045937612051 163168768033929068906418077)
          ·
            refine ⟨61188288012723400839906779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163168768033929068906418077 61188288012723400839906779)
            ·
              refine ⟨91782432019085101259860169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61188288012723400839906779 91782432019085101259860169)
              ·
                refine ⟨68836824014313825944895127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91782432019085101259860169 68836824014313825944895127)
                ·
                  refine ⟨103255236021470738917342691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68836824014313825944895127 103255236021470738917342691)
                  ·
                    refine ⟨154882854032206108376014037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103255236021470738917342691 154882854032206108376014037)
                    ·
                      refine ⟨3630066891379830665062829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154882854032206108376014037 3630066891379830665062829)
                      ·
                        rfl

theorem cell23_7069530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_7069530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069530 prefixEnd_7069530 := by exact prefixLift 7069530
  have htrace : WordTrace (prefixWord ++ tailWord_7069530) baseStart_7069530 baseEnd_7069530 := by
    simpa [prefixWord, tailWord_7069530, baseEnd_7069530] using wordTrace_append hprefix tailTrace_7069530
  have hstable : (prefixWord ++ tailWord_7069530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069530).length < 2 ^ (prefixWord ++ tailWord_7069530).sum := by decide
  have hdescent : baseEnd_7069530 < baseStart_7069530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069537 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_7069537 : Nat := 118140960795 + 7069537 * 2 ^ 59
def prefixEnd_7069537 : Nat := 4983230072969 + 3 ^ 40 * 7069537 * 2
def baseEnd_7069537 : Nat := 1210023495248137379225099

theorem tailTrace_7069537 : CollatzResearch.WordTrace tailWord_7069537 prefixEnd_7069537 1210023495248137379225099 := by
  unfold tailWord_7069537
  simp only [CollatzResearch.WordTrace]
  refine ⟨257847197389282304640214865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171898131592854869760143243 257847197389282304640214865)
  ·
    refine ⟨193385398041961728480161149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257847197389282304640214865 193385398041961728480161149)
    ·
      refine ⟨72519524265735648180060431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193385398041961728480161149 72519524265735648180060431)
      ·
        refine ⟨108779286398603472270090647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72519524265735648180060431 108779286398603472270090647)
        ·
          refine ⟨163168929597905208405135971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108779286398603472270090647 163168929597905208405135971)
          ·
            refine ⟨244753394396857812607703957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163168929597905208405135971 244753394396857812607703957)
            ·
              refine ⟨11472815362352709965986123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244753394396857812607703957 11472815362352709965986123)
              ·
                refine ⟨17209223043529064948979185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472815362352709965986123 17209223043529064948979185)
                ·
                  refine ⟨12906917282646798711734389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17209223043529064948979185 12906917282646798711734389)
                  ·
                    refine ⟨1210023495248137379225099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12906917282646798711734389 1210023495248137379225099)
                    ·
                      rfl

theorem cell23_7069537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_7069537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069537 prefixEnd_7069537 := by exact prefixLift 7069537
  have htrace : WordTrace (prefixWord ++ tailWord_7069537) baseStart_7069537 baseEnd_7069537 := by
    simpa [prefixWord, tailWord_7069537, baseEnd_7069537] using wordTrace_append hprefix tailTrace_7069537
  have hstable : (prefixWord ++ tailWord_7069537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069537).length < 2 ^ (prefixWord ++ tailWord_7069537).sum := by decide
  have hdescent : baseEnd_7069537 < baseStart_7069537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069567 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 3, 4]
def baseStart_7069567 : Nat := 118140960795 + 7069567 * 2 ^ 59
def prefixEnd_7069567 : Nat := 4983230072969 + 3 ^ 40 * 7069567 * 2
def baseEnd_7069567 : Nat := 1210028630054682340100053

theorem tailTrace_7069567 : CollatzResearch.WordTrace tailWord_7069567 prefixEnd_7069567 1210028630054682340100053 := by
  unfold tailWord_7069567
  simp only [CollatzResearch.WordTrace]
  refine ⟨257848291579173619763806955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171898861052782413175871303 257848291579173619763806955)
  ·
    refine ⟨386772437368760429645710433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257848291579173619763806955 386772437368760429645710433)
    ·
      refine ⟨290079328026570322234282825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386772437368760429645710433 290079328026570322234282825)
      ·
        refine ⟨217559496019927741675712119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290079328026570322234282825 217559496019927741675712119)
        ·
          refine ⟨326339244029891612513568179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217559496019927741675712119 326339244029891612513568179)
          ·
            refine ⟨489508866044837418770352269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326339244029891612513568179 489508866044837418770352269)
            ·
              refine ⟨183565824766814032038882101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489508866044837418770352269 183565824766814032038882101)
              ·
                refine ⟨17209296071888815503645197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183565824766814032038882101 17209296071888815503645197)
                ·
                  refine ⟨6453486026958305813866949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17209296071888815503645197 6453486026958305813866949)
                  ·
                    refine ⟨1210028630054682340100053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453486026958305813866949 1210028630054682340100053)
                    ·
                      rfl

theorem cell23_7069567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_7069567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069567 prefixEnd_7069567 := by exact prefixLift 7069567
  have htrace : WordTrace (prefixWord ++ tailWord_7069567) baseStart_7069567 baseEnd_7069567 := by
    simpa [prefixWord, tailWord_7069567, baseEnd_7069567] using wordTrace_append hprefix tailTrace_7069567
  have hstable : (prefixWord ++ tailWord_7069567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069567).length < 2 ^ (prefixWord ++ tailWord_7069567).sum := by decide
  have hdescent : baseEnd_7069567 < baseStart_7069567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069577 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_7069577 : Nat := 118140960795 + 7069577 * 2 ^ 59
def prefixEnd_7069577 : Nat := 4983230072969 + 3 ^ 40 * 7069577 * 2
def baseEnd_7069577 : Nat := 3630091024970591981175113

theorem tailTrace_7069577 : CollatzResearch.WordTrace tailWord_7069577 prefixEnd_7069577 3630091024970591981175113 := by
  unfold tailWord_7069577
  simp only [CollatzResearch.WordTrace]
  refine ⟨257848656309137391471670985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171899104206091594314447323 257848656309137391471670985)
  ·
    refine ⟨193386492231853043603753239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257848656309137391471670985 193386492231853043603753239)
    ·
      refine ⟨290079738347779565405629859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193386492231853043603753239 290079738347779565405629859)
      ·
        refine ⟨435119607521669348108444789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290079738347779565405629859 435119607521669348108444789)
        ·
          refine ⟨40792463205156501385166699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435119607521669348108444789 40792463205156501385166699)
          ·
            refine ⟨61188694807734752077750049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40792463205156501385166699 61188694807734752077750049)
            ·
              refine ⟨45891521105801064058312537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61188694807734752077750049 45891521105801064058312537)
              ·
                refine ⟨34418640829350798043734403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45891521105801064058312537 34418640829350798043734403)
                ·
                  refine ⟨51627961244026197065601605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34418640829350798043734403 51627961244026197065601605)
                  ·
                    refine ⟨9680242733254911949800301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51627961244026197065601605 9680242733254911949800301)
                    ·
                      refine ⟨3630091024970591981175113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680242733254911949800301 3630091024970591981175113)
                      ·
                        rfl

theorem cell23_7069577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_7069577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069577 prefixEnd_7069577 := by exact prefixLift 7069577
  have htrace : WordTrace (prefixWord ++ tailWord_7069577) baseStart_7069577 baseEnd_7069577 := by
    simpa [prefixWord, tailWord_7069577, baseEnd_7069577] using wordTrace_append hprefix tailTrace_7069577
  have hstable : (prefixWord ++ tailWord_7069577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069577).length < 2 ^ (prefixWord ++ tailWord_7069577).sum := by decide
  have hdescent : baseEnd_7069577 < baseStart_7069577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069580 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 10]
def baseStart_7069580 : Nat := 118140960795 + 7069580 * 2 ^ 59
def prefixEnd_7069580 : Nat := 4983230072969 + 3 ^ 40 * 7069580 * 2
def baseEnd_7069580 : Nat := 403343618379172829937511

theorem tailTrace_7069580 : CollatzResearch.WordTrace tailWord_7069580 prefixEnd_7069580 403343618379172829937511 := by
  unfold tailWord_7069580
  simp only [CollatzResearch.WordTrace]
  refine ⟨128924382864063261492015097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171899177152084348656020129 128924382864063261492015097)
  ·
    refine ⟨96693287148047446119011323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128924382864063261492015097 96693287148047446119011323)
    ·
      refine ⟨145039930722071169178516985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96693287148047446119011323 145039930722071169178516985)
      ·
        refine ⟨108779948041553376883887739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145039930722071169178516985 108779948041553376883887739)
        ·
          refine ⟨163169922062330065325831609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108779948041553376883887739 163169922062330065325831609)
          ·
            refine ⟨122377441546747548994373707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163169922062330065325831609 122377441546747548994373707)
            ·
              refine ⟨183566162320121323491560561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122377441546747548994373707 183566162320121323491560561)
              ·
                refine ⟨137674621740090992618670421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183566162320121323491560561 137674621740090992618670421)
                ·
                  refine ⟨403343618379172829937511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137674621740090992618670421 403343618379172829937511)
                  ·
                    rfl

theorem cell23_7069580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_7069580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069580 prefixEnd_7069580 := by exact prefixLift 7069580
  have htrace : WordTrace (prefixWord ++ tailWord_7069580) baseStart_7069580 baseEnd_7069580 := by
    simpa [prefixWord, tailWord_7069580, baseEnd_7069580] using wordTrace_append hprefix tailTrace_7069580
  have hstable : (prefixWord ++ tailWord_7069580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069580).length < 2 ^ (prefixWord ++ tailWord_7069580).sum := by decide
  have hdescent : baseEnd_7069580 < baseStart_7069580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069594 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7069594 : Nat := 118140960795 + 7069594 * 2 ^ 59
def prefixEnd_7069594 : Nat := 4983230072969 + 3 ^ 40 * 7069594 * 2
def baseEnd_7069594 : Nat := 3630099754141718414662535

theorem tailTrace_7069594 : CollatzResearch.WordTrace tailWord_7069594 prefixEnd_7069594 3630099754141718414662535 := by
  unfold tailWord_7069594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64462319087518950843759959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171899517566717202250026557 64462319087518950843759959)
  ·
    refine ⟨96693478631278426265639939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64462319087518950843759959 96693478631278426265639939)
    ·
      refine ⟨145040217946917639398459909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96693478631278426265639939 145040217946917639398459909)
      ·
        refine ⟨27195040865047057387211233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145040217946917639398459909 27195040865047057387211233)
        ·
          refine ⟨20396280648785293040408425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27195040865047057387211233 20396280648785293040408425)
          ·
            refine ⟨15297210486588969780306319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20396280648785293040408425 15297210486588969780306319)
            ·
              refine ⟨22945815729883454670459479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15297210486588969780306319 22945815729883454670459479)
              ·
                refine ⟨34418723594825182005689219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22945815729883454670459479 34418723594825182005689219)
                ·
                  refine ⟨51628085392237773008533829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34418723594825182005689219 51628085392237773008533829)
                  ·
                    refine ⟨9680266011044582439100093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51628085392237773008533829 9680266011044582439100093)
                    ·
                      refine ⟨3630099754141718414662535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680266011044582439100093 3630099754141718414662535)
                      ·
                        rfl

theorem cell23_7069594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7069594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069594 prefixEnd_7069594 := by exact prefixLift 7069594
  have htrace : WordTrace (prefixWord ++ tailWord_7069594) baseStart_7069594 baseEnd_7069594 := by
    simpa [prefixWord, tailWord_7069594, baseEnd_7069594] using wordTrace_append hprefix tailTrace_7069594
  have hstable : (prefixWord ++ tailWord_7069594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069594).length < 2 ^ (prefixWord ++ tailWord_7069594).sum := by decide
  have hdescent : baseEnd_7069594 < baseStart_7069594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069617 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7069617 : Nat := 118140960795 + 7069617 * 2 ^ 59
def prefixEnd_7069617 : Nat := 4983230072969 + 3 ^ 40 * 7069617 * 2
def baseEnd_7069617 : Nat := 3630111564196771824674929

theorem tailTrace_7069617 : CollatzResearch.WordTrace tailWord_7069617 prefixEnd_7069617 3630111564196771824674929 := by
  unfold tailWord_7069617
  simp only [CollatzResearch.WordTrace]
  refine ⟨257850115228992478303127105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171900076819328318868751403 257850115228992478303127105)
  ·
    refine ⟨193387586421744358727345329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257850115228992478303127105 193387586421744358727345329)
    ·
      refine ⟨145040689816308269045508997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193387586421744358727345329 145040689816308269045508997)
      ·
        refine ⟨27195129340557800446032937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145040689816308269045508997 27195129340557800446032937)
        ·
          refine ⟨20396347005418350334524703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27195129340557800446032937 20396347005418350334524703)
          ·
            refine ⟨30594520508127525501787055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20396347005418350334524703 30594520508127525501787055)
            ·
              refine ⟨45891780762191288252680583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30594520508127525501787055 45891780762191288252680583)
              ·
                refine ⟨68837671143286932379020875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45891780762191288252680583 68837671143286932379020875)
                ·
                  refine ⟨103256506714930398568531313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68837671143286932379020875 103256506714930398568531313)
                  ·
                    refine ⟨77442380036197798926398485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103256506714930398568531313 77442380036197798926398485)
                    ·
                      refine ⟨3630111564196771824674929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77442380036197798926398485 3630111564196771824674929)
                      ·
                        rfl

theorem cell23_7069617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7069617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069617 prefixEnd_7069617 := by exact prefixLift 7069617
  have htrace : WordTrace (prefixWord ++ tailWord_7069617) baseStart_7069617 baseEnd_7069617 := by
    simpa [prefixWord, tailWord_7069617, baseEnd_7069617] using wordTrace_append hprefix tailTrace_7069617
  have hstable : (prefixWord ++ tailWord_7069617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069617).length < 2 ^ (prefixWord ++ tailWord_7069617).sum := by decide
  have hdescent : baseEnd_7069617 < baseStart_7069617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069644 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_7069644 : Nat := 118140960795 + 7069644 * 2 ^ 59
def prefixEnd_7069644 : Nat := 4983230072969 + 3 ^ 40 * 7069644 * 2
def baseEnd_7069644 : Nat := 1210041809391481073012435

theorem tailTrace_7069644 : CollatzResearch.WordTrace tailWord_7069644 prefixEnd_7069644 1210041809391481073012435 := by
  unfold tailWord_7069644
  simp only [CollatzResearch.WordTrace]
  refine ⟨128925549999947330957179993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171900733333263107942906657 128925549999947330957179993)
  ·
    refine ⟨96694162499960498217884995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128925549999947330957179993 96694162499960498217884995)
    ·
      refine ⟨145041243749940747326827493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96694162499960498217884995 145041243749940747326827493)
      ·
        refine ⟨27195233203113890123780155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145041243749940747326827493 27195233203113890123780155)
        ·
          refine ⟨40792849804670835185670233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27195233203113890123780155 40792849804670835185670233)
          ·
            refine ⟨30594637353503126389252675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40792849804670835185670233 30594637353503126389252675)
            ·
              refine ⟨45891956030254689583879013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30594637353503126389252675 45891956030254689583879013)
              ·
                refine ⟨8604741755672754296977315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45891956030254689583879013 8604741755672754296977315)
                ·
                  refine ⟨12907112633509131445465973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604741755672754296977315 12907112633509131445465973)
                  ·
                    refine ⟨1210041809391481073012435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907112633509131445465973 1210041809391481073012435)
                    ·
                      rfl

theorem cell23_7069644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_7069644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069644 prefixEnd_7069644 := by exact prefixLift 7069644
  have htrace : WordTrace (prefixWord ++ tailWord_7069644) baseStart_7069644 baseEnd_7069644 := by
    simpa [prefixWord, tailWord_7069644, baseEnd_7069644] using wordTrace_append hprefix tailTrace_7069644
  have hstable : (prefixWord ++ tailWord_7069644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069644).length < 2 ^ (prefixWord ++ tailWord_7069644).sum := by decide
  have hdescent : baseEnd_7069644 < baseStart_7069644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069674 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_7069674 : Nat := 118140960795 + 7069674 * 2 ^ 59
def prefixEnd_7069674 : Nat := 4983230072969 + 3 ^ 40 * 7069674 * 2
def baseEnd_7069674 : Nat := 1210046944198026033887389

theorem tailTrace_7069674 : CollatzResearch.WordTrace tailWord_7069674 prefixEnd_7069674 1210046944198026033887389 := by
  unfold tailWord_7069674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64463048547446494259488019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171901462793190651358634717 64463048547446494259488019)
  ·
    refine ⟨96694572821169741389232029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64463048547446494259488019 96694572821169741389232029)
    ·
      refine ⟨36260464807938653020962011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96694572821169741389232029 36260464807938653020962011)
      ·
        refine ⟨54390697211907979531443017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36260464807938653020962011 54390697211907979531443017)
        ·
          refine ⟨40793022908930984648582263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54390697211907979531443017 40793022908930984648582263)
          ·
            refine ⟨61189534363396476972873395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40793022908930984648582263 61189534363396476972873395)
            ·
              refine ⟨91784301545094715459310093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61189534363396476972873395 91784301545094715459310093)
              ·
                refine ⟨34419113079410518297241285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91784301545094715459310093 34419113079410518297241285)
                ·
                  refine ⟨6453583702389472180732741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34419113079410518297241285 6453583702389472180732741)
                  ·
                    refine ⟨1210046944198026033887389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453583702389472180732741 1210046944198026033887389)
                    ·
                      rfl

theorem cell23_7069674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_7069674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069674 prefixEnd_7069674 := by exact prefixLift 7069674
  have htrace : WordTrace (prefixWord ++ tailWord_7069674) baseStart_7069674 baseEnd_7069674 := by
    simpa [prefixWord, tailWord_7069674, baseEnd_7069674] using wordTrace_append hprefix tailTrace_7069674
  have hstable : (prefixWord ++ tailWord_7069674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069674).length < 2 ^ (prefixWord ++ tailWord_7069674).sum := by decide
  have hdescent : baseEnd_7069674 < baseStart_7069674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069691 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 2, 4]
def baseStart_7069691 : Nat := 118140960795 + 7069691 * 2 ^ 59
def prefixEnd_7069691 : Nat := 4983230072969 + 3 ^ 40 * 7069691 * 2
def baseEnd_7069691 : Nat := 1210049853921734845049863

theorem tailTrace_7069691 : CollatzResearch.WordTrace tailWord_7069691 prefixEnd_7069691 1210049853921734845049863 := by
  unfold tailWord_7069691
  simp only [CollatzResearch.WordTrace]
  refine ⟨257852814230724388941320927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171901876153816259294213951 257852814230724388941320927)
  ·
    refine ⟨386779221346086583411981391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257852814230724388941320927 386779221346086583411981391)
    ·
      refine ⟨580168832019129875117972087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386779221346086583411981391 580168832019129875117972087)
      ·
        refine ⟨870253248028694812676958131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580168832019129875117972087 870253248028694812676958131)
        ·
          refine ⟨1305379872043042219015437197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870253248028694812676958131 1305379872043042219015437197)
          ·
            refine ⟨489517452016140832130788949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1305379872043042219015437197 489517452016140832130788949)
            ·
              refine ⟨5736532640814150376532683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 489517452016140832130788949 5736532640814150376532683)
              ·
                refine ⟨8604798961221225564799025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736532640814150376532683 8604798961221225564799025)
                ·
                  refine ⟨6453599220915919173599269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604798961221225564799025 6453599220915919173599269)
                  ·
                    refine ⟨1210049853921734845049863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453599220915919173599269 1210049853921734845049863)
                    ·
                      rfl

theorem cell23_7069691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 4].length) (baseStart_7069691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069691 prefixEnd_7069691 := by exact prefixLift 7069691
  have htrace : WordTrace (prefixWord ++ tailWord_7069691) baseStart_7069691 baseEnd_7069691 := by
    simpa [prefixWord, tailWord_7069691, baseEnd_7069691] using wordTrace_append hprefix tailTrace_7069691
  have hstable : (prefixWord ++ tailWord_7069691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069691).length < 2 ^ (prefixWord ++ tailWord_7069691).sum := by decide
  have hdescent : baseEnd_7069691 < baseStart_7069691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069701 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_7069701 : Nat := 118140960795 + 7069701 * 2 ^ 59
def prefixEnd_7069701 : Nat := 4983230072969 + 3 ^ 40 * 7069701 * 2
def baseEnd_7069701 : Nat := 3630154696571749496024543

theorem tailTrace_7069701 : CollatzResearch.WordTrace tailWord_7069701 prefixEnd_7069701 3630154696571749496024543 := by
  unfold tailWord_7069701
  simp only [CollatzResearch.WordTrace]
  refine ⟨257853178960688160649184957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171902119307125440432789971 257853178960688160649184957)
  ·
    refine ⟨96694942110258060243444359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257853178960688160649184957 96694942110258060243444359)
    ·
      refine ⟨145042413165387090365166539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96694942110258060243444359 145042413165387090365166539)
      ·
        refine ⟨217563619748080635547749809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145042413165387090365166539 217563619748080635547749809)
        ·
          refine ⟨163172714811060476660812357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217563619748080635547749809 163172714811060476660812357)
          ·
            refine ⟨30594884027073839373902317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163172714811060476660812357 30594884027073839373902317)
            ·
              refine ⟨11473081510152689765213369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30594884027073839373902317 11473081510152689765213369)
              ·
                refine ⟨8604811132614517323910027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11473081510152689765213369 8604811132614517323910027)
                ·
                  refine ⟨12907216698921775985865041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604811132614517323910027 12907216698921775985865041)
                  ·
                    refine ⟨9680412524191331989398781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12907216698921775985865041 9680412524191331989398781)
                    ·
                      refine ⟨3630154696571749496024543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680412524191331989398781 3630154696571749496024543)
                      ·
                        rfl

theorem cell23_7069701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_7069701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069701 prefixEnd_7069701 := by exact prefixLift 7069701
  have htrace : WordTrace (prefixWord ++ tailWord_7069701) baseStart_7069701 baseEnd_7069701 := by
    simpa [prefixWord, tailWord_7069701, baseEnd_7069701] using wordTrace_append hprefix tailTrace_7069701
  have hstable : (prefixWord ++ tailWord_7069701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069701).length < 2 ^ (prefixWord ++ tailWord_7069701).sum := by decide
  have hdescent : baseEnd_7069701 < baseStart_7069701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069732 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7069732 : Nat := 118140960795 + 7069732 * 2 ^ 59
def prefixEnd_7069732 : Nat := 4983230072969 + 3 ^ 40 * 7069732 * 2
def baseEnd_7069732 : Nat := 3630170614472038874736901

theorem tailTrace_7069732 : CollatzResearch.WordTrace tailWord_7069732 prefixEnd_7069732 3630170614472038874736901 := by
  unfold tailWord_7069732
  simp only [CollatzResearch.WordTrace]
  refine ⟨128927154811787926471781725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171902873082383901962375633 128927154811787926471781725)
  ·
    refine ⟨48347683054420472426918147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128927154811787926471781725 48347683054420472426918147)
    ·
      refine ⟨72521524581630708640377221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48347683054420472426918147 72521524581630708640377221)
      ·
        refine ⟨13597785859055757870070729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72521524581630708640377221 13597785859055757870070729)
        ·
          refine ⟨10198339394291818402553047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597785859055757870070729 10198339394291818402553047)
          ·
            refine ⟨15297509091437727603829571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198339394291818402553047 15297509091437727603829571)
            ·
              refine ⟨22946263637156591405744357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15297509091437727603829571 22946263637156591405744357)
              ·
                refine ⟨4302424431966860888577067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22946263637156591405744357 4302424431966860888577067)
                ·
                  refine ⟨6453636647950291332865601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302424431966860888577067 6453636647950291332865601)
                  ·
                    refine ⟨4840227485962718499649201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453636647950291332865601 4840227485962718499649201)
                    ·
                      refine ⟨3630170614472038874736901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840227485962718499649201 3630170614472038874736901)
                      ·
                        rfl

theorem cell23_7069732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7069732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069732 prefixEnd_7069732 := by exact prefixLift 7069732
  have htrace : WordTrace (prefixWord ++ tailWord_7069732) baseStart_7069732 baseEnd_7069732 := by
    simpa [prefixWord, tailWord_7069732, baseEnd_7069732] using wordTrace_append hprefix tailTrace_7069732
  have hstable : (prefixWord ++ tailWord_7069732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069732).length < 2 ^ (prefixWord ++ tailWord_7069732).sum := by decide
  have hdescent : baseEnd_7069732 < baseStart_7069732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069747 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 8]
def baseStart_7069747 : Nat := 118140960795 + 7069747 * 2 ^ 59
def prefixEnd_7069747 : Nat := 4983230072969 + 3 ^ 40 * 7069747 * 2
def baseEnd_7069747 : Nat := 1210059438893952105349777

theorem tailTrace_7069747 : CollatzResearch.WordTrace tailWord_7069747 prefixEnd_7069747 1210059438893952105349777 := by
  unfold tailWord_7069747
  simp only [CollatzResearch.WordTrace]
  refine ⟨257854856718521510505359495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171903237812347673670239663 257854856718521510505359495)
  ·
    refine ⟨386782285077782265758039243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257854856718521510505359495 386782285077782265758039243)
    ·
      refine ⟨580173427616673398637058865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386782285077782265758039243 580173427616673398637058865)
      ·
        refine ⟨435130070712505048977794149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580173427616673398637058865 435130070712505048977794149)
        ·
          refine ⟨81586888258594696683336403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435130070712505048977794149 81586888258594696683336403)
          ·
            refine ⟨122380332387892045025004605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81586888258594696683336403 122380332387892045025004605)
            ·
              refine ⟨45892624645459516884376727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122380332387892045025004605 45892624645459516884376727)
              ·
                refine ⟨68838936968189275326565091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45892624645459516884376727 68838936968189275326565091)
                ·
                  refine ⟨103258405452283912989847637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68838936968189275326565091 103258405452283912989847637)
                  ·
                    refine ⟨1210059438893952105349777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103258405452283912989847637 1210059438893952105349777)
                    ·
                      rfl

theorem cell23_7069747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_7069747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069747 prefixEnd_7069747 := by exact prefixLift 7069747
  have htrace : WordTrace (prefixWord ++ tailWord_7069747) baseStart_7069747 baseEnd_7069747 := by
    simpa [prefixWord, tailWord_7069747, baseEnd_7069747] using wordTrace_append hprefix tailTrace_7069747
  have hstable : (prefixWord ++ tailWord_7069747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069747).length < 2 ^ (prefixWord ++ tailWord_7069747).sum := by decide
  have hdescent : baseEnd_7069747 < baseStart_7069747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069771 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 6, 2, 2]
def baseStart_7069771 : Nat := 118140960795 + 7069771 * 2 ^ 59
def prefixEnd_7069771 : Nat := 4983230072969 + 3 ^ 40 * 7069771 * 2
def baseEnd_7069771 : Nat := 3630190640217564222149221

theorem tailTrace_7069771 : CollatzResearch.WordTrace tailWord_7069771 prefixEnd_7069771 3630190640217564222149221 := by
  unfold tailWord_7069771
  simp only [CollatzResearch.WordTrace]
  refine ⟨257855732070434562604233167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171903821380289708402822111 257855732070434562604233167)
  ·
    refine ⟨386783598105651843906349751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257855732070434562604233167 386783598105651843906349751)
    ·
      refine ⟨580175397158477765859524627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386783598105651843906349751 580175397158477765859524627)
      ·
        refine ⟨870263095737716648789286941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580175397158477765859524627 870263095737716648789286941)
        ·
          refine ⟨326348660901643743295982603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 870263095737716648789286941 326348660901643743295982603)
          ·
            refine ⟨489522991352465614943973905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326348660901643743295982603 489522991352465614943973905)
            ·
              refine ⟨367142243514349211207980429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489522991352465614943973905 367142243514349211207980429)
              ·
                refine ⟨137678341317880954202992661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367142243514349211207980429 137678341317880954202992661)
                ·
                  refine ⟨6453672249275669728265281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137678341317880954202992661 6453672249275669728265281)
                  ·
                    refine ⟨4840254186956752296198961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453672249275669728265281 4840254186956752296198961)
                    ·
                      refine ⟨3630190640217564222149221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840254186956752296198961 3630190640217564222149221)
                      ·
                        rfl

theorem cell23_7069771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2, 2].length) (baseStart_7069771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069771 prefixEnd_7069771 := by exact prefixLift 7069771
  have htrace : WordTrace (prefixWord ++ tailWord_7069771) baseStart_7069771 baseEnd_7069771 := by
    simpa [prefixWord, tailWord_7069771, baseEnd_7069771] using wordTrace_append hprefix tailTrace_7069771
  have hstable : (prefixWord ++ tailWord_7069771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069771).length < 2 ^ (prefixWord ++ tailWord_7069771).sum := by decide
  have hdescent : baseEnd_7069771 < baseStart_7069771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069777 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 11]
def baseStart_7069777 : Nat := 118140960795 + 7069777 * 2 ^ 59
def prefixEnd_7069777 : Nat := 4983230072969 + 3 ^ 40 * 7069777 * 2
def baseEnd_7069777 : Nat := 403354857900165688741577

theorem tailTrace_7069777 : CollatzResearch.WordTrace tailWord_7069777 prefixEnd_7069777 403354857900165688741577 := by
  unfold tailWord_7069777
  simp only [CollatzResearch.WordTrace]
  refine ⟨257855950908412825628951585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171903967272275217085967723 257855950908412825628951585)
  ·
    refine ⟨193391963181309619221713689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257855950908412825628951585 193391963181309619221713689)
    ·
      refine ⟨145043972385982214416285267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193391963181309619221713689 145043972385982214416285267)
      ·
        refine ⟨217565958578973321624427901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145043972385982214416285267 217565958578973321624427901)
        ·
          refine ⟨81587234467114995609160463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217565958578973321624427901 81587234467114995609160463)
          ·
            refine ⟨122380851700672493413740695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81587234467114995609160463 122380851700672493413740695)
            ·
              refine ⟨183571277551008740120611043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122380851700672493413740695 183571277551008740120611043)
              ·
                refine ⟨275356916326513110180916565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183571277551008740120611043 275356916326513110180916565)
                ·
                  refine ⟨403354857900165688741577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 275356916326513110180916565 403354857900165688741577)
                  ·
                    rfl

theorem cell23_7069777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_7069777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069777 prefixEnd_7069777 := by exact prefixLift 7069777
  have htrace : WordTrace (prefixWord ++ tailWord_7069777) baseStart_7069777 baseEnd_7069777 := by
    simpa [prefixWord, tailWord_7069777, baseEnd_7069777] using wordTrace_append hprefix tailTrace_7069777
  have hstable : (prefixWord ++ tailWord_7069777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069777).length < 2 ^ (prefixWord ++ tailWord_7069777).sum := by decide
  have hdescent : baseEnd_7069777 < baseStart_7069777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069782 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7069782 : Nat := 118140960795 + 7069782 * 2 ^ 59
def prefixEnd_7069782 : Nat := 4983230072969 + 3 ^ 40 * 7069782 * 2
def baseEnd_7069782 : Nat := 3630196288504763679111671

theorem tailTrace_7069782 : CollatzResearch.WordTrace tailWord_7069782 prefixEnd_7069782 3630196288504763679111671 := by
  unfold tailWord_7069782
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116008329587169467680225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171904088848929807655255733 16116008329587169467680225)
  ·
    refine ⟨12087006247190377100760169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16116008329587169467680225 12087006247190377100760169)
    ·
      refine ⟨9065254685392782825570127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12087006247190377100760169 9065254685392782825570127)
      ·
        refine ⟨13597882028089174238355191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065254685392782825570127 13597882028089174238355191)
        ·
          refine ⟨20396823042133761357532787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13597882028089174238355191 20396823042133761357532787)
          ·
            refine ⟨30595234563200642036299181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20396823042133761357532787 30595234563200642036299181)
            ·
              refine ⟨11473212961200240763612193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30595234563200642036299181 11473212961200240763612193)
              ·
                refine ⟨8604909720900180572709145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11473212961200240763612193 8604909720900180572709145)
                ·
                  refine ⟨6453682290675135429531859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604909720900180572709145 6453682290675135429531859)
                  ·
                    refine ⟨9680523436012703144297789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453682290675135429531859 9680523436012703144297789)
                    ·
                      refine ⟨3630196288504763679111671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680523436012703144297789 3630196288504763679111671)
                      ·
                        rfl

theorem cell23_7069782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7069782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069782 prefixEnd_7069782 := by exact prefixLift 7069782
  have htrace : WordTrace (prefixWord ++ tailWord_7069782) baseStart_7069782 baseEnd_7069782 := by
    simpa [prefixWord, tailWord_7069782, baseEnd_7069782] using wordTrace_append hprefix tailTrace_7069782
  have hstable : (prefixWord ++ tailWord_7069782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069782).length < 2 ^ (prefixWord ++ tailWord_7069782).sum := by decide
  have hdescent : baseEnd_7069782 < baseStart_7069782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069784 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7069784 : Nat := 118140960795 + 7069784 * 2 ^ 59
def prefixEnd_7069784 : Nat := 4983230072969 + 3 ^ 40 * 7069784 * 2
def baseEnd_7069784 : Nat := 3630197315466072671286661

theorem tailTrace_7069784 : CollatzResearch.WordTrace tailWord_7069784 prefixEnd_7069784 3630197315466072671286661 := by
  unfold tailWord_7069784
  simp only [CollatzResearch.WordTrace]
  refine ⟨128928103109693732912228203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171904137479591643882970937 128928103109693732912228203)
  ·
    refine ⟨193392154664540599368342305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128928103109693732912228203 193392154664540599368342305)
    ·
      refine ⟨145044115998405449526256729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193392154664540599368342305 145044115998405449526256729)
      ·
        refine ⟨108783086998804087144692547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145044115998405449526256729 108783086998804087144692547)
        ·
          refine ⟨163174630498206130717038821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108783086998804087144692547 163174630498206130717038821)
          ·
            refine ⟨30595243218413649509444779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163174630498206130717038821 30595243218413649509444779)
            ·
              refine ⟨45892864827620474264167169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30595243218413649509444779 45892864827620474264167169)
              ·
                refine ⟨34419648620715355698125377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45892864827620474264167169 34419648620715355698125377)
                ·
                  refine ⟨25814736465536516773594033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34419648620715355698125377 25814736465536516773594033)
                  ·
                    refine ⟨19361052349152387580195525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25814736465536516773594033 19361052349152387580195525)
                    ·
                      refine ⟨3630197315466072671286661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19361052349152387580195525 3630197315466072671286661)
                      ·
                        rfl

theorem cell23_7069784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7069784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069784 prefixEnd_7069784 := by exact prefixLift 7069784
  have htrace : WordTrace (prefixWord ++ tailWord_7069784) baseStart_7069784 baseEnd_7069784 := by
    simpa [prefixWord, tailWord_7069784, baseEnd_7069784] using wordTrace_append hprefix tailTrace_7069784
  have hstable : (prefixWord ++ tailWord_7069784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069784).length < 2 ^ (prefixWord ++ tailWord_7069784).sum := by decide
  have hdescent : baseEnd_7069784 < baseStart_7069784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069824 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_7069824 : Nat := 118140960795 + 7069824 * 2 ^ 59
def prefixEnd_7069824 : Nat := 4983230072969 + 3 ^ 40 * 7069824 * 2
def baseEnd_7069824 : Nat := 1210072618230750838262159

theorem tailTrace_7069824 : CollatzResearch.WordTrace tailWord_7069824 prefixEnd_7069824 1210072618230750838262159 := by
  unfold tailWord_7069824
  simp only [CollatzResearch.WordTrace]
  refine ⟨128928832569621276327956263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171905110092828368437275017 128928832569621276327956263)
  ·
    refine ⟨193393248854431914491934395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128928832569621276327956263 193393248854431914491934395)
    ·
      refine ⟨290089873281647871737901593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193393248854431914491934395 290089873281647871737901593)
      ·
        refine ⟨217567404961235903803426195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290089873281647871737901593 217567404961235903803426195)
        ·
          refine ⟨326351107441853855705139293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217567404961235903803426195 326351107441853855705139293)
          ·
            refine ⟨122381665290695195889427235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326351107441853855705139293 122381665290695195889427235)
            ·
              refine ⟨183572497936042793834140853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122381665290695195889427235 183572497936042793834140853)
              ·
                refine ⟨17209921681504011921950705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183572497936042793834140853 17209921681504011921950705)
                ·
                  refine ⟨12907441261128008941463029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17209921681504011921950705 12907441261128008941463029)
                  ·
                    refine ⟨1210072618230750838262159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907441261128008941463029 1210072618230750838262159)
                    ·
                      rfl

theorem cell23_7069824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_7069824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069824 prefixEnd_7069824 := by exact prefixLift 7069824
  have htrace : WordTrace (prefixWord ++ tailWord_7069824) baseStart_7069824 baseEnd_7069824 := by
    simpa [prefixWord, tailWord_7069824, baseEnd_7069824] using wordTrace_append hprefix tailTrace_7069824
  have hstable : (prefixWord ++ tailWord_7069824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069824).length < 2 ^ (prefixWord ++ tailWord_7069824).sum := by decide
  have hdescent : baseEnd_7069824 < baseStart_7069824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069861 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_7069861 : Nat := 118140960795 + 7069861 * 2 ^ 59
def prefixEnd_7069861 : Nat := 4983230072969 + 3 ^ 40 * 7069861 * 2
def baseEnd_7069861 : Nat := 3630236853476468870023807

theorem tailTrace_7069861 : CollatzResearch.WordTrace tailWord_7069861 prefixEnd_7069861 3630236853476468870023807 := by
  unfold tailWord_7069861
  simp only [CollatzResearch.WordTrace]
  refine ⟨257859014640108507975009437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171906009760072338650006291 257859014640108507975009437)
  ·
    refine ⟨96697130490040690490628539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257859014640108507975009437 96697130490040690490628539)
    ·
      refine ⟨145045695735061035735942809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96697130490040690490628539 145045695735061035735942809)
      ·
        refine ⟨108784271801295776801957107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145045695735061035735942809 108784271801295776801957107)
        ·
          refine ⟨163176407701943665202935661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108784271801295776801957107 163176407701943665202935661)
          ·
            refine ⟨61191152888228874451100873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163176407701943665202935661 61191152888228874451100873)
            ·
              refine ⟨45893364666171655838325655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61191152888228874451100873 45893364666171655838325655)
              ·
                refine ⟨68840046999257483757488483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45893364666171655838325655 68840046999257483757488483)
                ·
                  refine ⟨103260070498886225636232725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68840046999257483757488483 103260070498886225636232725)
                  ·
                    refine ⟨4840315804635291826698409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103260070498886225636232725 4840315804635291826698409)
                    ·
                      refine ⟨3630236853476468870023807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840315804635291826698409 3630236853476468870023807)
                      ·
                        rfl

theorem cell23_7069861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_7069861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069861 prefixEnd_7069861 := by exact prefixLift 7069861
  have htrace : WordTrace (prefixWord ++ tailWord_7069861) baseStart_7069861 baseEnd_7069861 := by
    simpa [prefixWord, tailWord_7069861, baseEnd_7069861] using wordTrace_append hprefix tailTrace_7069861
  have hstable : (prefixWord ++ tailWord_7069861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069861).length < 2 ^ (prefixWord ++ tailWord_7069861).sum := by decide
  have hdescent : baseEnd_7069861 < baseStart_7069861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069905 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 1, 4]
def baseStart_7069905 : Nat := 118140960795 + 7069905 * 2 ^ 59
def prefixEnd_7069905 : Nat := 4983230072969 + 3 ^ 40 * 7069905 * 2
def baseEnd_7069905 : Nat := 1210086482208422232624535

theorem tailTrace_7069905 : CollatzResearch.WordTrace tailWord_7069905 prefixEnd_7069905 1210086482208422232624535 := by
  unfold tailWord_7069905
  simp only [CollatzResearch.WordTrace]
  refine ⟨257860619451949103489611169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171907079634632735659740779 257860619451949103489611169)
  ·
    refine ⟨193395464588961827617208377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257860619451949103489611169 193395464588961827617208377)
    ·
      refine ⟨145046598441721370712906283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193395464588961827617208377 145046598441721370712906283)
      ·
        refine ⟨217569897662582056069359425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145046598441721370712906283 217569897662582056069359425)
        ·
          refine ⟨163177423246936542052019569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217569897662582056069359425 163177423246936542052019569)
          ·
            refine ⟨122383067435202406539014677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163177423246936542052019569 122383067435202406539014677)
            ·
              refine ⟨5736706286025112806516313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122383067435202406539014677 5736706286025112806516313)
              ·
                refine ⟨4302529714518834604887235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736706286025112806516313 4302529714518834604887235)
                ·
                  refine ⟨6453794571778251907330853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302529714518834604887235 6453794571778251907330853)
                  ·
                    refine ⟨1210086482208422232624535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453794571778251907330853 1210086482208422232624535)
                    ·
                      rfl

theorem cell23_7069905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_7069905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069905 prefixEnd_7069905 := by exact prefixLift 7069905
  have htrace : WordTrace (prefixWord ++ tailWord_7069905) baseStart_7069905 baseEnd_7069905 := by
    simpa [prefixWord, tailWord_7069905, baseEnd_7069905] using wordTrace_append hprefix tailTrace_7069905
  have hstable : (prefixWord ++ tailWord_7069905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069905).length < 2 ^ (prefixWord ++ tailWord_7069905).sum := by decide
  have hdescent : baseEnd_7069905 < baseStart_7069905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069924 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_7069924 : Nat := 118140960795 + 7069924 * 2 ^ 59
def prefixEnd_7069924 : Nat := 4983230072969 + 3 ^ 40 * 7069924 * 2
def baseEnd_7069924 : Nat := 3630269202757702123536017

theorem tailTrace_7069924 : CollatzResearch.WordTrace tailWord_7069924 prefixEnd_7069924 3630269202757702123536017 := by
  unfold tailWord_7069924
  simp only [CollatzResearch.WordTrace]
  refine ⟨128930656219440134867276413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171907541625920179823035217 128930656219440134867276413)
  ·
    refine ⟨48348996082290050575228655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128930656219440134867276413 48348996082290050575228655)
    ·
      refine ⟨72523494123435075862842983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48348996082290050575228655 72523494123435075862842983)
      ·
        refine ⟨108785241185152613794264475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72523494123435075862842983 108785241185152613794264475)
        ·
          refine ⟨163177861777728920691396713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108785241185152613794264475 163177861777728920691396713)
          ·
            refine ⟨122383396333296690518547535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163177861777728920691396713 122383396333296690518547535)
            ·
              refine ⟨183575094499945035777821303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122383396333296690518547535 183575094499945035777821303)
              ·
                refine ⟨275362641749917553666731955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183575094499945035777821303 275362641749917553666731955)
                ·
                  refine ⟨413043962624876330500097933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275362641749917553666731955 413043962624876330500097933)
                  ·
                    refine ⟨154891485984328623937536725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413043962624876330500097933 154891485984328623937536725)
                    ·
                      refine ⟨3630269202757702123536017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154891485984328623937536725 3630269202757702123536017)
                      ·
                        rfl

theorem cell23_7069924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_7069924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069924 prefixEnd_7069924 := by exact prefixLift 7069924
  have htrace : WordTrace (prefixWord ++ tailWord_7069924) baseStart_7069924 baseEnd_7069924 := by
    simpa [prefixWord, tailWord_7069924, baseEnd_7069924] using wordTrace_append hprefix tailTrace_7069924
  have hstable : (prefixWord ++ tailWord_7069924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069924).length < 2 ^ (prefixWord ++ tailWord_7069924).sum := by decide
  have hdescent : baseEnd_7069924 < baseStart_7069924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069928 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7069928 : Nat := 118140960795 + 7069928 * 2 ^ 59
def prefixEnd_7069928 : Nat := 4983230072969 + 3 ^ 40 * 7069928 * 2
def baseEnd_7069928 : Nat := 3630271256680320107885999

theorem tailTrace_7069928 : CollatzResearch.WordTrace tailWord_7069928 prefixEnd_7069928 3630271256680320107885999 := by
  unfold tailWord_7069928
  simp only [CollatzResearch.WordTrace]
  refine ⟨128930729165432889208849219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171907638887243852278465625 128930729165432889208849219)
  ·
    refine ⟨193396093748149333813273829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128930729165432889208849219 193396093748149333813273829)
    ·
      refine ⟨36261767577778000089988843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193396093748149333813273829 36261767577778000089988843)
      ·
        refine ⟨54392651366667000134983265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36261767577778000089988843 54392651366667000134983265)
        ·
          refine ⟨40794488525000250101237449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54392651366667000134983265 40794488525000250101237449)
          ·
            refine ⟨30595866393750187575928087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40794488525000250101237449 30595866393750187575928087)
            ·
              refine ⟨45893799590625281363892131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30595866393750187575928087 45893799590625281363892131)
              ·
                refine ⟨68840699385937922045838197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45893799590625281363892131 68840699385937922045838197)
                ·
                  refine ⟨6453815567431680191797331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68840699385937922045838197 6453815567431680191797331)
                  ·
                    refine ⟨9680723351147520287695997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453815567431680191797331 9680723351147520287695997)
                    ·
                      refine ⟨3630271256680320107885999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680723351147520287695997 3630271256680320107885999)
                      ·
                        rfl

theorem cell23_7069928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7069928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069928 prefixEnd_7069928 := by exact prefixLift 7069928
  have htrace : WordTrace (prefixWord ++ tailWord_7069928) baseStart_7069928 baseEnd_7069928 := by
    simpa [prefixWord, tailWord_7069928, baseEnd_7069928] using wordTrace_append hprefix tailTrace_7069928
  have hstable : (prefixWord ++ tailWord_7069928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069928).length < 2 ^ (prefixWord ++ tailWord_7069928).sum := by decide
  have hdescent : baseEnd_7069928 < baseStart_7069928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069931 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 1, 5]
def baseStart_7069931 : Nat := 118140960795 + 7069931 * 2 ^ 59
def prefixEnd_7069931 : Nat := 4983230072969 + 3 ^ 40 * 7069931 * 2
def baseEnd_7069931 : Nat := 1210090932374094532049495

theorem tailTrace_7069931 : CollatzResearch.WordTrace tailWord_7069931 prefixEnd_7069931 1210090932374094532049495 := by
  unfold tailWord_7069931
  simp only [CollatzResearch.WordTrace]
  refine ⟨257861567749854909930057647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171907711833236606620038431 257861567749854909930057647)
  ·
    refine ⟨386792351624782364895086471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257861567749854909930057647 386792351624782364895086471)
    ·
      refine ⟨580188527437173547342629707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386792351624782364895086471 580188527437173547342629707)
      ·
        refine ⟨870282791155760321013944561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580188527437173547342629707 870282791155760321013944561)
        ·
          refine ⟨652712093366820240760458421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870282791155760321013944561 652712093366820240760458421)
          ·
            refine ⟨61191758753139397571292977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 652712093366820240760458421 61191758753139397571292977)
            ·
              refine ⟨45893819064854548178469733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61191758753139397571292977 45893819064854548178469733)
              ·
                refine ⟨8605091074660227783463075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45893819064854548178469733 8605091074660227783463075)
                ·
                  refine ⟨12907636611990341675194613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605091074660227783463075 12907636611990341675194613)
                  ·
                    refine ⟨1210090932374094532049495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907636611990341675194613 1210090932374094532049495)
                    ·
                      rfl

theorem cell23_7069931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 5].length) (baseStart_7069931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069931 prefixEnd_7069931 := by exact prefixLift 7069931
  have htrace : WordTrace (prefixWord ++ tailWord_7069931) baseStart_7069931 baseEnd_7069931 := by
    simpa [prefixWord, tailWord_7069931, baseEnd_7069931] using wordTrace_append hprefix tailTrace_7069931
  have hstable : (prefixWord ++ tailWord_7069931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069931).length < 2 ^ (prefixWord ++ tailWord_7069931).sum := by decide
  have hdescent : baseEnd_7069931 < baseStart_7069931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069948 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_7069948 : Nat := 118140960795 + 7069948 * 2 ^ 59
def prefixEnd_7069948 : Nat := 4983230072969 + 3 ^ 40 * 7069948 * 2
def baseEnd_7069948 : Nat := 1210093842097803343211969

theorem tailTrace_7069948 : CollatzResearch.WordTrace tailWord_7069948 prefixEnd_7069948 1210093842097803343211969 := by
  unfold tailWord_7069948
  simp only [CollatzResearch.WordTrace]
  refine ⟨128931093895396660916713249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171908125193862214555617665 128931093895396660916713249)
  ·
    refine ⟨96698320421547495687534937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128931093895396660916713249 96698320421547495687534937)
    ·
      refine ⟨72523740316160621765651203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96698320421547495687534937 72523740316160621765651203)
      ·
        refine ⟨108785610474240932648476805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72523740316160621765651203 108785610474240932648476805)
        ·
          refine ⟨20397301963920174871589401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108785610474240932648476805 20397301963920174871589401)
          ·
            refine ⟨15297976472940131153692051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20397301963920174871589401 15297976472940131153692051)
            ·
              refine ⟨22946964709410196730538077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15297976472940131153692051 22946964709410196730538077)
              ·
                refine ⟨8605111766028823773951779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22946964709410196730538077 8605111766028823773951779)
                ·
                  refine ⟨12907667649043235660927669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605111766028823773951779 12907667649043235660927669)
                  ·
                    refine ⟨1210093842097803343211969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907667649043235660927669 1210093842097803343211969)
                    ·
                      rfl

theorem cell23_7069948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_7069948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069948 prefixEnd_7069948 := by exact prefixLift 7069948
  have htrace : WordTrace (prefixWord ++ tailWord_7069948) baseStart_7069948 baseEnd_7069948 := by
    simpa [prefixWord, tailWord_7069948, baseEnd_7069948] using wordTrace_append hprefix tailTrace_7069948
  have hstable : (prefixWord ++ tailWord_7069948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069948).length < 2 ^ (prefixWord ++ tailWord_7069948).sum := by decide
  have hdescent : baseEnd_7069948 < baseStart_7069948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069971 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3]
def baseStart_7069971 : Nat := 118140960795 + 7069971 * 2 ^ 59
def prefixEnd_7069971 : Nat := 4983230072969 + 3 ^ 40 * 7069971 * 2
def baseEnd_7069971 : Nat := 3630293336348463439648301

theorem tailTrace_7069971 : CollatzResearch.WordTrace tailWord_7069971 prefixEnd_7069971 3630293336348463439648301 := by
  unfold tailWord_7069971
  simp only [CollatzResearch.WordTrace]
  refine ⟨257863026669709996761513767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171908684446473331174342511 257863026669709996761513767)
  ·
    refine ⟨386794540004564995142270651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257863026669709996761513767 386794540004564995142270651)
    ·
      refine ⟨580191810006847492713405977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386794540004564995142270651 580191810006847492713405977)
      ·
        refine ⟨435143857505135619535054483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580191810006847492713405977 435143857505135619535054483)
        ·
          refine ⟨652715786257703429302581725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435143857505135619535054483 652715786257703429302581725)
          ·
            refine ⟨244768419846638785988468147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652715786257703429302581725 244768419846638785988468147)
            ·
              refine ⟨367152629769958178982702221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244768419846638785988468147 367152629769958178982702221)
              ·
                refine ⟨137682236163734317118513333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367152629769958178982702221 137682236163734317118513333)
                ·
                  refine ⟨12907709640350092229860625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137682236163734317118513333 12907709640350092229860625)
                  ·
                    refine ⟨9680782230262569172395469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12907709640350092229860625 9680782230262569172395469)
                    ·
                      refine ⟨3630293336348463439648301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9680782230262569172395469 3630293336348463439648301)
                      ·
                        rfl

theorem cell23_7069971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_7069971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069971 prefixEnd_7069971 := by exact prefixLift 7069971
  have htrace : WordTrace (prefixWord ++ tailWord_7069971) baseStart_7069971 baseEnd_7069971 := by
    simpa [prefixWord, tailWord_7069971, baseEnd_7069971] using wordTrace_append hprefix tailTrace_7069971
  have hstable : (prefixWord ++ tailWord_7069971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069971).length < 2 ^ (prefixWord ++ tailWord_7069971).sum := by decide
  have hdescent : baseEnd_7069971 < baseStart_7069971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069982 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7069982 : Nat := 118140960795 + 7069982 * 2 ^ 59
def prefixEnd_7069982 : Nat := 4983230072969 + 3 ^ 40 * 7069982 * 2
def baseEnd_7069982 : Nat := 1210099661545220965536917

theorem tailTrace_7069982 : CollatzResearch.WordTrace tailWord_7069982 prefixEnd_7069982 1210099661545220965536917 := by
  unfold tailWord_7069982
  simp only [CollatzResearch.WordTrace]
  refine ⟨32232928484083768205020525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171908951915113430426776133 32232928484083768205020525)
  ·
    refine ⟨12087348181531413076882697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32232928484083768205020525 12087348181531413076882697)
    ·
      refine ⟨9065511136148559807662023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12087348181531413076882697 9065511136148559807662023)
      ·
        refine ⟨13598266704222839711493035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065511136148559807662023 13598266704222839711493035)
        ·
          refine ⟨20397400056334259567239553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13598266704222839711493035 20397400056334259567239553)
          ·
            refine ⟨15298050042250694675429665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20397400056334259567239553 15298050042250694675429665)
            ·
              refine ⟨11473537531688021006572249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15298050042250694675429665 11473537531688021006572249)
              ·
                refine ⟨8605153148766015754929187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11473537531688021006572249 8605153148766015754929187)
                ·
                  refine ⟨12907729723149023632393781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605153148766015754929187 12907729723149023632393781)
                  ·
                    refine ⟨1210099661545220965536917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907729723149023632393781 1210099661545220965536917)
                    ·
                      rfl

theorem cell23_7069982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7069982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069982 prefixEnd_7069982 := by exact prefixLift 7069982
  have htrace : WordTrace (prefixWord ++ tailWord_7069982) baseStart_7069982 baseEnd_7069982 := by
    simpa [prefixWord, tailWord_7069982, baseEnd_7069982] using wordTrace_append hprefix tailTrace_7069982
  have hstable : (prefixWord ++ tailWord_7069982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069982).length < 2 ^ (prefixWord ++ tailWord_7069982).sum := by decide
  have hdescent : baseEnd_7069982 < baseStart_7069982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7069985 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7069985 : Nat := 118140960795 + 7069985 * 2 ^ 59
def prefixEnd_7069985 : Nat := 4983230072969 + 3 ^ 40 * 7069985 * 2
def baseEnd_7069985 : Nat := 3630300525077626384873237

theorem tailTrace_7069985 : CollatzResearch.WordTrace tailWord_7069985 prefixEnd_7069985 3630300525077626384873237 := by
  unfold tailWord_7069985
  simp only [CollatzResearch.WordTrace]
  refine ⟨257863537291659277152523409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171909024861106184768348939 257863537291659277152523409)
  ·
    refine ⟨193397652968744457864392557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257863537291659277152523409 193397652968744457864392557)
    ·
      refine ⟨72524119863279171699147209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193397652968744457864392557 72524119863279171699147209)
      ·
        refine ⟨54393089897459378774360407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72524119863279171699147209 54393089897459378774360407)
        ·
          refine ⟨81589634846189068161540611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54393089897459378774360407 81589634846189068161540611)
          ·
            refine ⟨122384452269283602242310917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81589634846189068161540611 122384452269283602242310917)
            ·
              refine ⟨22947084800490675420433297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122384452269283602242310917 22947084800490675420433297)
              ·
                refine ⟨17210313600368006565324973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22947084800490675420433297 17210313600368006565324973)
                ·
                  refine ⟨6453867600138002461996865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17210313600368006565324973 6453867600138002461996865)
                  ·
                    refine ⟨4840400700103501846497649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453867600138002461996865 4840400700103501846497649)
                    ·
                      refine ⟨3630300525077626384873237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840400700103501846497649 3630300525077626384873237)
                      ·
                        rfl

theorem cell23_7069985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7069985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7069985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7069985 prefixEnd_7069985 := by exact prefixLift 7069985
  have htrace : WordTrace (prefixWord ++ tailWord_7069985) baseStart_7069985 baseEnd_7069985 := by
    simpa [prefixWord, tailWord_7069985, baseEnd_7069985] using wordTrace_append hprefix tailTrace_7069985
  have hstable : (prefixWord ++ tailWord_7069985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7069985).length < 2 ^ (prefixWord ++ tailWord_7069985).sum := by decide
  have hdescent : baseEnd_7069985 < baseStart_7069985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7069985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070070 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7070070 : Nat := 118140960795 + 7070070 * 2 ^ 59
def prefixEnd_7070070 : Nat := 4983230072969 + 3 ^ 40 * 7070070 * 2
def baseEnd_7070070 : Nat := 3630344170933258552310347

theorem tailTrace_7070070 : CollatzResearch.WordTrace tailWord_7070070 prefixEnd_7070070 3630344170933258552310347 := by
  unfold tailWord_7070070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116664843521958541835479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171911091664234224446245109 16116664843521958541835479)
  ·
    refine ⟨24174997265282937812753219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16116664843521958541835479 24174997265282937812753219)
    ·
      refine ⟨36262495897924406719129829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24174997265282937812753219 36262495897924406719129829)
      ·
        refine ⟨6799217980860826259836843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36262495897924406719129829 6799217980860826259836843)
        ·
          refine ⟨10198826971291239389755265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799217980860826259836843 10198826971291239389755265)
          ·
            refine ⟨7649120228468429542316449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10198826971291239389755265 7649120228468429542316449)
            ·
              refine ⟨5736840171351322156737337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649120228468429542316449 5736840171351322156737337)
              ·
                refine ⟨4302630128513491617553003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736840171351322156737337 4302630128513491617553003)
                ·
                  refine ⟨6453945192770237426329505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302630128513491617553003 6453945192770237426329505)
                  ·
                    refine ⟨4840458894577678069747129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453945192770237426329505 4840458894577678069747129)
                    ·
                      refine ⟨3630344170933258552310347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840458894577678069747129 3630344170933258552310347)
                      ·
                        rfl

theorem cell23_7070070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7070070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070070 prefixEnd_7070070 := by exact prefixLift 7070070
  have htrace : WordTrace (prefixWord ++ tailWord_7070070) baseStart_7070070 baseEnd_7070070 := by
    simpa [prefixWord, tailWord_7070070, baseEnd_7070070] using wordTrace_append hprefix tailTrace_7070070
  have hstable : (prefixWord ++ tailWord_7070070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070070).length < 2 ^ (prefixWord ++ tailWord_7070070).sum := by decide
  have hdescent : baseEnd_7070070 < baseStart_7070070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070088 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7070088 : Nat := 118140960795 + 7070088 * 2 ^ 59
def prefixEnd_7070088 : Nat := 4983230072969 + 3 ^ 40 * 7070088 * 2
def baseEnd_7070088 : Nat := 3630353413585039481885263

theorem tailTrace_7070088 : CollatzResearch.WordTrace tailWord_7070088 prefixEnd_7070088 3630353413585039481885263 := by
  unfold tailWord_7070088
  simp only [CollatzResearch.WordTrace]
  refine ⟨128933647005143062871761459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171911529340190750495681945 128933647005143062871761459)
  ·
    refine ⟨193400470507714594307642189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128933647005143062871761459 193400470507714594307642189)
    ·
      refine ⟨72525176440392972865365821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193400470507714594307642189 72525176440392972865365821)
      ·
        refine ⟨27196941165147364824512183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72525176440392972865365821 27196941165147364824512183)
        ·
          refine ⟨40795411747721047236768275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27196941165147364824512183 40795411747721047236768275)
          ·
            refine ⟨61193117621581570855152413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40795411747721047236768275 61193117621581570855152413)
            ·
              refine ⟨22947419108093089070682155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61193117621581570855152413 22947419108093089070682155)
              ·
                refine ⟨34421128662139633606023233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22947419108093089070682155 34421128662139633606023233)
                ·
                  refine ⟨25815846496604725204517425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34421128662139633606023233 25815846496604725204517425)
                  ·
                    refine ⟨19361884872453543903388069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25815846496604725204517425 19361884872453543903388069)
                    ·
                      refine ⟨3630353413585039481885263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19361884872453543903388069 3630353413585039481885263)
                      ·
                        rfl

theorem cell23_7070088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7070088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070088 prefixEnd_7070088 := by exact prefixLift 7070088
  have htrace : WordTrace (prefixWord ++ tailWord_7070088) baseStart_7070088 baseEnd_7070088 := by
    simpa [prefixWord, tailWord_7070088, baseEnd_7070088] using wordTrace_append hprefix tailTrace_7070088
  have hstable : (prefixWord ++ tailWord_7070088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070088).length < 2 ^ (prefixWord ++ tailWord_7070088).sum := by decide
  have hdescent : baseEnd_7070088 < baseStart_7070088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070092 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_7070092 : Nat := 118140960795 + 7070092 * 2 ^ 59
def prefixEnd_7070092 : Nat := 4983230072969 + 3 ^ 40 * 7070092 * 2
def baseEnd_7070092 : Nat := 3630355467507657466235245

theorem tailTrace_7070092 : CollatzResearch.WordTrace tailWord_7070092 prefixEnd_7070092 3630355467507657466235245 := by
  unfold tailWord_7070092
  simp only [CollatzResearch.WordTrace]
  refine ⟨128933719951135817213334265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171911626601514422951112353 128933719951135817213334265)
  ·
    refine ⟨96700289963351862910000699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128933719951135817213334265 96700289963351862910000699)
    ·
      refine ⟨145050434945027794365001049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96700289963351862910000699 145050434945027794365001049)
      ·
        refine ⟨108787826208770845773750787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145050434945027794365001049 108787826208770845773750787)
        ·
          refine ⟨163181739313156268660626181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108787826208770845773750787 163181739313156268660626181)
          ·
            refine ⟨30596576121216800373867409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163181739313156268660626181 30596576121216800373867409)
            ·
              refine ⟨22947432090912600280400557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30596576121216800373867409 22947432090912600280400557)
              ·
                refine ⟨8605287034092225105150209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22947432090912600280400557 8605287034092225105150209)
                ·
                  refine ⟨6453965275569168828862657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8605287034092225105150209 6453965275569168828862657)
                  ·
                    refine ⟨4840473956676876621646993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453965275569168828862657 4840473956676876621646993)
                    ·
                      refine ⟨3630355467507657466235245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840473956676876621646993 3630355467507657466235245)
                      ·
                        rfl

theorem cell23_7070092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_7070092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070092 prefixEnd_7070092 := by exact prefixLift 7070092
  have htrace : WordTrace (prefixWord ++ tailWord_7070092) baseStart_7070092 baseEnd_7070092 := by
    simpa [prefixWord, tailWord_7070092, baseEnd_7070092] using wordTrace_append hprefix tailTrace_7070092
  have hstable : (prefixWord ++ tailWord_7070092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070092).length < 2 ^ (prefixWord ++ tailWord_7070092).sum := by decide
  have hdescent : baseEnd_7070092 < baseStart_7070092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070113 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7070113 : Nat := 118140960795 + 7070113 * 2 ^ 59
def prefixEnd_7070113 : Nat := 4983230072969 + 3 ^ 40 * 7070113 * 2
def baseEnd_7070113 : Nat := 3630366250601401884072649

theorem tailTrace_7070113 : CollatzResearch.WordTrace tailWord_7070113 prefixEnd_7070113 3630366250601401884072649 := by
  unfold tailWord_7070113
  simp only [CollatzResearch.WordTrace]
  refine ⟨257868205835195555013182993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171912137223463703342121995 257868205835195555013182993)
  ·
    refine ⟨193401154376396666259887245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257868205835195555013182993 193401154376396666259887245)
    ·
      refine ⟨72525432891148749847457717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193401154376396666259887245 72525432891148749847457717)
      ·
        refine ⟨6799259333545195298199161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72525432891148749847457717 6799259333545195298199161)
        ·
          refine ⟨5099444500158896473649371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6799259333545195298199161 5099444500158896473649371)
          ·
            refine ⟨7649166750238344710474057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099444500158896473649371 7649166750238344710474057)
            ·
              refine ⟨5736875062678758532855543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649166750238344710474057 5736875062678758532855543)
              ·
                refine ⟨8605312594018137799283315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736875062678758532855543 8605312594018137799283315)
                ·
                  refine ⟨12907968891027206698924973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605312594018137799283315 12907968891027206698924973)
                  ·
                    refine ⟨4840488334135202512096865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12907968891027206698924973 4840488334135202512096865)
                    ·
                      refine ⟨3630366250601401884072649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840488334135202512096865 3630366250601401884072649)
                      ·
                        rfl

theorem cell23_7070113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7070113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070113 prefixEnd_7070113 := by exact prefixLift 7070113
  have htrace : WordTrace (prefixWord ++ tailWord_7070113) baseStart_7070113 baseEnd_7070113 := by
    simpa [prefixWord, tailWord_7070113, baseEnd_7070113] using wordTrace_append hprefix tailTrace_7070113
  have hstable : (prefixWord ++ tailWord_7070113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070113).length < 2 ^ (prefixWord ++ tailWord_7070113).sum := by decide
  have hdescent : baseEnd_7070113 < baseStart_7070113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070115 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 5]
def baseStart_7070115 : Nat := 118140960795 + 7070115 * 2 ^ 59
def prefixEnd_7070115 : Nat := 4983230072969 + 3 ^ 40 * 7070115 * 2
def baseEnd_7070115 : Nat := 403374141951412319583071

theorem tailTrace_7070115 : CollatzResearch.WordTrace tailWord_7070115 prefixEnd_7070115 403374141951412319583071 := by
  unfold tailWord_7070115
  simp only [CollatzResearch.WordTrace]
  refine ⟨257868278781188309354755799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171912185854125539569837199 257868278781188309354755799)
  ·
    refine ⟨386802418171782464032133699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257868278781188309354755799 386802418171782464032133699)
    ·
      refine ⟨580203627257673696048200549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386802418171782464032133699 580203627257673696048200549)
      ·
        refine ⟨108788180110813818009037603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 580203627257673696048200549 108788180110813818009037603)
        ·
          refine ⟨163182270166220727013556405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108788180110813818009037603 163182270166220727013556405)
          ·
            refine ⟨15298337828083193157520913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163182270166220727013556405 15298337828083193157520913)
            ·
              refine ⟨11473753371062394868140685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15298337828083193157520913 11473753371062394868140685)
              ·
                refine ⟨4302657514148398075552757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11473753371062394868140685 4302657514148398075552757)
                ·
                  refine ⟨403374141951412319583071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302657514148398075552757 403374141951412319583071)
                  ·
                    rfl

theorem cell23_7070115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 5].length) (baseStart_7070115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070115 prefixEnd_7070115 := by exact prefixLift 7070115
  have htrace : WordTrace (prefixWord ++ tailWord_7070115) baseStart_7070115 baseEnd_7070115 := by
    simpa [prefixWord, tailWord_7070115, baseEnd_7070115] using wordTrace_append hprefix tailTrace_7070115
  have hstable : (prefixWord ++ tailWord_7070115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070115).length < 2 ^ (prefixWord ++ tailWord_7070115).sum := by decide
  have hdescent : baseEnd_7070115 < baseStart_7070115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070121 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_7070121 : Nat := 118140960795 + 7070121 * 2 ^ 59
def prefixEnd_7070121 : Nat := 4983230072969 + 3 ^ 40 * 7070121 * 2
def baseEnd_7070121 : Nat := 3630370358446637852772611

theorem tailTrace_7070121 : CollatzResearch.WordTrace tailWord_7070121 prefixEnd_7070121 3630370358446637852772611 := by
  unfold tailWord_7070121
  simp only [CollatzResearch.WordTrace]
  refine ⟨257868497619166572379474217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171912331746111048252982811 257868497619166572379474217)
  ·
    refine ⟨193401373214374929284605663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257868497619166572379474217 193401373214374929284605663)
    ·
      refine ⟨290102059821562393926908495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193401373214374929284605663 290102059821562393926908495)
      ·
        refine ⟨435153089732343590890362743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290102059821562393926908495 435153089732343590890362743)
        ·
          refine ⟨652729634598515386335544115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435153089732343590890362743 652729634598515386335544115)
          ·
            refine ⟨979094451897773079503316173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652729634598515386335544115 979094451897773079503316173)
            ·
              refine ⟨367160419461664904813743565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979094451897773079503316173 367160419461664904813743565)
              ·
                refine ⟨137685157298124339305153837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367160419461664904813743565 137685157298124339305153837)
                ·
                  refine ⟨51631933986796627239432689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137685157298124339305153837 51631933986796627239432689)
                  ·
                    refine ⟨38723950490097470429574517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51631933986796627239432689 38723950490097470429574517)
                    ·
                      refine ⟨3630370358446637852772611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38723950490097470429574517 3630370358446637852772611)
                      ·
                        rfl

theorem cell23_7070121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_7070121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070121 prefixEnd_7070121 := by exact prefixLift 7070121
  have htrace : WordTrace (prefixWord ++ tailWord_7070121) baseStart_7070121 baseEnd_7070121 := by
    simpa [prefixWord, tailWord_7070121, baseEnd_7070121] using wordTrace_append hprefix tailTrace_7070121
  have hstable : (prefixWord ++ tailWord_7070121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070121).length < 2 ^ (prefixWord ++ tailWord_7070121).sum := by decide
  have hdescent : baseEnd_7070121 < baseStart_7070121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070188 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 6]
def baseStart_7070188 : Nat := 118140960795 + 7070188 * 2 ^ 59
def prefixEnd_7070188 : Nat := 4983230072969 + 3 ^ 40 * 7070188 * 2
def baseEnd_7070188 : Nat := 403378306850054343403867

theorem tailTrace_7070188 : CollatzResearch.WordTrace tailWord_7070188 prefixEnd_7070188 403378306850054343403867 := by
  unfold tailWord_7070188
  simp only [CollatzResearch.WordTrace]
  refine ⟨128935470654961921411081609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171913960873282561881442145 128935470654961921411081609)
  ·
    refine ⟨96701602991221441058311207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128935470654961921411081609 96701602991221441058311207)
    ·
      refine ⟨145052404486832161587466811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96701602991221441058311207 145052404486832161587466811)
      ·
        refine ⟨217578606730248242381200217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145052404486832161587466811 217578606730248242381200217)
        ·
          refine ⟨163183955047686181785900163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217578606730248242381200217 163183955047686181785900163)
          ·
            refine ⟨244775932571529272678850245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163183955047686181785900163 244775932571529272678850245)
            ·
              refine ⟨45895487357161738627284421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244775932571529272678850245 45895487357161738627284421)
              ·
                refine ⟨8605403879467825992615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45895487357161738627284421 8605403879467825992615829)
                ·
                  refine ⟨403378306850054343403867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8605403879467825992615829 403378306850054343403867)
                  ·
                    rfl

theorem cell23_7070188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_7070188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070188 prefixEnd_7070188 := by exact prefixLift 7070188
  have htrace : WordTrace (prefixWord ++ tailWord_7070188) baseStart_7070188 baseEnd_7070188 := by
    simpa [prefixWord, tailWord_7070188, baseEnd_7070188] using wordTrace_append hprefix tailTrace_7070188
  have hstable : (prefixWord ++ tailWord_7070188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070188).length < 2 ^ (prefixWord ++ tailWord_7070188).sum := by decide
  have hdescent : baseEnd_7070188 < baseStart_7070188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070265 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_7070265 : Nat := 118140960795 + 7070265 * 2 ^ 59
def prefixEnd_7070265 : Nat := 4983230072969 + 3 ^ 40 * 7070265 * 2
def baseEnd_7070265 : Nat := 1210148099886961763123983

theorem tailTrace_7070265 : CollatzResearch.WordTrace tailWord_7070265 prefixEnd_7070265 1210148099886961763123983 := by
  unfold tailWord_7070265
  simp only [CollatzResearch.WordTrace]
  refine ⟨257873749730644884972716249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171915833153763256648477499 257873749730644884972716249)
  ·
    refine ⟨193405312297983663729537187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257873749730644884972716249 193405312297983663729537187)
    ·
      refine ⟨290107968446975495594305781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193405312297983663729537187 290107968446975495594305781)
      ·
        refine ⟨27197622041903952711966167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 290107968446975495594305781 27197622041903952711966167)
        ·
          refine ⟨40796433062855929067949251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27197622041903952711966167 40796433062855929067949251)
          ·
            refine ⟨61194649594283893601923877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40796433062855929067949251 61194649594283893601923877)
            ·
              refine ⟨11473996798928230050360727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61194649594283893601923877 11473996798928230050360727)
              ·
                refine ⟨17210995198392345075541091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11473996798928230050360727 17210995198392345075541091)
                ·
                  refine ⟨25816492797588517613311637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17210995198392345075541091 25816492797588517613311637)
                  ·
                    refine ⟨1210148099886961763123983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25816492797588517613311637 1210148099886961763123983)
                    ·
                      rfl

theorem cell23_7070265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_7070265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070265 prefixEnd_7070265 := by exact prefixLift 7070265
  have htrace : WordTrace (prefixWord ++ tailWord_7070265) baseStart_7070265 baseEnd_7070265 := by
    simpa [prefixWord, tailWord_7070265, baseEnd_7070265] using wordTrace_append hprefix tailTrace_7070265
  have hstable : (prefixWord ++ tailWord_7070265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070265).length < 2 ^ (prefixWord ++ tailWord_7070265).sum := by decide
  have hdescent : baseEnd_7070265 < baseStart_7070265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070272 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2]
def baseStart_7070272 : Nat := 118140960795 + 7070272 * 2 ^ 59
def prefixEnd_7070272 : Nat := 4983230072969 + 3 ^ 40 * 7070272 * 2
def baseEnd_7070272 : Nat := 3630447894025466761984417

theorem tailTrace_7070272 : CollatzResearch.WordTrace tailWord_7070272 prefixEnd_7070272 3630447894025466761984417 := by
  unfold tailWord_7070272
  simp only [CollatzResearch.WordTrace]
  refine ⟨128937002520809762584110535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171916003361079683445480713 128937002520809762584110535)
  ·
    refine ⟨193405503781214643876165803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128937002520809762584110535 193405503781214643876165803)
    ·
      refine ⟨290108255671821965814248705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193405503781214643876165803 290108255671821965814248705)
      ·
        refine ⟨217581191753866474360686529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290108255671821965814248705 217581191753866474360686529)
        ·
          refine ⟨163185893815399855770514897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217581191753866474360686529 163185893815399855770514897)
          ·
            refine ⟨122389420361549891827886173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163185893815399855770514897 122389420361549891827886173)
            ·
              refine ⟨45896032635581209435457315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122389420361549891827886173 45896032635581209435457315)
              ·
                refine ⟨68844048953371814153185973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45896032635581209435457315 68844048953371814153185973)
                ·
                  refine ⟨6454129589378607576861185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68844048953371814153185973 6454129589378607576861185)
                  ·
                    refine ⟨4840597192033955682645889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6454129589378607576861185 4840597192033955682645889)
                    ·
                      refine ⟨3630447894025466761984417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840597192033955682645889 3630447894025466761984417)
                      ·
                        rfl

theorem cell23_7070272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_7070272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070272 prefixEnd_7070272 := by exact prefixLift 7070272
  have htrace : WordTrace (prefixWord ++ tailWord_7070272) baseStart_7070272 baseEnd_7070272 := by
    simpa [prefixWord, tailWord_7070272, baseEnd_7070272] using wordTrace_append hprefix tailTrace_7070272
  have hstable : (prefixWord ++ tailWord_7070272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070272).length < 2 ^ (prefixWord ++ tailWord_7070272).sum := by decide
  have hdescent : baseEnd_7070272 < baseStart_7070272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070289 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_7070289 : Nat := 118140960795 + 7070289 * 2 ^ 59
def prefixEnd_7070289 : Nat := 4983230072969 + 3 ^ 40 * 7070289 * 2
def baseEnd_7070289 : Nat := 3630456623196593195471839

theorem tailTrace_7070289 : CollatzResearch.WordTrace tailWord_7070289 prefixEnd_7070289 3630456623196593195471839 := by
  unfold tailWord_7070289
  simp only [CollatzResearch.WordTrace]
  refine ⟨257874625082557937071589921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171916416721705291381059947 257874625082557937071589921)
  ·
    refine ⟨193405968811918452803692441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257874625082557937071589921 193405968811918452803692441)
    ·
      refine ⟨145054476608938839602769331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193405968811918452803692441 145054476608938839602769331)
      ·
        refine ⟨217581714913408259404153997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145054476608938839602769331 217581714913408259404153997)
        ·
          refine ⟨81593143092528097276557749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217581714913408259404153997 81593143092528097276557749)
          ·
            refine ⟨7649357164924509119677289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81593143092528097276557749 7649357164924509119677289)
            ·
              refine ⟨5737017873693381839757967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649357164924509119677289 5737017873693381839757967)
              ·
                refine ⟨8605526810540072759636951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737017873693381839757967 8605526810540072759636951)
                ·
                  refine ⟨12908290215810109139455427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605526810540072759636951 12908290215810109139455427)
                  ·
                    refine ⟨19362435323715163709183141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12908290215810109139455427 19362435323715163709183141)
                    ·
                      refine ⟨3630456623196593195471839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19362435323715163709183141 3630456623196593195471839)
                      ·
                        rfl

theorem cell23_7070289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_7070289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070289 prefixEnd_7070289 := by exact prefixLift 7070289
  have htrace : WordTrace (prefixWord ++ tailWord_7070289) baseStart_7070289 baseEnd_7070289 := by
    simpa [prefixWord, tailWord_7070289, baseEnd_7070289] using wordTrace_append hprefix tailTrace_7070289
  have hstable : (prefixWord ++ tailWord_7070289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070289).length < 2 ^ (prefixWord ++ tailWord_7070289).sum := by decide
  have hdescent : baseEnd_7070289 < baseStart_7070289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070298 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_7070298 : Nat := 118140960795 + 7070298 * 2 ^ 59
def prefixEnd_7070298 : Nat := 4983230072969 + 3 ^ 40 * 7070298 * 2
def baseEnd_7070298 : Nat := 3630461244522483660259297

theorem tailTrace_7070298 : CollatzResearch.WordTrace tailWord_7070298 prefixEnd_7070298 3630461244522483660259297 := by
  unfold tailWord_7070298
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468738334881332902166887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171916635559683554405778365 64468738334881332902166887)
  ·
    refine ⟨96703107502321999353250331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64468738334881332902166887 96703107502321999353250331)
    ·
      refine ⟨145054661253482999029875497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96703107502321999353250331 145054661253482999029875497)
      ·
        refine ⟨108790995940112249272406623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145054661253482999029875497 108790995940112249272406623)
        ·
          refine ⟨163186493910168373908609935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108790995940112249272406623 163186493910168373908609935)
          ·
            refine ⟨244779740865252560862914903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163186493910168373908609935 244779740865252560862914903)
            ·
              refine ⟨367169611297878841294372355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244779740865252560862914903 367169611297878841294372355)
              ·
                refine ⟨550754416946818261941558533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367169611297878841294372355 550754416946818261941558533)
                ·
                  refine ⟨103266453177528424114042225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550754416946818261941558533 103266453177528424114042225)
                  ·
                    refine ⟨77449839883146318085531669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103266453177528424114042225 77449839883146318085531669)
                    ·
                      refine ⟨3630461244522483660259297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77449839883146318085531669 3630461244522483660259297)
                      ·
                        rfl

theorem cell23_7070298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_7070298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070298 prefixEnd_7070298 := by exact prefixLift 7070298
  have htrace : WordTrace (prefixWord ++ tailWord_7070298) baseStart_7070298 baseEnd_7070298 := by
    simpa [prefixWord, tailWord_7070298, baseEnd_7070298] using wordTrace_append hprefix tailTrace_7070298
  have hstable : (prefixWord ++ tailWord_7070298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070298).length < 2 ^ (prefixWord ++ tailWord_7070298).sum := by decide
  have hdescent : baseEnd_7070298 < baseStart_7070298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070315 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 7, 2]
def baseStart_7070315 : Nat := 118140960795 + 7070315 * 2 ^ 59
def prefixEnd_7070315 : Nat := 4983230072969 + 3 ^ 40 * 7070315 * 2
def baseEnd_7070315 : Nat := 3630469973693610093746719

theorem tailTrace_7070315 : CollatzResearch.WordTrace tailWord_7070315 prefixEnd_7070315 3630469973693610093746719 := by
  unfold tailWord_7070315
  simp only [CollatzResearch.WordTrace]
  refine ⟨257875573380463743512036399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171917048920309162341357599 257875573380463743512036399)
  ·
    refine ⟨386813360070695615268054599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257875573380463743512036399 386813360070695615268054599)
    ·
      refine ⟨580220040106043422902081899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386813360070695615268054599 580220040106043422902081899)
      ·
        refine ⟨870330060159065134353122849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580220040106043422902081899 870330060159065134353122849)
        ·
          refine ⟨652747545119298850764842137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870330060159065134353122849 652747545119298850764842137)
          ·
            refine ⟨489560658839474138073631603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652747545119298850764842137 489560658839474138073631603)
            ·
              refine ⟨734340988259211207110447405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489560658839474138073631603 734340988259211207110447405)
              ·
                refine ⟨275377870597204202666417777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 734340988259211207110447405 275377870597204202666417777)
                ·
                  refine ⟨206533402947903151999813333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275377870597204202666417777 206533402947903151999813333)
                  ·
                    refine ⟨4840626631591480124995625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 206533402947903151999813333 4840626631591480124995625)
                    ·
                      refine ⟨3630469973693610093746719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840626631591480124995625 3630469973693610093746719)
                      ·
                        rfl

theorem cell23_7070315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7, 2].length) (baseStart_7070315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070315 prefixEnd_7070315 := by exact prefixLift 7070315
  have htrace : WordTrace (prefixWord ++ tailWord_7070315) baseStart_7070315 baseEnd_7070315 := by
    simpa [prefixWord, tailWord_7070315, baseEnd_7070315] using wordTrace_append hprefix tailTrace_7070315
  have hstable : (prefixWord ++ tailWord_7070315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070315).length < 2 ^ (prefixWord ++ tailWord_7070315).sum := by decide
  have hdescent : baseEnd_7070315 < baseStart_7070315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070326 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7070326 : Nat := 118140960795 + 7070326 * 2 ^ 59
def prefixEnd_7070326 : Nat := 4983230072969 + 3 ^ 40 * 7070326 * 2
def baseEnd_7070326 : Nat := 3630475621980809550709169

theorem tailTrace_7070326 : CollatzResearch.WordTrace tailWord_7070326 prefixEnd_7070326 3630475621980809550709169 := by
  unfold tailWord_7070326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117248411463993274417927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 171917316388949261593791221 16117248411463993274417927)
  ·
    refine ⟨24175872617195989911626891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16117248411463993274417927 24175872617195989911626891)
    ·
      refine ⟨36263808925793984867440337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24175872617195989911626891 36263808925793984867440337)
      ·
        refine ⟨27197856694345488650580253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36263808925793984867440337 27197856694345488650580253)
        ·
          refine ⟨10199196260379558243967595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27197856694345488650580253 10199196260379558243967595)
          ·
            refine ⟨15298794390569337365951393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10199196260379558243967595 15298794390569337365951393)
            ·
              refine ⟨11474095792927003024463545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15298794390569337365951393 11474095792927003024463545)
              ·
                refine ⟨8605571844695252268347659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474095792927003024463545 8605571844695252268347659)
                ·
                  refine ⟨12908357767042878402521489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605571844695252268347659 12908357767042878402521489)
                  ·
                    refine ⟨9681268325282158801891117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12908357767042878402521489 9681268325282158801891117)
                    ·
                      refine ⟨3630475621980809550709169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681268325282158801891117 3630475621980809550709169)
                      ·
                        rfl

theorem cell23_7070326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7070326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070326 prefixEnd_7070326 := by exact prefixLift 7070326
  have htrace : WordTrace (prefixWord ++ tailWord_7070326) baseStart_7070326 baseEnd_7070326 := by
    simpa [prefixWord, tailWord_7070326, baseEnd_7070326] using wordTrace_append hprefix tailTrace_7070326
  have hstable : (prefixWord ++ tailWord_7070326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070326).length < 2 ^ (prefixWord ++ tailWord_7070326).sum := by decide
  have hdescent : baseEnd_7070326 < baseStart_7070326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070332 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_7070332 : Nat := 118140960795 + 7070332 * 2 ^ 59
def prefixEnd_7070332 : Nat := 4983230072969 + 3 ^ 40 * 7070332 * 2
def baseEnd_7070332 : Nat := 3630478702864736527234141

theorem tailTrace_7070332 : CollatzResearch.WordTrace tailWord_7070332 prefixEnd_7070332 3630478702864736527234141 := by
  unfold tailWord_7070332
  simp only [CollatzResearch.WordTrace]
  refine ⟨128938096710701077707702625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171917462280934770276936833 128938096710701077707702625)
  ·
    refine ⟨96703572533025808280776969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128938096710701077707702625 96703572533025808280776969)
    ·
      refine ⟨72527679399769356210582727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96703572533025808280776969 72527679399769356210582727)
      ·
        refine ⟨108791519099654034315874091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72527679399769356210582727 108791519099654034315874091)
        ·
          refine ⟨163187278649481051473811137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108791519099654034315874091 163187278649481051473811137)
          ·
            refine ⟨122390458987110788605358353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163187278649481051473811137 122390458987110788605358353)
            ·
              refine ⟨91792844240333091454018765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122390458987110788605358353 91792844240333091454018765)
              ·
                refine ⟨34422316590124909295257037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91792844240333091454018765 34422316590124909295257037)
                ·
                  refine ⟨12908368721296840985721389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34422316590124909295257037 12908368721296840985721389)
                  ·
                    refine ⟨4840638270486315369645521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12908368721296840985721389 4840638270486315369645521)
                    ·
                      refine ⟨3630478702864736527234141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840638270486315369645521 3630478702864736527234141)
                      ·
                        rfl

theorem cell23_7070332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_7070332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070332 prefixEnd_7070332 := by exact prefixLift 7070332
  have htrace : WordTrace (prefixWord ++ tailWord_7070332) baseStart_7070332 baseEnd_7070332 := by
    simpa [prefixWord, tailWord_7070332, baseEnd_7070332] using wordTrace_append hprefix tailTrace_7070332
  have hstable : (prefixWord ++ tailWord_7070332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070332).length < 2 ^ (prefixWord ++ tailWord_7070332).sum := by decide
  have hdescent : baseEnd_7070332 < baseStart_7070332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070395 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3]
def baseStart_7070395 : Nat := 118140960795 + 7070395 * 2 ^ 59
def prefixEnd_7070395 : Nat := 4983230072969 + 3 ^ 40 * 7070395 * 2
def baseEnd_7070395 : Nat := 3630511052145969780746351

theorem tailTrace_7070395 : CollatzResearch.WordTrace tailWord_7070395 prefixEnd_7070395 3630511052145969780746351 := by
  unfold tailWord_7070395
  simp only [CollatzResearch.WordTrace]
  refine ⟨257878491220173917174948639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171918994146782611449965759 257878491220173917174948639)
  ·
    refine ⟨386817736830260875762422959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257878491220173917174948639 386817736830260875762422959)
    ·
      refine ⟨580226605245391313643634439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386817736830260875762422959 580226605245391313643634439)
      ·
        refine ⟨870339907868086970465451659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580226605245391313643634439 870339907868086970465451659)
        ·
          refine ⟨1305509861802130455698177489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870339907868086970465451659 1305509861802130455698177489)
          ·
            refine ⟨979132396351597841773633117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305509861802130455698177489 979132396351597841773633117)
            ·
              refine ⟨367174648631849190665112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979132396351597841773633117 367174648631849190665112419)
              ·
                refine ⟨550761972947773785997668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367174648631849190665112419 550761972947773785997668629)
                ·
                  refine ⟨25816967481926896218640717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 550761972947773785997668629 25816967481926896218640717)
                  ·
                    refine ⟨9681362805722586081990269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25816967481926896218640717 9681362805722586081990269)
                    ·
                      refine ⟨3630511052145969780746351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681362805722586081990269 3630511052145969780746351)
                      ·
                        rfl

theorem cell23_7070395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3].length) (baseStart_7070395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070395 prefixEnd_7070395 := by exact prefixLift 7070395
  have htrace : WordTrace (prefixWord ++ tailWord_7070395) baseStart_7070395 baseEnd_7070395 := by
    simpa [prefixWord, tailWord_7070395, baseEnd_7070395] using wordTrace_append hprefix tailTrace_7070395
  have hstable : (prefixWord ++ tailWord_7070395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070395).length < 2 ^ (prefixWord ++ tailWord_7070395).sum := by decide
  have hdescent : baseEnd_7070395 < baseStart_7070395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070425 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_7070425 : Nat := 118140960795 + 7070425 * 2 ^ 59
def prefixEnd_7070425 : Nat := 4983230072969 + 3 ^ 40 * 7070425 * 2
def baseEnd_7070425 : Nat := 3630526456565604663371213

theorem tailTrace_7070425 : CollatzResearch.WordTrace tailWord_7070425 prefixEnd_7070425 3630526456565604663371213 := by
  unfold tailWord_7070425
  simp only [CollatzResearch.WordTrace]
  refine ⟨257879585410065232298540729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171919723606710154865693819 257879585410065232298540729)
  ·
    refine ⟨193409689057548924223905547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257879585410065232298540729 193409689057548924223905547)
    ·
      refine ⟨290114533586323386335858321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193409689057548924223905547 290114533586323386335858321)
      ·
        refine ⟨217585900189742539751893741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290114533586323386335858321 217585900189742539751893741)
        ·
          refine ⟨81594712571153452406960153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217585900189742539751893741 81594712571153452406960153)
          ·
            refine ⟨61196034428365089305220115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81594712571153452406960153 61196034428365089305220115)
            ·
              refine ⟨91794051642547633957830173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61196034428365089305220115 91794051642547633957830173)
              ·
                refine ⟨34422769365955362734186315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91794051642547633957830173 34422769365955362734186315)
                ·
                  refine ⟨51634154048933044101279473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34422769365955362734186315 51634154048933044101279473)
                  ·
                    refine ⟨38725615536699783075959605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51634154048933044101279473 38725615536699783075959605)
                    ·
                      refine ⟨3630526456565604663371213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38725615536699783075959605 3630526456565604663371213)
                      ·
                        rfl

theorem cell23_7070425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_7070425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070425 prefixEnd_7070425 := by exact prefixLift 7070425
  have htrace : WordTrace (prefixWord ++ tailWord_7070425) baseStart_7070425 baseEnd_7070425 := by
    simpa [prefixWord, tailWord_7070425, baseEnd_7070425] using wordTrace_append hprefix tailTrace_7070425
  have hstable : (prefixWord ++ tailWord_7070425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070425).length < 2 ^ (prefixWord ++ tailWord_7070425).sum := by decide
  have hdescent : baseEnd_7070425 < baseStart_7070425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070479 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 1, 4]
def baseStart_7070479 : Nat := 118140960795 + 7070479 * 2 ^ 59
def prefixEnd_7070479 : Nat := 4983230072969 + 3 ^ 40 * 7070479 * 2
def baseEnd_7070479 : Nat := 1210184728173649150698655

theorem tailTrace_7070479 : CollatzResearch.WordTrace tailWord_7070479 prefixEnd_7070479 1210184728173649150698655 := by
  unfold tailWord_7070479
  simp only [CollatzResearch.WordTrace]
  refine ⟨257881554951869599521006491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171921036634579733014004327 257881554951869599521006491)
  ·
    refine ⟨386822332427804399281509737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257881554951869599521006491 386822332427804399281509737)
    ·
      refine ⟨290116749320853299461132303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386822332427804399281509737 290116749320853299461132303)
      ·
        refine ⟨435175123981279949191698455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290116749320853299461132303 435175123981279949191698455)
        ·
          refine ⟨652762685971919923787547683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435175123981279949191698455 652762685971919923787547683)
          ·
            refine ⟨979144028957879885681321525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652762685971919923787547683 979144028957879885681321525)
            ·
              refine ⟨91794752714801239282623893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 979144028957879885681321525 91794752714801239282623893)
              ·
                refine ⟨4302879033506308091372995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91794752714801239282623893 4302879033506308091372995)
                ·
                  refine ⟨6454318550259462137059493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302879033506308091372995 6454318550259462137059493)
                  ·
                    refine ⟨1210184728173649150698655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6454318550259462137059493 1210184728173649150698655)
                    ·
                      rfl

theorem cell23_7070479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 4].length) (baseStart_7070479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070479 prefixEnd_7070479 := by exact prefixLift 7070479
  have htrace : WordTrace (prefixWord ++ tailWord_7070479) baseStart_7070479 baseEnd_7070479 := by
    simpa [prefixWord, tailWord_7070479, baseEnd_7070479] using wordTrace_append hprefix tailTrace_7070479
  have hstable : (prefixWord ++ tailWord_7070479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070479).length < 2 ^ (prefixWord ++ tailWord_7070479).sum := by decide
  have hdescent : baseEnd_7070479 < baseStart_7070479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070556 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7070556 : Nat := 118140960795 + 7070556 * 2 ^ 59
def prefixEnd_7070556 : Nat := 4983230072969 + 3 ^ 40 * 7070556 * 2
def baseEnd_7070556 : Nat := 1210197907510447883611037

theorem tailTrace_7070556 : CollatzResearch.WordTrace tailWord_7070556 prefixEnd_7070556 1210197907510447883611037 := by
  unfold tailWord_7070556
  simp only [CollatzResearch.WordTrace]
  refine ⟨128942181686295320835779761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171922908915060427781039681 128942181686295320835779761)
  ·
    refine ⟨96706636264721490626834821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128942181686295320835779761 96706636264721490626834821)
    ·
      refine ⟨18132494299635279492531529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96706636264721490626834821 18132494299635279492531529)
      ·
        refine ⟨13599370724726459619398647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18132494299635279492531529 13599370724726459619398647)
        ·
          refine ⟨20399056087089689429097971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13599370724726459619398647 20399056087089689429097971)
          ·
            refine ⟨30598584130634534143646957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20399056087089689429097971 30598584130634534143646957)
            ·
              refine ⟨11474469048987950303867609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30598584130634534143646957 11474469048987950303867609)
              ·
                refine ⟨8605851786740962727900707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474469048987950303867609 8605851786740962727900707)
                ·
                  refine ⟨12908777680111444091851061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605851786740962727900707 12908777680111444091851061)
                  ·
                    refine ⟨1210197907510447883611037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12908777680111444091851061 1210197907510447883611037)
                    ·
                      rfl

theorem cell23_7070556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7070556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070556 prefixEnd_7070556 := by exact prefixLift 7070556
  have htrace : WordTrace (prefixWord ++ tailWord_7070556) baseStart_7070556 baseEnd_7070556 := by
    simpa [prefixWord, tailWord_7070556, baseEnd_7070556] using wordTrace_append hprefix tailTrace_7070556
  have hstable : (prefixWord ++ tailWord_7070556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070556).length < 2 ^ (prefixWord ++ tailWord_7070556).sum := by decide
  have hdescent : baseEnd_7070556 < baseStart_7070556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070579 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 3]
def baseStart_7070579 : Nat := 118140960795 + 7070579 * 2 ^ 59
def prefixEnd_7070579 : Nat := 4983230072969 + 3 ^ 40 * 7070579 * 2
def baseEnd_7070579 : Nat := 3630605532586397060845505

theorem tailTrace_7070579 : CollatzResearch.WordTrace tailWord_7070579 prefixEnd_7070579 3630605532586397060845505 := by
  unfold tailWord_7070579
  simp only [CollatzResearch.WordTrace]
  refine ⟨257885202251507316599646791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171923468167671544399764527 257885202251507316599646791)
  ·
    refine ⟨386827803377260974899470187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257885202251507316599646791 386827803377260974899470187)
    ·
      refine ⟨580241705065891462349205281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386827803377260974899470187 580241705065891462349205281)
      ·
        refine ⟨435181278799418596761903961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580241705065891462349205281 435181278799418596761903961)
        ·
          refine ⟨326385959099563947571427971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435181278799418596761903961 326385959099563947571427971)
          ·
            refine ⟨489578938649345921357141957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326385959099563947571427971 489578938649345921357141957)
            ·
              refine ⟨91796050996752360254464117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489578938649345921357141957 91796050996752360254464117)
              ·
                refine ⟨8605879780945533773856011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91796050996752360254464117 8605879780945533773856011)
                ·
                  refine ⟨12908819671418300660784017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605879780945533773856011 12908819671418300660784017)
                  ·
                    refine ⟨9681614753563725495588013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12908819671418300660784017 9681614753563725495588013)
                    ·
                      refine ⟨3630605532586397060845505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681614753563725495588013 3630605532586397060845505)
                      ·
                        rfl

theorem cell23_7070579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_7070579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070579 prefixEnd_7070579 := by exact prefixLift 7070579
  have htrace : WordTrace (prefixWord ++ tailWord_7070579) baseStart_7070579 baseEnd_7070579 := by
    simpa [prefixWord, tailWord_7070579, baseEnd_7070579] using wordTrace_append hprefix tailTrace_7070579
  have hstable : (prefixWord ++ tailWord_7070579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070579).length < 2 ^ (prefixWord ++ tailWord_7070579).sum := by decide
  have hdescent : baseEnd_7070579 < baseStart_7070579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070599 : List Nat := [1, 1, 4, 2, 3, 3, 1, 8]
def baseStart_7070599 : Nat := 118140960795 + 7070599 * 2 ^ 59
def prefixEnd_7070599 : Nat := 4983230072969 + 3 ^ 40 * 7070599 * 2
def baseEnd_7070599 : Nat := 134467251933314332688719

theorem tailTrace_7070599 : CollatzResearch.WordTrace tailWord_7070599 prefixEnd_7070599 134467251933314332688719 := by
  unfold tailWord_7070599
  simp only [CollatzResearch.WordTrace]
  refine ⟨257885931711434860015374851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171923954474289906676916567 257885931711434860015374851)
  ·
    refine ⟨386828897567152290023062277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257885931711434860015374851 386828897567152290023062277)
    ·
      refine ⟨72530418293841054379324177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386828897567152290023062277 72530418293841054379324177)
      ·
        refine ⟨54397813720380790784493133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72530418293841054379324177 54397813720380790784493133)
        ·
          refine ⟨20399180145142796544184925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54397813720380790784493133 20399180145142796544184925)
          ·
            refine ⟨7649692554428548704069347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20399180145142796544184925 7649692554428548704069347)
            ·
              refine ⟨11474538831642823056104021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649692554428548704069347 11474538831642823056104021)
              ·
                refine ⟨134467251933314332688719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11474538831642823056104021 134467251933314332688719)
                ·
                  rfl

theorem cell23_7070599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 8].length) (baseStart_7070599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070599 prefixEnd_7070599 := by exact prefixLift 7070599
  have htrace : WordTrace (prefixWord ++ tailWord_7070599) baseStart_7070599 baseEnd_7070599 := by
    simpa [prefixWord, tailWord_7070599, baseEnd_7070599] using wordTrace_append hprefix tailTrace_7070599
  have hstable : (prefixWord ++ tailWord_7070599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070599).length < 2 ^ (prefixWord ++ tailWord_7070599).sum := by decide
  have hdescent : baseEnd_7070599 < baseStart_7070599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070609 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_7070609 : Nat := 118140960795 + 7070609 * 2 ^ 59
def prefixEnd_7070609 : Nat := 4983230072969 + 3 ^ 40 * 7070609 * 2
def baseEnd_7070609 : Nat := 3630620937006031943470367

theorem tailTrace_7070609 : CollatzResearch.WordTrace tailWord_7070609 prefixEnd_7070609 3630620937006031943470367 := by
  unfold tailWord_7070609
  simp only [CollatzResearch.WordTrace]
  refine ⟨257886296441398631723238881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171924197627599087815492587 257886296441398631723238881)
  ·
    refine ⟨193414722331048973792429161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257886296441398631723238881 193414722331048973792429161)
    ·
      refine ⟨145061041748286730344321871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193414722331048973792429161 145061041748286730344321871)
      ·
        refine ⟨217591562622430095516482807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145061041748286730344321871 217591562622430095516482807)
        ·
          refine ⟨326387343933645143274724211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217591562622430095516482807 326387343933645143274724211)
          ·
            refine ⟨489581015900467714912086317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326387343933645143274724211 489581015900467714912086317)
            ·
              refine ⟨183592880962675393092032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489581015900467714912086317 183592880962675393092032369)
              ·
                refine ⟨137694660722006544819024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183592880962675393092032369 137694660722006544819024277)
                ·
                  refine ⟨6454437221344056788391763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137694660722006544819024277 6454437221344056788391763)
                  ·
                    refine ⟨9681655832016085182587645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454437221344056788391763 9681655832016085182587645)
                    ·
                      refine ⟨3630620937006031943470367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681655832016085182587645 3630620937006031943470367)
                      ·
                        rfl

theorem cell23_7070609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_7070609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070609 prefixEnd_7070609 := by exact prefixLift 7070609
  have htrace : WordTrace (prefixWord ++ tailWord_7070609) baseStart_7070609 baseEnd_7070609 := by
    simpa [prefixWord, tailWord_7070609, baseEnd_7070609] using wordTrace_append hprefix tailTrace_7070609
  have hstable : (prefixWord ++ tailWord_7070609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070609).length < 2 ^ (prefixWord ++ tailWord_7070609).sum := by decide
  have hdescent : baseEnd_7070609 < baseStart_7070609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070610 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7070610 : Nat := 118140960795 + 7070610 * 2 ^ 59
def prefixEnd_7070610 : Nat := 4983230072969 + 3 ^ 40 * 7070610 * 2
def baseEnd_7070610 : Nat := 3630621450486686439557863

theorem tailTrace_7070610 : CollatzResearch.WordTrace tailWord_7070610 prefixEnd_7070610 3630621450486686439557863 := by
  unfold tailWord_7070610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64471583228598752223506321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171924221942930005929350189 64471583228598752223506321)
  ·
    refine ⟨48353687421449064167629741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64471583228598752223506321 48353687421449064167629741)
    ·
      refine ⟨18132632783043399062861153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48353687421449064167629741 18132632783043399062861153)
      ·
        refine ⟨13599474587282549297145865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18132632783043399062861153 13599474587282549297145865)
        ·
          refine ⟨10199605940461911972859399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13599474587282549297145865 10199605940461911972859399)
          ·
            refine ⟨15299408910692867959289099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10199605940461911972859399 15299408910692867959289099)
            ·
              refine ⟨22949113366039301938933649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15299408910692867959289099 22949113366039301938933649)
              ·
                refine ⟨17211835024529476454200237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22949113366039301938933649 17211835024529476454200237)
                ·
                  refine ⟨6454438134198553670325089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17211835024529476454200237 6454438134198553670325089)
                  ·
                    refine ⟨4840828600648915252743817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6454438134198553670325089 4840828600648915252743817)
                    ·
                      refine ⟨3630621450486686439557863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840828600648915252743817 3630621450486686439557863)
                      ·
                        rfl

theorem cell23_7070610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7070610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070610 prefixEnd_7070610 := by exact prefixLift 7070610
  have htrace : WordTrace (prefixWord ++ tailWord_7070610) baseStart_7070610 baseEnd_7070610 := by
    simpa [prefixWord, tailWord_7070610, baseEnd_7070610] using wordTrace_append hprefix tailTrace_7070610
  have hstable : (prefixWord ++ tailWord_7070610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070610).length < 2 ^ (prefixWord ++ tailWord_7070610).sum := by decide
  have hdescent : baseEnd_7070610 < baseStart_7070610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070626 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_7070626 : Nat := 118140960795 + 7070626 * 2 ^ 59
def prefixEnd_7070626 : Nat := 4983230072969 + 3 ^ 40 * 7070626 * 2
def baseEnd_7070626 : Nat := 3630629666177158376957789

theorem tailTrace_7070626 : CollatzResearch.WordTrace tailWord_7070626 prefixEnd_7070626 3630629666177158376957789 := by
  unfold tailWord_7070626
  simp only [CollatzResearch.WordTrace]
  refine ⟨64471729120584260906651933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171924610988224695751071821 64471729120584260906651933)
  ·
    refine ⟨24176898420219097839994475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64471729120584260906651933 24176898420219097839994475)
    ·
      refine ⟨36265347630328646759991713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24176898420219097839994475 36265347630328646759991713)
      ·
        refine ⟨27199010722746485069993785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36265347630328646759991713 27199010722746485069993785)
        ·
          refine ⟨20399258042059863802495339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27199010722746485069993785 20399258042059863802495339)
          ·
            refine ⟨30598887063089795703743009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20399258042059863802495339 30598887063089795703743009)
            ·
              refine ⟨22949165297317346777807257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30598887063089795703743009 22949165297317346777807257)
              ·
                refine ⟨17211873972988010083355443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22949165297317346777807257 17211873972988010083355443)
                ·
                  refine ⟨25817810959482015125033165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17211873972988010083355443 25817810959482015125033165)
                  ·
                    refine ⟨9681679109805755671887437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25817810959482015125033165 9681679109805755671887437)
                    ·
                      refine ⟨3630629666177158376957789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681679109805755671887437 3630629666177158376957789)
                      ·
                        rfl

theorem cell23_7070626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_7070626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070626 prefixEnd_7070626 := by exact prefixLift 7070626
  have htrace : WordTrace (prefixWord ++ tailWord_7070626) baseStart_7070626 baseEnd_7070626 := by
    simpa [prefixWord, tailWord_7070626, baseEnd_7070626] using wordTrace_append hprefix tailTrace_7070626
  have hstable : (prefixWord ++ tailWord_7070626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070626).length < 2 ^ (prefixWord ++ tailWord_7070626).sum := by decide
  have hdescent : baseEnd_7070626 < baseStart_7070626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070636 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_7070636 : Nat := 118140960795 + 7070636 * 2 ^ 59
def prefixEnd_7070636 : Nat := 4983230072969 + 3 ^ 40 * 7070636 * 2
def baseEnd_7070636 : Nat := 3630634800983703337832743

theorem tailTrace_7070636 : CollatzResearch.WordTrace tailWord_7070636 prefixEnd_7070636 3630634800983703337832743 := by
  unfold tailWord_7070636
  simp only [CollatzResearch.WordTrace]
  refine ⟨128943640606150407667235881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171924854141533876889647841 128943640606150407667235881)
  ·
    refine ⟨96707730454612805750426911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128943640606150407667235881 96707730454612805750426911)
    ·
      refine ⟨145061595681919208625640367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96707730454612805750426911 145061595681919208625640367)
      ·
        refine ⟨217592393522878812938460551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145061595681919208625640367 217592393522878812938460551)
        ·
          refine ⟨326388590284318219407690827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217592393522878812938460551 326388590284318219407690827)
          ·
            refine ⟨489582885426477329111536241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326388590284318219407690827 489582885426477329111536241)
            ·
              refine ⟨367187164069857996833652181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489582885426477329111536241 367187164069857996833652181)
              ·
                refine ⟨8605949157887296800788723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367187164069857996833652181 8605949157887296800788723)
                ·
                  refine ⟨12908923736830945201183085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605949157887296800788723 12908923736830945201183085)
                  ·
                    refine ⟨4840846401311604450443657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12908923736830945201183085 4840846401311604450443657)
                    ·
                      refine ⟨3630634800983703337832743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4840846401311604450443657 3630634800983703337832743)
                      ·
                        rfl

theorem cell23_7070636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_7070636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070636 prefixEnd_7070636 := by exact prefixLift 7070636
  have htrace : WordTrace (prefixWord ++ tailWord_7070636) baseStart_7070636 baseEnd_7070636 := by
    simpa [prefixWord, tailWord_7070636, baseEnd_7070636] using wordTrace_append hprefix tailTrace_7070636
  have hstable : (prefixWord ++ tailWord_7070636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070636).length < 2 ^ (prefixWord ++ tailWord_7070636).sum := by decide
  have hdescent : baseEnd_7070636 < baseStart_7070636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070637 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7070637 : Nat := 118140960795 + 7070637 * 2 ^ 59
def prefixEnd_7070637 : Nat := 4983230072969 + 3 ^ 40 * 7070637 * 2
def baseEnd_7070637 : Nat := 1210211771488119277973413

theorem tailTrace_7070637 : CollatzResearch.WordTrace tailWord_7070637 prefixEnd_7070637 1210211771488119277973413 := by
  unfold tailWord_7070637
  simp only [CollatzResearch.WordTrace]
  refine ⟨257887317685297192505258165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171924878456864795003505443 257887317685297192505258165)
  ·
    refine ⟨24176936032996611797367953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257887317685297192505258165 24176936032996611797367953)
    ·
      refine ⟨18132702024747458848025965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24176936032996611797367953 18132702024747458848025965)
      ·
        refine ⟨6799763259280297068009737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18132702024747458848025965 6799763259280297068009737)
        ·
          refine ⟨5099822444460222801007303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6799763259280297068009737 5099822444460222801007303)
          ·
            refine ⟨7649733666690334201510955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099822444460222801007303 7649733666690334201510955)
            ·
              refine ⟨11474600500035501302266433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649733666690334201510955 11474600500035501302266433)
              ·
                refine ⟨8605950375026625976699825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474600500035501302266433 8605950375026625976699825)
                ·
                  refine ⟨6454462781269969482524869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8605950375026625976699825 6454462781269969482524869)
                  ·
                    refine ⟨1210211771488119277973413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6454462781269969482524869 1210211771488119277973413)
                    ·
                      rfl

theorem cell23_7070637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7070637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070637 prefixEnd_7070637 := by exact prefixLift 7070637
  have htrace : WordTrace (prefixWord ++ tailWord_7070637) baseStart_7070637 baseEnd_7070637 := by
    simpa [prefixWord, tailWord_7070637, baseEnd_7070637] using wordTrace_append hprefix tailTrace_7070637
  have hstable : (prefixWord ++ tailWord_7070637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070637).length < 2 ^ (prefixWord ++ tailWord_7070637).sum := by decide
  have hdescent : baseEnd_7070637 < baseStart_7070637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070660 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7070660 : Nat := 118140960795 + 7070660 * 2 ^ 59
def prefixEnd_7070660 : Nat := 4983230072969 + 3 ^ 40 * 7070660 * 2
def baseEnd_7070660 : Nat := 3630647124519411243932633

theorem tailTrace_7070660 : CollatzResearch.WordTrace tailWord_7070660 prefixEnd_7070660 3630647124519411243932633 := by
  unfold tailWord_7070660
  simp only [CollatzResearch.WordTrace]
  refine ⟨128944078282106933716672717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171925437709475911622230289 128944078282106933716672717)
  ·
    refine ⟨48354029355790100143752269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128944078282106933716672717 48354029355790100143752269)
    ·
      refine ⟨18132761008421287553907101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48354029355790100143752269 18132761008421287553907101)
      ·
        refine ⟨6799785378157982832715163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18132761008421287553907101 6799785378157982832715163)
        ·
          refine ⟨10199678067236974249072745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799785378157982832715163 10199678067236974249072745)
          ·
            refine ⟨7649758550427730686804559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10199678067236974249072745 7649758550427730686804559)
            ·
              refine ⟨11474637825641596030206839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649758550427730686804559 11474637825641596030206839)
              ·
                refine ⟨17211956738462394045310259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11474637825641596030206839 17211956738462394045310259)
                ·
                  refine ⟨25817935107693591067965389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17211956738462394045310259 25817935107693591067965389)
                  ·
                    refine ⟨9681725665385096650487021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25817935107693591067965389 9681725665385096650487021)
                    ·
                      refine ⟨3630647124519411243932633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681725665385096650487021 3630647124519411243932633)
                      ·
                        rfl

theorem cell23_7070660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7070660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070660 prefixEnd_7070660 := by exact prefixLift 7070660
  have htrace : WordTrace (prefixWord ++ tailWord_7070660) baseStart_7070660 baseEnd_7070660 := by
    simpa [prefixWord, tailWord_7070660, baseEnd_7070660] using wordTrace_append hprefix tailTrace_7070660
  have hstable : (prefixWord ++ tailWord_7070660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070660).length < 2 ^ (prefixWord ++ tailWord_7070660).sum := by decide
  have hdescent : baseEnd_7070660 < baseStart_7070660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070790 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7070790 : Nat := 118140960795 + 7070790 * 2 ^ 59
def prefixEnd_7070790 : Nat := 4983230072969 + 3 ^ 40 * 7070790 * 2
def baseEnd_7070790 : Nat := 3630713877004495735307035

theorem tailTrace_7070790 : CollatzResearch.WordTrace tailWord_7070790 prefixEnd_7070790 3630713877004495735307035 := by
  unfold tailWord_7070790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059153064179465613611807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171928598702495266423718549 8059153064179465613611807)
  ·
    refine ⟨12088729596269198420417711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059153064179465613611807 12088729596269198420417711)
    ·
      refine ⟨18133094394403797630626567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12088729596269198420417711 18133094394403797630626567)
      ·
        refine ⟨27199641591605696445939851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133094394403797630626567 27199641591605696445939851)
        ·
          refine ⟨40799462387408544668909777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27199641591605696445939851 40799462387408544668909777)
          ·
            refine ⟨30599596790556408501682333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40799462387408544668909777 30599596790556408501682333)
            ·
              refine ⟨11474848796458653188130875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30599596790556408501682333 11474848796458653188130875)
              ·
                refine ⟨17212273194687979782196313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11474848796458653188130875 17212273194687979782196313)
                ·
                  refine ⟨12909204896015984836647235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17212273194687979782196313 12909204896015984836647235)
                  ·
                    refine ⟨19363807344023977254970853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12909204896015984836647235 19363807344023977254970853)
                    ·
                      refine ⟨3630713877004495735307035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19363807344023977254970853 3630713877004495735307035)
                      ·
                        rfl

theorem cell23_7070790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7070790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070790 prefixEnd_7070790 := by exact prefixLift 7070790
  have htrace : WordTrace (prefixWord ++ tailWord_7070790) baseStart_7070790 baseEnd_7070790 := by
    simpa [prefixWord, tailWord_7070790, baseEnd_7070790] using wordTrace_append hprefix tailTrace_7070790
  have hstable : (prefixWord ++ tailWord_7070790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070790).length < 2 ^ (prefixWord ++ tailWord_7070790).sum := by decide
  have hdescent : baseEnd_7070790 < baseStart_7070790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070809 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_7070809 : Nat := 118140960795 + 7070809 * 2 ^ 59
def prefixEnd_7070809 : Nat := 4983230072969 + 3 ^ 40 * 7070809 * 2
def baseEnd_7070809 : Nat := 1210241211045643720323149

theorem tailTrace_7070809 : CollatzResearch.WordTrace tailWord_7070809 prefixEnd_7070809 1210241211045643720323149 := by
  unfold tailWord_7070809
  simp only [CollatzResearch.WordTrace]
  refine ⟨257893591040674065880519481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171929060693782710587012987 257893591040674065880519481)
  ·
    refine ⟨193420193280505549410389611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257893591040674065880519481 193420193280505549410389611)
    ·
      refine ⟨290130289920758324115584417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193420193280505549410389611 290130289920758324115584417)
      ·
        refine ⟨217597717440568743086688313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290130289920758324115584417 217597717440568743086688313)
        ·
          refine ⟨163198288080426557315016235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217597717440568743086688313 163198288080426557315016235)
          ·
            refine ⟨244797432120639835972524353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163198288080426557315016235 244797432120639835972524353)
            ·
              refine ⟨183598074090479876979393265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244797432120639835972524353 183598074090479876979393265)
              ·
                refine ⟨137698555567859907734544949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183598074090479876979393265 137698555567859907734544949)
                ·
                  refine ⟨12909239584486866350113589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137698555567859907734544949 12909239584486866350113589)
                  ·
                    refine ⟨1210241211045643720323149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12909239584486866350113589 1210241211045643720323149)
                    ·
                      rfl

theorem cell23_7070809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_7070809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070809 prefixEnd_7070809 := by exact prefixLift 7070809
  have htrace : WordTrace (prefixWord ++ tailWord_7070809) baseStart_7070809 baseEnd_7070809 := by
    simpa [prefixWord, tailWord_7070809, baseEnd_7070809] using wordTrace_append hprefix tailTrace_7070809
  have hstable : (prefixWord ++ tailWord_7070809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070809).length < 2 ^ (prefixWord ++ tailWord_7070809).sum := by decide
  have hdescent : baseEnd_7070809 < baseStart_7070809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070813 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 8]
def baseStart_7070813 : Nat := 118140960795 + 7070813 * 2 ^ 59
def prefixEnd_7070813 : Nat := 4983230072969 + 3 ^ 40 * 7070813 * 2
def baseEnd_7070813 : Nat := 403413965228838793924381

theorem tailTrace_7070813 : CollatzResearch.WordTrace tailWord_7070813 prefixEnd_7070813 403413965228838793924381 := by
  unfold tailWord_7070813
  simp only [CollatzResearch.WordTrace]
  refine ⟨257893736932659574563665093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171929157955106383042443395 257893736932659574563665093)
  ·
    refine ⟨48355075674873670230687205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257893736932659574563665093 48355075674873670230687205)
    ·
      refine ⟨9066576689038813168253851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48355075674873670230687205 9066576689038813168253851)
      ·
        refine ⟨13599865033558219752380777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066576689038813168253851 13599865033558219752380777)
        ·
          refine ⟨10199898775168664814285583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13599865033558219752380777 10199898775168664814285583)
          ·
            refine ⟨15299848162752997221428375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10199898775168664814285583 15299848162752997221428375)
            ·
              refine ⟨22949772244129495832142563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15299848162752997221428375 22949772244129495832142563)
              ·
                refine ⟨34424658366194243748213845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22949772244129495832142563 34424658366194243748213845)
                ·
                  refine ⟨403413965228838793924381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34424658366194243748213845 403413965228838793924381)
                  ·
                    rfl

theorem cell23_7070813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_7070813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070813 prefixEnd_7070813 := by exact prefixLift 7070813
  have htrace : WordTrace (prefixWord ++ tailWord_7070813) baseStart_7070813 baseEnd_7070813 := by
    simpa [prefixWord, tailWord_7070813, baseEnd_7070813] using wordTrace_append hprefix tailTrace_7070813
  have hstable : (prefixWord ++ tailWord_7070813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070813).length < 2 ^ (prefixWord ++ tailWord_7070813).sum := by decide
  have hdescent : baseEnd_7070813 < baseStart_7070813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070823 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_7070823 : Nat := 118140960795 + 7070823 * 2 ^ 59
def prefixEnd_7070823 : Nat := 4983230072969 + 3 ^ 40 * 7070823 * 2
def baseEnd_7070823 : Nat := 3630730821866094106194383

theorem tailTrace_7070823 : CollatzResearch.WordTrace tailWord_7070823 prefixEnd_7070823 3630730821866094106194383 := by
  unfold tailWord_7070823
  simp only [CollatzResearch.WordTrace]
  refine ⟨257894101662623346271529123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171929401108415564181019415 257894101662623346271529123)
  ·
    refine ⟨386841152493935019407293685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257894101662623346271529123 386841152493935019407293685)
    ·
      refine ⟨36266358046306408069433783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 386841152493935019407293685 36266358046306408069433783)
      ·
        refine ⟨54399537069459612104150675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36266358046306408069433783 54399537069459612104150675)
        ·
          refine ⟨81599305604189418156226013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54399537069459612104150675 81599305604189418156226013)
          ·
            refine ⟨30599739601571031808584755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81599305604189418156226013 30599739601571031808584755)
            ·
              refine ⟨45899609402356547712877133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30599739601571031808584755 45899609402356547712877133)
              ·
                refine ⟨17212353525883705392328925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45899609402356547712877133 17212353525883705392328925)
                ·
                  refine ⟨6454632572206389522123347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17212353525883705392328925 6454632572206389522123347)
                  ·
                    refine ⟨9681948858309584283185021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454632572206389522123347 9681948858309584283185021)
                    ·
                      refine ⟨3630730821866094106194383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681948858309584283185021 3630730821866094106194383)
                      ·
                        rfl

theorem cell23_7070823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_7070823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070823 prefixEnd_7070823 := by exact prefixLift 7070823
  have htrace : WordTrace (prefixWord ++ tailWord_7070823) baseStart_7070823 baseEnd_7070823 := by
    simpa [prefixWord, tailWord_7070823, baseEnd_7070823] using wordTrace_append hprefix tailTrace_7070823
  have hstable : (prefixWord ++ tailWord_7070823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070823).length < 2 ^ (prefixWord ++ tailWord_7070823).sum := by decide
  have hdescent : baseEnd_7070823 < baseStart_7070823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070857 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 1, 1, 3]
def baseStart_7070857 : Nat := 118140960795 + 7070857 * 2 ^ 59
def prefixEnd_7070857 : Nat := 4983230072969 + 3 ^ 40 * 7070857 * 2
def baseEnd_7070857 : Nat := 3630748280208346973169227

theorem tailTrace_7070857 : CollatzResearch.WordTrace tailWord_7070857 prefixEnd_7070857 3630748280208346973169227 := by
  unfold tailWord_7070857
  simp only [CollatzResearch.WordTrace]
  refine ⟨257895341744500170078266825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171930227829666780052177883 257895341744500170078266825)
  ·
    refine ⟨193421506308375127558700119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257895341744500170078266825 193421506308375127558700119)
    ·
      refine ⟨290132259462562691338050179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193421506308375127558700119 290132259462562691338050179)
      ·
        refine ⟨435198389193844037007075269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290132259462562691338050179 435198389193844037007075269)
        ·
          refine ⟨81599697973845756938826613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435198389193844037007075269 81599697973845756938826613)
          ·
            refine ⟨7649971685048039713014995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81599697973845756938826613 7649971685048039713014995)
            ·
              refine ⟨11474957527572059569522493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649971685048039713014995 11474957527572059569522493)
              ·
                refine ⟨4303109072839522338570935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11474957527572059569522493 4303109072839522338570935)
                ·
                  refine ⟨6454663609259283507856403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303109072839522338570935 6454663609259283507856403)
                  ·
                    refine ⟨9681995413888925261784605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454663609259283507856403 9681995413888925261784605)
                    ·
                      refine ⟨3630748280208346973169227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9681995413888925261784605 3630748280208346973169227)
                      ·
                        rfl

theorem cell23_7070857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 1, 3].length) (baseStart_7070857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070857 prefixEnd_7070857 := by exact prefixLift 7070857
  have htrace : WordTrace (prefixWord ++ tailWord_7070857) baseStart_7070857 baseEnd_7070857 := by
    simpa [prefixWord, tailWord_7070857, baseEnd_7070857] using wordTrace_append hprefix tailTrace_7070857
  have hstable : (prefixWord ++ tailWord_7070857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070857).length < 2 ^ (prefixWord ++ tailWord_7070857).sum := by decide
  have hdescent : baseEnd_7070857 < baseStart_7070857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070874 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7070874 : Nat := 118140960795 + 7070874 * 2 ^ 59
def prefixEnd_7070874 : Nat := 4983230072969 + 3 ^ 40 * 7070874 * 2
def baseEnd_7070874 : Nat := 3630757009379473406656649

theorem tailTrace_7070874 : CollatzResearch.WordTrace tailWord_7070874 prefixEnd_7070874 3630757009379473406656649 := by
  unfold tailWord_7070874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64473990446359645495408919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171930641190292387987757117 64473990446359645495408919)
  ·
    refine ⟨96710985669539468243113379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64473990446359645495408919 96710985669539468243113379)
    ·
      refine ⟨145066478504309202364670069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96710985669539468243113379 145066478504309202364670069)
      ·
        refine ⟨13599982359778987721687819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145066478504309202364670069 13599982359778987721687819)
        ·
          refine ⟨20399973539668481582531729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13599982359778987721687819 20399973539668481582531729)
          ·
            refine ⟨15299980154751361186898797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20399973539668481582531729 15299980154751361186898797)
            ·
              refine ⟨5737492558031760445087049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15299980154751361186898797 5737492558031760445087049)
              ·
                refine ⟨4303119418523820333815287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737492558031760445087049 4303119418523820333815287)
                ·
                  refine ⟨6454679127785730500722931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303119418523820333815287 6454679127785730500722931)
                  ·
                    refine ⟨9682018691678595751084397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454679127785730500722931 9682018691678595751084397)
                    ·
                      refine ⟨3630757009379473406656649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682018691678595751084397 3630757009379473406656649)
                      ·
                        rfl

theorem cell23_7070874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7070874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070874 prefixEnd_7070874 := by exact prefixLift 7070874
  have htrace : WordTrace (prefixWord ++ tailWord_7070874) baseStart_7070874 baseEnd_7070874 := by
    simpa [prefixWord, tailWord_7070874, baseEnd_7070874] using wordTrace_append hprefix tailTrace_7070874
  have hstable : (prefixWord ++ tailWord_7070874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070874).length < 2 ^ (prefixWord ++ tailWord_7070874).sum := by decide
  have hdescent : baseEnd_7070874 < baseStart_7070874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070876 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7070876 : Nat := 118140960795 + 7070876 * 2 ^ 59
def prefixEnd_7070876 : Nat := 4983230072969 + 3 ^ 40 * 7070876 * 2
def baseEnd_7070876 : Nat := 3630758036340782398831639

theorem tailTrace_7070876 : CollatzResearch.WordTrace tailWord_7070876 prefixEnd_7070876 3630758036340782398831639 := by
  unfold tailWord_7070876
  simp only [CollatzResearch.WordTrace]
  refine ⟨128948017365715668161604241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171930689820954224215472321 128948017365715668161604241)
  ·
    refine ⟨96711013024286751121203181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128948017365715668161604241 96711013024286751121203181)
    ·
      refine ⟨36266629884107531670451193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96711013024286751121203181 36266629884107531670451193)
      ·
        refine ⟨27199972413080648752838395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36266629884107531670451193 27199972413080648752838395)
        ·
          refine ⟨40799958619620973129257593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27199972413080648752838395 40799958619620973129257593)
          ·
            refine ⟨30599968964715729846943195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40799958619620973129257593 30599968964715729846943195)
            ·
              refine ⟨45899953447073594770414793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30599968964715729846943195 45899953447073594770414793)
              ·
                refine ⟨34424965085305196077811095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45899953447073594770414793 34424965085305196077811095)
                ·
                  refine ⟨51637447627957794116716643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34424965085305196077811095 51637447627957794116716643)
                  ·
                    refine ⟨77456171441936691175074965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51637447627957794116716643 77456171441936691175074965)
                    ·
                      refine ⟨3630758036340782398831639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77456171441936691175074965 3630758036340782398831639)
                      ·
                        rfl

theorem cell23_7070876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7070876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070876 prefixEnd_7070876 := by exact prefixLift 7070876
  have htrace : WordTrace (prefixWord ++ tailWord_7070876) baseStart_7070876 baseEnd_7070876 := by
    simpa [prefixWord, tailWord_7070876, baseEnd_7070876] using wordTrace_append hprefix tailTrace_7070876
  have hstable : (prefixWord ++ tailWord_7070876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070876).length < 2 ^ (prefixWord ++ tailWord_7070876).sum := by decide
  have hdescent : baseEnd_7070876 < baseStart_7070876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070925 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7070925 : Nat := 118140960795 + 7070925 * 2 ^ 59
def prefixEnd_7070925 : Nat := 4983230072969 + 3 ^ 40 * 7070925 * 2
def baseEnd_7070925 : Nat := 3630783196892852707118915

theorem tailTrace_7070925 : CollatzResearch.WordTrace tailWord_7070925 prefixEnd_7070925 3630783196892852707118915 := by
  unfold tailWord_7070925
  simp only [CollatzResearch.WordTrace]
  refine ⟨257897821908253817691742229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171931881272169211794494819 257897821908253817691742229)
  ·
    refine ⟨12088960401949397704300417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 257897821908253817691742229 12088960401949397704300417)
    ·
      refine ⟨9066720301462048278225313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12088960401949397704300417 9066720301462048278225313)
      ·
        refine ⟨6800040226096536208668985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9066720301462048278225313 6800040226096536208668985)
        ·
          refine ⟨5100030169572402156501739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6800040226096536208668985 5100030169572402156501739)
          ·
            refine ⟨7650045254358603234752609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100030169572402156501739 7650045254358603234752609)
            ·
              refine ⟨5737533940768952426064457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7650045254358603234752609 5737533940768952426064457)
              ·
                refine ⟨4303150455576714319548343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737533940768952426064457 4303150455576714319548343)
                ·
                  refine ⟨6454725683365071479322515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303150455576714319548343 6454725683365071479322515)
                  ·
                    refine ⟨9682088525047607218983773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454725683365071479322515 9682088525047607218983773)
                    ·
                      refine ⟨3630783196892852707118915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682088525047607218983773 3630783196892852707118915)
                      ·
                        rfl

theorem cell23_7070925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7070925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070925 prefixEnd_7070925 := by exact prefixLift 7070925
  have htrace : WordTrace (prefixWord ++ tailWord_7070925) baseStart_7070925 baseEnd_7070925 := by
    simpa [prefixWord, tailWord_7070925, baseEnd_7070925] using wordTrace_append hprefix tailTrace_7070925
  have hstable : (prefixWord ++ tailWord_7070925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070925).length < 2 ^ (prefixWord ++ tailWord_7070925).sum := by decide
  have hdescent : baseEnd_7070925 < baseStart_7070925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070970 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_7070970 : Nat := 118140960795 + 7070970 * 2 ^ 59
def prefixEnd_7070970 : Nat := 4983230072969 + 3 ^ 40 * 7070970 * 2
def baseEnd_7070970 : Nat := 3630806303522305031056207

theorem tailTrace_7070970 : CollatzResearch.WordTrace tailWord_7070970 prefixEnd_7070970 3630806303522305031056207 := by
  unfold tailWord_7070970
  simp only [CollatzResearch.WordTrace]
  refine ⟨64474865798272697594282591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171932975462060526918086909 64474865798272697594282591)
  ·
    refine ⟨96712298697409046391423887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64474865798272697594282591 96712298697409046391423887)
    ·
      refine ⟨145068448046113569587135831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96712298697409046391423887 145068448046113569587135831)
      ·
        refine ⟨217602672069170354380703747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145068448046113569587135831 217602672069170354380703747)
        ·
          refine ⟨326404008103755531571055621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217602672069170354380703747 326404008103755531571055621)
          ·
            refine ⟨61200751519454162169572929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326404008103755531571055621 61200751519454162169572929)
            ·
              refine ⟨45900563639590621627179697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61200751519454162169572929 45900563639590621627179697)
              ·
                refine ⟨34425422729692966220384773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45900563639590621627179697 34425422729692966220384773)
                ·
                  refine ⟨6454766761817431166322145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34425422729692966220384773 6454766761817431166322145)
                  ·
                    refine ⟨4841075071363073374741609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6454766761817431166322145 4841075071363073374741609)
                    ·
                      refine ⟨3630806303522305031056207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841075071363073374741609 3630806303522305031056207)
                      ·
                        rfl

theorem cell23_7070970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_7070970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070970 prefixEnd_7070970 := by exact prefixLift 7070970
  have htrace : WordTrace (prefixWord ++ tailWord_7070970) baseStart_7070970 baseEnd_7070970 := by
    simpa [prefixWord, tailWord_7070970, baseEnd_7070970] using wordTrace_append hprefix tailTrace_7070970
  have hstable : (prefixWord ++ tailWord_7070970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070970).length < 2 ^ (prefixWord ++ tailWord_7070970).sum := by decide
  have hdescent : baseEnd_7070970 < baseStart_7070970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070974 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_7070974 : Nat := 118140960795 + 7070974 * 2 ^ 59
def prefixEnd_7070974 : Nat := 4983230072969 + 3 ^ 40 * 7070974 * 2
def baseEnd_7070974 : Nat := 3630808357444923015406189

theorem tailTrace_7070974 : CollatzResearch.WordTrace tailWord_7070974 prefixEnd_7070974 3630808357444923015406189 := by
  unfold tailWord_7070974
  simp only [CollatzResearch.WordTrace]
  refine ⟨32237451135634537382534497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171933072723384199373517317 32237451135634537382534497)
  ·
    refine ⟨24178088351725903036900873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32237451135634537382534497 24178088351725903036900873)
    ·
      refine ⟨18133566263794427277675655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24178088351725903036900873 18133566263794427277675655)
      ·
        refine ⟨27200349395691640916513483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133566263794427277675655 27200349395691640916513483)
        ·
          refine ⟨40800524093537461374770225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200349395691640916513483 40800524093537461374770225)
          ·
            refine ⟨30600393070153096031077669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40800524093537461374770225 30600393070153096031077669)
            ·
              refine ⟨5737573700653705505827063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30600393070153096031077669 5737573700653705505827063)
              ·
                refine ⟨8606360550980558258740595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737573700653705505827063 8606360550980558258740595)
                ·
                  refine ⟨12909540826470837388110893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8606360550980558258740595 12909540826470837388110893)
                  ·
                    refine ⟨4841077809926564020541585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12909540826470837388110893 4841077809926564020541585)
                    ·
                      refine ⟨3630808357444923015406189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841077809926564020541585 3630808357444923015406189)
                      ·
                        rfl

theorem cell23_7070974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_7070974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070974 prefixEnd_7070974 := by exact prefixLift 7070974
  have htrace : WordTrace (prefixWord ++ tailWord_7070974) baseStart_7070974 baseEnd_7070974 := by
    simpa [prefixWord, tailWord_7070974, baseEnd_7070974] using wordTrace_append hprefix tailTrace_7070974
  have hstable : (prefixWord ++ tailWord_7070974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070974).length < 2 ^ (prefixWord ++ tailWord_7070974).sum := by decide
  have hdescent : baseEnd_7070974 < baseStart_7070974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070987 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 2, 2, 2]
def baseStart_7070987 : Nat := 118140960795 + 7070987 * 2 ^ 59
def prefixEnd_7070987 : Nat := 4983230072969 + 3 ^ 40 * 7070987 * 2
def baseEnd_7070987 : Nat := 3630815032693431464543629

theorem tailTrace_7070987 : CollatzResearch.WordTrace tailWord_7070987 prefixEnd_7070987 3630815032693431464543629 := by
  unfold tailWord_7070987
  simp only [CollatzResearch.WordTrace]
  refine ⟨257900083234029202280499215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171933388822686134853666143 257900083234029202280499215)
  ·
    refine ⟨386850124851043803420748823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257900083234029202280499215 386850124851043803420748823)
    ·
      refine ⟨580275187276565705131123235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386850124851043803420748823 580275187276565705131123235)
      ·
        refine ⟨870412780914848557696684853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580275187276565705131123235 870412780914848557696684853)
        ·
          refine ⟨81601198210767052284064205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 870412780914848557696684853 81601198210767052284064205)
          ·
            refine ⟨30600449329037644606524077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81601198210767052284064205 30600449329037644606524077)
            ·
              refine ⟨11475168498389116727446529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30600449329037644606524077 11475168498389116727446529)
              ·
                refine ⟨8606376373791837545584897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11475168498389116727446529 8606376373791837545584897)
                ·
                  refine ⟨6454782280343878159188673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8606376373791837545584897 6454782280343878159188673)
                  ·
                    refine ⟨4841086710257908619391505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6454782280343878159188673 4841086710257908619391505)
                    ·
                      refine ⟨3630815032693431464543629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841086710257908619391505 3630815032693431464543629)
                      ·
                        rfl

theorem cell23_7070987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2, 2].length) (baseStart_7070987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070987 prefixEnd_7070987 := by exact prefixLift 7070987
  have htrace : WordTrace (prefixWord ++ tailWord_7070987) baseStart_7070987 baseEnd_7070987 := by
    simpa [prefixWord, tailWord_7070987, baseEnd_7070987] using wordTrace_append hprefix tailTrace_7070987
  have hstable : (prefixWord ++ tailWord_7070987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070987).length < 2 ^ (prefixWord ++ tailWord_7070987).sum := by decide
  have hdescent : baseEnd_7070987 < baseStart_7070987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7070993 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 5]
def baseStart_7070993 : Nat := 118140960795 + 7070993 * 2 ^ 59
def prefixEnd_7070993 : Nat := 4983230072969 + 3 ^ 40 * 7070993 * 2
def baseEnd_7070993 : Nat := 403424234841928715674289

theorem tailTrace_7070993 : CollatzResearch.WordTrace tailWord_7070993 prefixEnd_7070993 403424234841928715674289 := by
  unfold tailWord_7070993
  simp only [CollatzResearch.WordTrace]
  refine ⟨257900302072007465305217633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171933534714671643536811755 257900302072007465305217633)
  ·
    refine ⟨193425226554005598978913225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257900302072007465305217633 193425226554005598978913225)
    ·
      refine ⟨145068919915504199234184919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193425226554005598978913225 145068919915504199234184919)
      ·
        refine ⟨217603379873256298851277379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145068919915504199234184919 217603379873256298851277379)
        ·
          refine ⟨326405069809884448276916069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217603379873256298851277379 326405069809884448276916069)
          ·
            refine ⟨61200950589353334051921763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326405069809884448276916069 61200950589353334051921763)
            ·
              refine ⟨91801425884030001077882645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61200950589353334051921763 91801425884030001077882645)
              ·
                refine ⟨4303191838313906300525749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91801425884030001077882645 4303191838313906300525749)
                ·
                  refine ⟨403424234841928715674289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303191838313906300525749 403424234841928715674289)
                  ·
                    rfl

theorem cell23_7070993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 5].length) (baseStart_7070993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7070993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7070993 prefixEnd_7070993 := by exact prefixLift 7070993
  have htrace : WordTrace (prefixWord ++ tailWord_7070993) baseStart_7070993 baseEnd_7070993 := by
    simpa [prefixWord, tailWord_7070993, baseEnd_7070993] using wordTrace_append hprefix tailTrace_7070993
  have hstable : (prefixWord ++ tailWord_7070993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7070993).length < 2 ^ (prefixWord ++ tailWord_7070993).sum := by decide
  have hdescent : baseEnd_7070993 < baseStart_7070993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7070993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071044 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 5]
def baseStart_7071044 : Nat := 118140960795 + 7071044 * 2 ^ 59
def prefixEnd_7071044 : Nat := 4983230072969 + 3 ^ 40 * 7071044 * 2
def baseEnd_7071044 : Nat := 403427144565637526836763

theorem tailTrace_7071044 : CollatzResearch.WordTrace tailWord_7071044 prefixEnd_7071044 403427144565637526836763 := by
  unfold tailWord_7071044
  simp only [CollatzResearch.WordTrace]
  refine ⟨128951081097411350507662093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171934774796548467343549457 128951081097411350507662093)
  ·
    refine ⟨48356655411529256440373285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128951081097411350507662093 48356655411529256440373285)
    ·
      refine ⟨9066872889661735582569991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48356655411529256440373285 9066872889661735582569991)
      ·
        refine ⟨13600309334492603373854987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066872889661735582569991 13600309334492603373854987)
        ·
          refine ⟨20400464001738905060782481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13600309334492603373854987 20400464001738905060782481)
          ·
            refine ⟨15300348001304178795586861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20400464001738905060782481 15300348001304178795586861)
            ·
              refine ⟨5737630500489067048345073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15300348001304178795586861 5737630500489067048345073)
              ·
                refine ⟨4303222875366800286258805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737630500489067048345073 4303222875366800286258805)
                ·
                  refine ⟨403427144565637526836763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303222875366800286258805 403427144565637526836763)
                  ·
                    rfl

theorem cell23_7071044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_7071044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071044 prefixEnd_7071044 := by exact prefixLift 7071044
  have htrace : WordTrace (prefixWord ++ tailWord_7071044) baseStart_7071044 baseEnd_7071044 := by
    simpa [prefixWord, tailWord_7071044, baseEnd_7071044] using wordTrace_append hprefix tailTrace_7071044
  have hstable : (prefixWord ++ tailWord_7071044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071044).length < 2 ^ (prefixWord ++ tailWord_7071044).sum := by decide
  have hdescent : baseEnd_7071044 < baseStart_7071044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071060 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_7071060 : Nat := 118140960795 + 7071060 * 2 ^ 59
def prefixEnd_7071060 : Nat := 4983230072969 + 3 ^ 40 * 7071060 * 2
def baseEnd_7071060 : Nat := 3630852516781209678930793

theorem tailTrace_7071060 : CollatzResearch.WordTrace tailWord_7071060 prefixEnd_7071060 3630852516781209678930793 := by
  unfold tailWord_7071060
  simp only [CollatzResearch.WordTrace]
  refine ⟨128951372881382367873953317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171935163841843157165271089 128951372881382367873953317)
  ·
    refine ⟨24178382415259193976366247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128951372881382367873953317 24178382415259193976366247)
    ·
      refine ⟨36267573622888790964549371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24178382415259193976366247 36267573622888790964549371)
      ·
        refine ⟨54401360434333186446824057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36267573622888790964549371 54401360434333186446824057)
        ·
          refine ⟨40801020325749889835118043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54401360434333186446824057 40801020325749889835118043)
          ·
            refine ⟨61201530488624834752677065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40801020325749889835118043 61201530488624834752677065)
            ·
              refine ⟨45901147866468626064507799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61201530488624834752677065 45901147866468626064507799)
              ·
                refine ⟨68851721799702939096761699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45901147866468626064507799 68851721799702939096761699)
                ·
                  refine ⟨103277582699554408645142549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68851721799702939096761699 103277582699554408645142549)
                  ·
                    refine ⟨4841136689041612905241057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103277582699554408645142549 4841136689041612905241057)
                    ·
                      refine ⟨3630852516781209678930793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841136689041612905241057 3630852516781209678930793)
                      ·
                        rfl

theorem cell23_7071060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_7071060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071060 prefixEnd_7071060 := by exact prefixLift 7071060
  have htrace : WordTrace (prefixWord ++ tailWord_7071060) baseStart_7071060 baseEnd_7071060 := by
    simpa [prefixWord, tailWord_7071060, baseEnd_7071060] using wordTrace_append hprefix tailTrace_7071060
  have hstable : (prefixWord ++ tailWord_7071060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071060).length < 2 ^ (prefixWord ++ tailWord_7071060).sum := by decide
  have hdescent : baseEnd_7071060 < baseStart_7071060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071130 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_7071130 : Nat := 118140960795 + 7071130 * 2 ^ 59
def prefixEnd_7071130 : Nat := 4983230072969 + 3 ^ 40 * 7071130 * 2
def baseEnd_7071130 : Nat := 1210296153475674801685157

theorem tailTrace_7071130 : CollatzResearch.WordTrace tailWord_7071130 prefixEnd_7071130 1210296153475674801685157 := by
  unfold tailWord_7071130
  simp only [CollatzResearch.WordTrace]
  refine ⟨64476324718127784425738711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171936865915007425135303229 64476324718127784425738711)
  ·
    refine ⟨96714487077191676638608067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64476324718127784425738711 96714487077191676638608067)
    ·
      refine ⟨145071730615787514957912101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96714487077191676638608067 145071730615787514957912101)
      ·
        refine ⟨27200949490460159054608519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145071730615787514957912101 27200949490460159054608519)
        ·
          refine ⟨40801424235690238581912779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200949490460159054608519 40801424235690238581912779)
          ·
            refine ⟨61202136353535357872869169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40801424235690238581912779 61202136353535357872869169)
            ·
              refine ⟨45901602265151518404651877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61202136353535357872869169 45901602265151518404651877)
              ·
                refine ⟨8606550424715909700872227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45901602265151518404651877 8606550424715909700872227)
                ·
                  refine ⟨12909825637073864551308341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8606550424715909700872227 12909825637073864551308341)
                  ·
                    refine ⟨1210296153475674801685157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12909825637073864551308341 1210296153475674801685157)
                    ·
                      rfl

theorem cell23_7071130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_7071130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071130 prefixEnd_7071130 := by exact prefixLift 7071130
  have htrace : WordTrace (prefixWord ++ tailWord_7071130) baseStart_7071130 baseEnd_7071130 := by
    simpa [prefixWord, tailWord_7071130, baseEnd_7071130] using wordTrace_append hprefix tailTrace_7071130
  have hstable : (prefixWord ++ tailWord_7071130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071130).length < 2 ^ (prefixWord ++ tailWord_7071130).sum := by decide
  have hdescent : baseEnd_7071130 < baseStart_7071130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071180 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7071180 : Nat := 118140960795 + 7071180 * 2 ^ 59
def prefixEnd_7071180 : Nat := 4983230072969 + 3 ^ 40 * 7071180 * 2
def baseEnd_7071180 : Nat := 3630914134459749209430241

theorem tailTrace_7071180 : CollatzResearch.WordTrace tailWord_7071180 prefixEnd_7071180 3630914134459749209430241 := by
  unfold tailWord_7071180
  simp only [CollatzResearch.WordTrace]
  refine ⟨128953561261164998121137497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171938081681553330828183329 128953561261164998121137497)
  ·
    refine ⟨96715170945873748590853123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128953561261164998121137497 96715170945873748590853123)
    ·
      refine ⟨145072756418810622886279685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96715170945873748590853123 145072756418810622886279685)
      ·
        refine ⟨27201141828526991791177441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145072756418810622886279685 27201141828526991791177441)
        ·
          refine ⟨20400856371395243843383081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27201141828526991791177441 20400856371395243843383081)
          ·
            refine ⟨15300642278546432882537311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20400856371395243843383081 15300642278546432882537311)
            ·
              refine ⟨22950963417819649323805967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15300642278546432882537311 22950963417819649323805967)
              ·
                refine ⟨34426445126729473985708951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22950963417819649323805967 34426445126729473985708951)
                ·
                  refine ⟨51639667690094210978563427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34426445126729473985708951 51639667690094210978563427)
                  ·
                    refine ⟨77459501535141316467845141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51639667690094210978563427 77459501535141316467845141)
                    ·
                      refine ⟨3630914134459749209430241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77459501535141316467845141 3630914134459749209430241)
                      ·
                        rfl

theorem cell23_7071180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7071180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071180 prefixEnd_7071180 := by exact prefixLift 7071180
  have htrace : WordTrace (prefixWord ++ tailWord_7071180) baseStart_7071180 baseEnd_7071180 := by
    simpa [prefixWord, tailWord_7071180, baseEnd_7071180] using wordTrace_append hprefix tailTrace_7071180
  have hstable : (prefixWord ++ tailWord_7071180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071180).length < 2 ^ (prefixWord ++ tailWord_7071180).sum := by decide
  have hdescent : baseEnd_7071180 < baseStart_7071180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071201 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_7071201 : Nat := 118140960795 + 7071201 * 2 ^ 59
def prefixEnd_7071201 : Nat := 4983230072969 + 3 ^ 40 * 7071201 * 2
def baseEnd_7071201 : Nat := 3630924917553493627267645

theorem tailTrace_7071201 : CollatzResearch.WordTrace tailWord_7071201 prefixEnd_7071201 3630924917553493627267645 := by
  unfold tailWord_7071201
  simp only [CollatzResearch.WordTrace]
  refine ⟨257907888455253916828789457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171938592303502611219192971 257907888455253916828789457)
  ·
    refine ⟨193430916341440437621592093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257907888455253916828789457 193430916341440437621592093)
    ·
      refine ⟨72536593628040164108097035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193430916341440437621592093 72536593628040164108097035)
      ·
        refine ⟨108804890442060246162145553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72536593628040164108097035 108804890442060246162145553)
        ·
          refine ⟨81603667831545184621609165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108804890442060246162145553 81603667831545184621609165)
          ·
            refine ⟨30601375436829444233103437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81603667831545184621609165 30601375436829444233103437)
            ·
              refine ⟨11475515788811041587413789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30601375436829444233103437 11475515788811041587413789)
              ·
                refine ⟨4303318420804140595280171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11475515788811041587413789 4303318420804140595280171)
                ·
                  refine ⟨6454977631206210892920257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303318420804140595280171 6454977631206210892920257)
                  ·
                    refine ⟨4841233223404658169690193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6454977631206210892920257 4841233223404658169690193)
                    ·
                      refine ⟨3630924917553493627267645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841233223404658169690193 3630924917553493627267645)
                      ·
                        rfl

theorem cell23_7071201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_7071201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071201 prefixEnd_7071201 := by exact prefixLift 7071201
  have htrace : WordTrace (prefixWord ++ tailWord_7071201) baseStart_7071201 baseEnd_7071201 := by
    simpa [prefixWord, tailWord_7071201, baseEnd_7071201] using wordTrace_append hprefix tailTrace_7071201
  have hstable : (prefixWord ++ tailWord_7071201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071201).length < 2 ^ (prefixWord ++ tailWord_7071201).sum := by decide
  have hdescent : baseEnd_7071201 < baseStart_7071201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071217 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_7071217 : Nat := 118140960795 + 7071217 * 2 ^ 59
def prefixEnd_7071217 : Nat := 4983230072969 + 3 ^ 40 * 7071217 * 2
def baseEnd_7071217 : Nat := 3630933133243965564667571

theorem tailTrace_7071217 : CollatzResearch.WordTrace tailWord_7071217 prefixEnd_7071217 3630933133243965564667571 := by
  unfold tailWord_7071217
  simp only [CollatzResearch.WordTrace]
  refine ⟨257908472023195951561371905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171938981348797301040914603 257908472023195951561371905)
  ·
    refine ⟨193431354017396963671028929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257908472023195951561371905 193431354017396963671028929)
    ·
      refine ⟨145073515513047722753271697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193431354017396963671028929 145073515513047722753271697)
      ·
        refine ⟨108805136634785792064953773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145073515513047722753271697 108805136634785792064953773)
        ·
          refine ⟨40801926238044672024357665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108805136634785792064953773 40801926238044672024357665)
          ·
            refine ⟨30601444678533504018268249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40801926238044672024357665 30601444678533504018268249)
            ·
              refine ⟨22951083508900128013701187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30601444678533504018268249 22951083508900128013701187)
              ·
                refine ⟨34426625263350192020551781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22951083508900128013701187 34426625263350192020551781)
                ·
                  refine ⟨6454992236878161003853459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34426625263350192020551781 6454992236878161003853459)
                  ·
                    refine ⟨9682488355317241505780189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6454992236878161003853459 9682488355317241505780189)
                    ·
                      refine ⟨3630933133243965564667571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682488355317241505780189 3630933133243965564667571)
                      ·
                        rfl

theorem cell23_7071217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_7071217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071217 prefixEnd_7071217 := by exact prefixLift 7071217
  have htrace : WordTrace (prefixWord ++ tailWord_7071217) baseStart_7071217 baseEnd_7071217 := by
    simpa [prefixWord, tailWord_7071217, baseEnd_7071217] using wordTrace_append hprefix tailTrace_7071217
  have hstable : (prefixWord ++ tailWord_7071217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071217).length < 2 ^ (prefixWord ++ tailWord_7071217).sum := by decide
  have hdescent : baseEnd_7071217 < baseStart_7071217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071238 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7071238 : Nat := 118140960795 + 7071238 * 2 ^ 59
def prefixEnd_7071238 : Nat := 4983230072969 + 3 ^ 40 * 7071238 * 2
def baseEnd_7071238 : Nat := 3630943916337709982504975

theorem tailTrace_7071238 : CollatzResearch.WordTrace tailWord_7071238 prefixEnd_7071238 3630943916337709982504975 := by
  unfold tailWord_7071238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059663686128746004621449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 171939491970746581431924245 8059663686128746004621449)
  ·
    refine ⟨6044747764596559503466087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8059663686128746004621449 6044747764596559503466087)
    ·
      refine ⟨9067121646894839255199131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6044747764596559503466087 9067121646894839255199131)
      ·
        refine ⟨13600682470342258882798697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9067121646894839255199131 13600682470342258882798697)
        ·
          refine ⟨10200511852756694162099023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13600682470342258882798697 10200511852756694162099023)
          ·
            refine ⟨15300767779135041243148535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200511852756694162099023 15300767779135041243148535)
            ·
              refine ⟨22951151668702561864722803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15300767779135041243148535 22951151668702561864722803)
              ·
                refine ⟨34426727503053842797084205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22951151668702561864722803 34426727503053842797084205)
                ·
                  refine ⟨12910022813645191048906577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34426727503053842797084205 12910022813645191048906577)
                  ·
                    refine ⟨9682517110233893286679933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12910022813645191048906577 9682517110233893286679933)
                    ·
                      refine ⟨3630943916337709982504975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682517110233893286679933 3630943916337709982504975)
                      ·
                        rfl

theorem cell23_7071238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7071238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071238 prefixEnd_7071238 := by exact prefixLift 7071238
  have htrace : WordTrace (prefixWord ++ tailWord_7071238) baseStart_7071238 baseEnd_7071238 := by
    simpa [prefixWord, tailWord_7071238, baseEnd_7071238] using wordTrace_append hprefix tailTrace_7071238
  have hstable : (prefixWord ++ tailWord_7071238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071238).length < 2 ^ (prefixWord ++ tailWord_7071238).sum := by decide
  have hdescent : baseEnd_7071238 < baseStart_7071238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071244 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_7071244 : Nat := 118140960795 + 7071244 * 2 ^ 59
def prefixEnd_7071244 : Nat := 4983230072969 + 3 ^ 40 * 7071244 * 2
def baseEnd_7071244 : Nat := 3630946997221636959029947

theorem tailTrace_7071244 : CollatzResearch.WordTrace tailWord_7071244 prefixEnd_7071244 3630946997221636959029947 := by
  unfold tailWord_7071244
  simp only [CollatzResearch.WordTrace]
  refine ⟨128954728397049067586302393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171939637862732090115069857 128954728397049067586302393)
  ·
    refine ⟨96716046297786800689726795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128954728397049067586302393 96716046297786800689726795)
    ·
      refine ⟨145074069446680201034590193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96716046297786800689726795 145074069446680201034590193)
      ·
        refine ⟨108805552085010150775942645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145074069446680201034590193 108805552085010150775942645)
        ·
          refine ⟨10200520507969701635244623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108805552085010150775942645 10200520507969701635244623)
          ·
            refine ⟨15300780761954552452866935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200520507969701635244623 15300780761954552452866935)
            ·
              refine ⟨22951171142931828679300403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15300780761954552452866935 22951171142931828679300403)
              ·
                refine ⟨34426756714397743018950605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22951171142931828679300403 34426756714397743018950605)
                ·
                  refine ⟨12910033767899153632106477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34426756714397743018950605 12910033767899153632106477)
                  ·
                    refine ⟨4841262662962182612039929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12910033767899153632106477 4841262662962182612039929)
                    ·
                      refine ⟨3630946997221636959029947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841262662962182612039929 3630946997221636959029947)
                      ·
                        rfl

theorem cell23_7071244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_7071244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071244 prefixEnd_7071244 := by exact prefixLift 7071244
  have htrace : WordTrace (prefixWord ++ tailWord_7071244) baseStart_7071244 baseEnd_7071244 := by
    simpa [prefixWord, tailWord_7071244, baseEnd_7071244] using wordTrace_append hprefix tailTrace_7071244
  have hstable : (prefixWord ++ tailWord_7071244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071244).length < 2 ^ (prefixWord ++ tailWord_7071244).sum := by decide
  have hdescent : baseEnd_7071244 < baseStart_7071244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071260 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7071260 : Nat := 118140960795 + 7071260 * 2 ^ 59
def prefixEnd_7071260 : Nat := 4983230072969 + 3 ^ 40 * 7071260 * 2
def baseEnd_7071260 : Nat := 3630955212912108896429873

theorem tailTrace_7071260 : CollatzResearch.WordTrace tailWord_7071260 prefixEnd_7071260 3630955212912108896429873 := by
  unfold tailWord_7071260
  simp only [CollatzResearch.WordTrace]
  refine ⟨128955020181020084952593617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171940026908026779936791489 128955020181020084952593617)
  ·
    refine ⟨96716265135765063714445213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128955020181020084952593617 96716265135765063714445213)
    ·
      refine ⟨36268599425911898892916955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96716265135765063714445213 36268599425911898892916955)
      ·
        refine ⟨54402899138867848339375433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36268599425911898892916955 54402899138867848339375433)
        ·
          refine ⟨40802174354150886254531575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54402899138867848339375433 40802174354150886254531575)
          ·
            refine ⟨61203261531226329381797363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40802174354150886254531575 61203261531226329381797363)
            ·
              refine ⟨91804892296839494072696045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61203261531226329381797363 91804892296839494072696045)
              ·
                refine ⟨34426834611314810277261017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91804892296839494072696045 34426834611314810277261017)
                ·
                  refine ⟨25820125958486107707945763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34426834611314810277261017 25820125958486107707945763)
                  ·
                    refine ⟨38730188937729161561918645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25820125958486107707945763 38730188937729161561918645)
                    ·
                      refine ⟨3630955212912108896429873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38730188937729161561918645 3630955212912108896429873)
                      ·
                        rfl

theorem cell23_7071260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7071260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071260 prefixEnd_7071260 := by exact prefixLift 7071260
  have htrace : WordTrace (prefixWord ++ tailWord_7071260) baseStart_7071260 baseEnd_7071260 := by
    simpa [prefixWord, tailWord_7071260, baseEnd_7071260] using wordTrace_append hprefix tailTrace_7071260
  have hstable : (prefixWord ++ tailWord_7071260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071260).length < 2 ^ (prefixWord ++ tailWord_7071260).sum := by decide
  have hdescent : baseEnd_7071260 < baseStart_7071260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071261 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_7071261 : Nat := 118140960795 + 7071261 * 2 ^ 59
def prefixEnd_7071261 : Nat := 4983230072969 + 3 ^ 40 * 7071261 * 2
def baseEnd_7071261 : Nat := 3630955726392763392517369

theorem tailTrace_7071261 : CollatzResearch.WordTrace tailWord_7071261 prefixEnd_7071261 3630955726392763392517369 := by
  unfold tailWord_7071261
  simp only [CollatzResearch.WordTrace]
  refine ⟨257910076835036547075973637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171940051223357698050649091 257910076835036547075973637)
  ·
    refine ⟨48358139406569352576745057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257910076835036547075973637 48358139406569352576745057)
    ·
      refine ⟨36268604554927014432558793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48358139406569352576745057 36268604554927014432558793)
      ·
        refine ⟨27201453416195260824419095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36268604554927014432558793 27201453416195260824419095)
        ·
          refine ⟨40802180124292891236628643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27201453416195260824419095 40802180124292891236628643)
          ·
            refine ⟨61203270186439336854942965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40802180124292891236628643 61203270186439336854942965)
            ·
              refine ⟨5737806579978687830150903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61203270186439336854942965 5737806579978687830150903)
              ·
                refine ⟨8606709869968031745226355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737806579978687830150903 8606709869968031745226355)
                ·
                  refine ⟨12910064804952047617839533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8606709869968031745226355 12910064804952047617839533)
                  ·
                    refine ⟨4841274301857017856689825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12910064804952047617839533 4841274301857017856689825)
                    ·
                      refine ⟨3630955726392763392517369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841274301857017856689825 3630955726392763392517369)
                      ·
                        rfl

theorem cell23_7071261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_7071261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071261 prefixEnd_7071261 := by exact prefixLift 7071261
  have htrace : WordTrace (prefixWord ++ tailWord_7071261) baseStart_7071261 baseEnd_7071261 := by
    simpa [prefixWord, tailWord_7071261, baseEnd_7071261] using wordTrace_append hprefix tailTrace_7071261
  have hstable : (prefixWord ++ tailWord_7071261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071261).length < 2 ^ (prefixWord ++ tailWord_7071261).sum := by decide
  have hdescent : baseEnd_7071261 < baseStart_7071261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071314 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_7071314 : Nat := 118140960795 + 7071314 * 2 ^ 59
def prefixEnd_7071314 : Nat := 4983230072969 + 3 ^ 40 * 7071314 * 2
def baseEnd_7071314 : Nat := 403442548985272409461625

theorem tailTrace_7071314 : CollatzResearch.WordTrace tailWord_7071314 prefixEnd_7071314 403442548985272409461625 := by
  unfold tailWord_7071314
  simp only [CollatzResearch.WordTrace]
  refine ⟨64478002475961134281913249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171941339935896358085101997 64478002475961134281913249)
  ·
    refine ⟨48358501856970850711434937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64478002475961134281913249 48358501856970850711434937)
    ·
      refine ⟨36268876392728138033576203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48358501856970850711434937 36268876392728138033576203)
      ·
        refine ⟨54403314589092207050364305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36268876392728138033576203 54403314589092207050364305)
        ·
          refine ⟨40802485941819155287773229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54403314589092207050364305 40802485941819155287773229)
          ·
            refine ⟨15300932228182183232914961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40802485941819155287773229 15300932228182183232914961)
            ·
              refine ⟨11475699171136637424686221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15300932228182183232914961 11475699171136637424686221)
              ·
                refine ⟨4303387189176239034257333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11475699171136637424686221 4303387189176239034257333)
                ·
                  refine ⟨403442548985272409461625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303387189176239034257333 403442548985272409461625)
                  ·
                    rfl

theorem cell23_7071314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_7071314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071314 prefixEnd_7071314 := by exact prefixLift 7071314
  have htrace : WordTrace (prefixWord ++ tailWord_7071314) baseStart_7071314 baseEnd_7071314 := by
    simpa [prefixWord, tailWord_7071314, baseEnd_7071314] using wordTrace_append hprefix tailTrace_7071314
  have hstable : (prefixWord ++ tailWord_7071314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071314).length < 2 ^ (prefixWord ++ tailWord_7071314).sum := by decide
  have hdescent : baseEnd_7071314 < baseStart_7071314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071360 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_7071360 : Nat := 118140960795 + 7071360 * 2 ^ 59
def prefixEnd_7071360 : Nat := 4983230072969 + 3 ^ 40 * 7071360 * 2
def baseEnd_7071360 : Nat := 3631006560977558505179413

theorem tailTrace_7071360 : CollatzResearch.WordTrace tailWord_7071360 prefixEnd_7071360 3631006560977558505179413 := by
  unfold tailWord_7071360
  simp only [CollatzResearch.WordTrace]
  refine ⟨128956843830838943491913767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171942458441118591322551689 128956843830838943491913767)
  ·
    refine ⟨193435265746258415237870651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128956843830838943491913767 193435265746258415237870651)
    ·
      refine ⟨290152898619387622856805977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193435265746258415237870651 290152898619387622856805977)
      ·
        refine ⟨217614673964540717142604483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290152898619387622856805977 217614673964540717142604483)
        ·
          refine ⟨326422010946811075713906725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217614673964540717142604483 326422010946811075713906725)
          ·
            refine ⟨61204127052527076696357511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326422010946811075713906725 61204127052527076696357511)
            ·
              refine ⟨91806190578790615044536267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61204127052527076696357511 91806190578790615044536267)
              ·
                refine ⟨137709285868185922566804401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91806190578790615044536267 137709285868185922566804401)
                ·
                  refine ⟨103281964401139441925103301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137709285868185922566804401 103281964401139441925103301)
                  ·
                    refine ⟨19365368325213645360956869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103281964401139441925103301 19365368325213645360956869)
                    ·
                      refine ⟨3631006560977558505179413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19365368325213645360956869 3631006560977558505179413)
                      ·
                        rfl

theorem cell23_7071360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_7071360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071360 prefixEnd_7071360 := by exact prefixLift 7071360
  have htrace : WordTrace (prefixWord ++ tailWord_7071360) baseStart_7071360 baseEnd_7071360 := by
    simpa [prefixWord, tailWord_7071360, baseEnd_7071360] using wordTrace_append hprefix tailTrace_7071360
  have hstable : (prefixWord ++ tailWord_7071360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071360).length < 2 ^ (prefixWord ++ tailWord_7071360).sum := by decide
  have hdescent : baseEnd_7071360 < baseStart_7071360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071367 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_7071367 : Nat := 118140960795 + 7071367 * 2 ^ 59
def prefixEnd_7071367 : Nat := 4983230072969 + 3 ^ 40 * 7071367 * 2
def baseEnd_7071367 : Nat := 3631010155342139977791881

theorem tailTrace_7071367 : CollatzResearch.WordTrace tailWord_7071367 prefixEnd_7071367 3631010155342139977791881 := by
  unfold tailWord_7071367
  simp only [CollatzResearch.WordTrace]
  refine ⟨257913942972652527179332355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171942628648435018119554903 257913942972652527179332355)
  ·
    refine ⟨386870914458978790768998533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257913942972652527179332355 386870914458978790768998533)
    ·
      refine ⟨72538296461058523269187225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386870914458978790768998533 72538296461058523269187225)
      ·
        refine ⟨54403722345793892451890419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72538296461058523269187225 54403722345793892451890419)
        ·
          refine ⟨81605583518690838677835629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54403722345793892451890419 81605583518690838677835629)
          ·
            refine ⟨30602093819509064504188361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81605583518690838677835629 30602093819509064504188361)
            ·
              refine ⟨22951570364631798378141271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30602093819509064504188361 22951570364631798378141271)
              ·
                refine ⟨34427355546947697567211907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22951570364631798378141271 34427355546947697567211907)
                ·
                  refine ⟨51641033320421546350817861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34427355546947697567211907 51641033320421546350817861)
                  ·
                    refine ⟨9682693747579039940778349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51641033320421546350817861 9682693747579039940778349)
                    ·
                      refine ⟨3631010155342139977791881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682693747579039940778349 3631010155342139977791881)
                      ·
                        rfl

theorem cell23_7071367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_7071367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071367 prefixEnd_7071367 := by exact prefixLift 7071367
  have htrace : WordTrace (prefixWord ++ tailWord_7071367) baseStart_7071367 baseEnd_7071367 := by
    simpa [prefixWord, tailWord_7071367, baseEnd_7071367] using wordTrace_append hprefix tailTrace_7071367
  have hstable : (prefixWord ++ tailWord_7071367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071367).length < 2 ^ (prefixWord ++ tailWord_7071367).sum := by decide
  have hdescent : baseEnd_7071367 < baseStart_7071367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071384 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7071384 : Nat := 118140960795 + 7071384 * 2 ^ 59
def prefixEnd_7071384 : Nat := 4983230072969 + 3 ^ 40 * 7071384 * 2
def baseEnd_7071384 : Nat := 3631018884513266411279303

theorem tailTrace_7071384 : CollatzResearch.WordTrace tailWord_7071384 prefixEnd_7071384 3631018884513266411279303 := by
  unfold tailWord_7071384
  simp only [CollatzResearch.WordTrace]
  refine ⟨128957281506795469541350603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171943042009060626055134137 128957281506795469541350603)
  ·
    refine ⟨193435922260193204312025905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128957281506795469541350603 193435922260193204312025905)
    ·
      refine ⟨145076941695144903234019429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193435922260193204312025905 145076941695144903234019429)
      ·
        refine ⟨27201926567839669356378643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145076941695144903234019429 27201926567839669356378643)
        ·
          refine ⟨40802889851759504034567965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27201926567839669356378643 40802889851759504034567965)
          ·
            refine ⟨15301083694409814012962987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40802889851759504034567965 15301083694409814012962987)
            ·
              refine ⟨22951625541614721019444481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301083694409814012962987 22951625541614721019444481)
              ·
                refine ⟨17213719156211040764583361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22951625541614721019444481 17213719156211040764583361)
                ·
                  refine ⟨12910289367158280573437521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17213719156211040764583361 12910289367158280573437521)
                  ·
                    refine ⟨9682717025368710430078141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12910289367158280573437521 9682717025368710430078141)
                    ·
                      refine ⟨3631018884513266411279303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682717025368710430078141 3631018884513266411279303)
                      ·
                        rfl

theorem cell23_7071384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7071384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071384 prefixEnd_7071384 := by exact prefixLift 7071384
  have htrace : WordTrace (prefixWord ++ tailWord_7071384) baseStart_7071384 baseEnd_7071384 := by
    simpa [prefixWord, tailWord_7071384, baseEnd_7071384] using wordTrace_append hprefix tailTrace_7071384
  have hstable : (prefixWord ++ tailWord_7071384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071384).length < 2 ^ (prefixWord ++ tailWord_7071384).sum := by decide
  have hdescent : baseEnd_7071384 < baseStart_7071384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071431 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_7071431 : Nat := 118140960795 + 7071431 * 2 ^ 59
def prefixEnd_7071431 : Nat := 4983230072969 + 3 ^ 40 * 7071431 * 2
def baseEnd_7071431 : Nat := 3631043018104027727391587

theorem tailTrace_7071431 : CollatzResearch.WordTrace tailWord_7071431 prefixEnd_7071431 3631043018104027727391587 := by
  unfold tailWord_7071431
  simp only [CollatzResearch.WordTrace]
  refine ⟨257916277244420666109662147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171944184829613777406441431 257916277244420666109662147)
  ·
    refine ⟨386874415866630999164493221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257916277244420666109662147 386874415866630999164493221)
    ·
      refine ⟨72538952974993312343342479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386874415866630999164493221 72538952974993312343342479)
      ·
        refine ⟨108808429462489968515013719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72538952974993312343342479 108808429462489968515013719)
        ·
          refine ⟨163212644193734952772520579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108808429462489968515013719 163212644193734952772520579)
          ·
            refine ⟨244818966290602429158780869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163212644193734952772520579 244818966290602429158780869)
            ·
              refine ⟨45903556179487955467271413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244818966290602429158780869 45903556179487955467271413)
              ·
                refine ⟨4303458391826995825056695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45903556179487955467271413 4303458391826995825056695)
                ·
                  refine ⟨6455187587740493737585043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303458391826995825056695 6455187587740493737585043)
                  ·
                    refine ⟨9682781381610740606377565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6455187587740493737585043 9682781381610740606377565)
                    ·
                      refine ⟨3631043018104027727391587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682781381610740606377565 3631043018104027727391587)
                      ·
                        rfl

theorem cell23_7071431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_7071431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071431 prefixEnd_7071431 := by exact prefixLift 7071431
  have htrace : WordTrace (prefixWord ++ tailWord_7071431) baseStart_7071431 baseEnd_7071431 := by
    simpa [prefixWord, tailWord_7071431, baseEnd_7071431] using wordTrace_append hprefix tailTrace_7071431
  have hstable : (prefixWord ++ tailWord_7071431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071431).length < 2 ^ (prefixWord ++ tailWord_7071431).sum := by decide
  have hdescent : baseEnd_7071431 < baseStart_7071431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071464 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7071464 : Nat := 118140960795 + 7071464 * 2 ^ 59
def prefixEnd_7071464 : Nat := 4983230072969 + 3 ^ 40 * 7071464 * 2
def baseEnd_7071464 : Nat := 1210353320988542032759645

theorem tailTrace_7071464 : CollatzResearch.WordTrace tailWord_7071464 prefixEnd_7071464 1210353320988542032759645 := by
  unfold tailWord_7071464
  simp only [CollatzResearch.WordTrace]
  refine ⟨128958740426650556372806723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171944987235534075163742297 128958740426650556372806723)
  ·
    refine ⟨193438110639975834559210085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128958740426650556372806723 193438110639975834559210085)
    ·
      refine ⟨36269645744995468979851891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193438110639975834559210085 36269645744995468979851891)
      ·
        refine ⟨54404468617493203469777837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36269645744995468979851891 54404468617493203469777837)
        ·
          refine ⟨20401675731559951301166689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54404468617493203469777837 20401675731559951301166689)
          ·
            refine ⟨15301256798669963475875017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20401675731559951301166689 15301256798669963475875017)
            ·
              refine ⟨11475942599002472606906263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15301256798669963475875017 11475942599002472606906263)
              ·
                refine ⟨17213913898503708910359395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11475942599002472606906263 17213913898503708910359395)
                ·
                  refine ⟨25820870847755563365539093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17213913898503708910359395 25820870847755563365539093)
                  ·
                    refine ⟨1210353320988542032759645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25820870847755563365539093 1210353320988542032759645)
                    ·
                      rfl

theorem cell23_7071464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7071464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071464 prefixEnd_7071464 := by exact prefixLift 7071464
  have htrace : WordTrace (prefixWord ++ tailWord_7071464) baseStart_7071464 baseEnd_7071464 := by
    simpa [prefixWord, tailWord_7071464, baseEnd_7071464] using wordTrace_append hprefix tailTrace_7071464
  have hstable : (prefixWord ++ tailWord_7071464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071464).length < 2 ^ (prefixWord ++ tailWord_7071464).sum := by decide
  have hdescent : baseEnd_7071464 < baseStart_7071464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071467 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4]
def baseStart_7071467 : Nat := 118140960795 + 7071467 * 2 ^ 59
def prefixEnd_7071467 : Nat := 4983230072969 + 3 ^ 40 * 7071467 * 2
def baseEnd_7071467 : Nat := 3631061503407589586541421

theorem tailTrace_7071467 : CollatzResearch.WordTrace tailWord_7071467 prefixEnd_7071467 3631061503407589586541421 := by
  unfold tailWord_7071467
  simp only [CollatzResearch.WordTrace]
  refine ⟨257917590272290244257972655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171945060181526829505315103 257917590272290244257972655)
  ·
    refine ⟨386876385408435366386958983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257917590272290244257972655 386876385408435366386958983)
    ·
      refine ⟨580314578112653049580438475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386876385408435366386958983 580314578112653049580438475)
      ·
        refine ⟨870471867168979574370657713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580314578112653049580438475 870471867168979574370657713)
        ·
          refine ⟨652853900376734680777993285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870471867168979574370657713 652853900376734680777993285)
          ·
            refine ⟨122410106320637752645873741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 652853900376734680777993285 122410106320637752645873741)
            ·
              refine ⟨45903789870239157242202653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122410106320637752645873741 45903789870239157242202653)
              ·
                refine ⟨17213921201339683965825995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45903789870239157242202653 17213921201339683965825995)
                ·
                  refine ⟨25820881802009525948738993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17213921201339683965825995 25820881802009525948738993)
                  ·
                    refine ⟨19365661351507144461554245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25820881802009525948738993 19365661351507144461554245)
                    ·
                      refine ⟨3631061503407589586541421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19365661351507144461554245 3631061503407589586541421)
                      ·
                        rfl

theorem cell23_7071467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_7071467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071467 prefixEnd_7071467 := by exact prefixLift 7071467
  have htrace : WordTrace (prefixWord ++ tailWord_7071467) baseStart_7071467 baseEnd_7071467 := by
    simpa [prefixWord, tailWord_7071467, baseEnd_7071467] using wordTrace_append hprefix tailTrace_7071467
  have hstable : (prefixWord ++ tailWord_7071467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071467).length < 2 ^ (prefixWord ++ tailWord_7071467).sum := by decide
  have hdescent : baseEnd_7071467 < baseStart_7071467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071471 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 3, 2, 2]
def baseStart_7071471 : Nat := 118140960795 + 7071471 * 2 ^ 59
def prefixEnd_7071471 : Nat := 4983230072969 + 3 ^ 40 * 7071471 * 2
def baseEnd_7071471 : Nat := 3631063557330207570891403

theorem tailTrace_7071471 : CollatzResearch.WordTrace tailWord_7071471 prefixEnd_7071471 3631063557330207570891403 := by
  unfold tailWord_7071471
  simp only [CollatzResearch.WordTrace]
  refine ⟨257917736164275752941118267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171945157442850501960745511 257917736164275752941118267)
  ·
    refine ⟨386876604246413629411677401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257917736164275752941118267 386876604246413629411677401)
    ·
      refine ⟨290157453184810222058758051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386876604246413629411677401 290157453184810222058758051)
      ·
        refine ⟨435236179777215333088137077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290157453184810222058758051 435236179777215333088137077)
        ·
          refine ⟨40803391854113937477012851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435236179777215333088137077 40803391854113937477012851)
          ·
            refine ⟨61205087781170906215519277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40803391854113937477012851 61205087781170906215519277)
            ·
              refine ⟨22951907917939089830819729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61205087781170906215519277 22951907917939089830819729)
              ·
                refine ⟨17213930938454317373114797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22951907917939089830819729 17213930938454317373114797)
                ·
                  refine ⟨6455224101920369014918049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17213930938454317373114797 6455224101920369014918049)
                  ·
                    refine ⟨4841418076440276761188537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455224101920369014918049 4841418076440276761188537)
                    ·
                      refine ⟨3631063557330207570891403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841418076440276761188537 3631063557330207570891403)
                      ·
                        rfl

theorem cell23_7071471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2, 2].length) (baseStart_7071471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071471 prefixEnd_7071471 := by exact prefixLift 7071471
  have htrace : WordTrace (prefixWord ++ tailWord_7071471) baseStart_7071471 baseEnd_7071471 := by
    simpa [prefixWord, tailWord_7071471, baseEnd_7071471] using wordTrace_append hprefix tailTrace_7071471
  have hstable : (prefixWord ++ tailWord_7071471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071471).length < 2 ^ (prefixWord ++ tailWord_7071471).sum := by decide
  have hdescent : baseEnd_7071471 < baseStart_7071471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071474 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7071474 : Nat := 118140960795 + 7071474 * 2 ^ 59
def prefixEnd_7071474 : Nat := 4983230072969 + 3 ^ 40 * 7071474 * 2
def baseEnd_7071474 : Nat := 3631065097772171059153889

theorem tailTrace_7071474 : CollatzResearch.WordTrace tailWord_7071474 prefixEnd_7071474 3631065097772171059153889 := by
  unfold tailWord_7071474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64479461395816221113369369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171945230388843256302318317 64479461395816221113369369)
  ·
    refine ⟨48359596046862165835027027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64479461395816221113369369 48359596046862165835027027)
    ·
      refine ⟨72539394070293248752540541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48359596046862165835027027 72539394070293248752540541)
      ·
        refine ⟨27202272776359968282202703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72539394070293248752540541 27202272776359968282202703)
        ·
          refine ⟨40803409164539952423304055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27202272776359968282202703 40803409164539952423304055)
          ·
            refine ⟨61205113746809928634956083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40803409164539952423304055 61205113746809928634956083)
            ·
              refine ⟨91807670620214892952434125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61205113746809928634956083 91807670620214892952434125)
              ·
                refine ⟨34427876482580584857162797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91807670620214892952434125 34427876482580584857162797)
                ·
                  refine ⟨12910453680967719321436049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34427876482580584857162797 12910453680967719321436049)
                  ·
                    refine ⟨9682840260725789491077037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12910453680967719321436049 9682840260725789491077037)
                    ·
                      refine ⟨3631065097772171059153889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682840260725789491077037 3631065097772171059153889)
                      ·
                        rfl

theorem cell23_7071474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7071474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071474 prefixEnd_7071474 := by exact prefixLift 7071474
  have htrace : WordTrace (prefixWord ++ tailWord_7071474) baseStart_7071474 baseEnd_7071474 := by
    simpa [prefixWord, tailWord_7071474, baseEnd_7071474] using wordTrace_append hprefix tailTrace_7071474
  have hstable : (prefixWord ++ tailWord_7071474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071474).length < 2 ^ (prefixWord ++ tailWord_7071474).sum := by decide
  have hdescent : baseEnd_7071474 < baseStart_7071474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071491 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 1, 2, 3]
def baseStart_7071491 : Nat := 118140960795 + 7071491 * 2 ^ 59
def prefixEnd_7071491 : Nat := 4983230072969 + 3 ^ 40 * 7071491 * 2
def baseEnd_7071491 : Nat := 3631073826943297492641311

theorem tailTrace_7071491 : CollatzResearch.WordTrace tailWord_7071491 prefixEnd_7071491 3631073826943297492641311 := by
  unfold tailWord_7071491
  simp only [CollatzResearch.WordTrace]
  refine ⟨257918465624203296356846327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171945643749468864237897551 257918465624203296356846327)
  ·
    refine ⟨386877698436304944535269491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257918465624203296356846327 386877698436304944535269491)
    ·
      refine ⟨580316547654457416802904237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386877698436304944535269491 580316547654457416802904237)
      ·
        refine ⟨217618705370421531301089089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580316547654457416802904237 217618705370421531301089089)
        ·
          refine ⟨163214029027816148475816817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217618705370421531301089089 163214029027816148475816817)
          ·
            refine ⟨122410521770862111356862613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163214029027816148475816817 122410521770862111356862613)
            ·
              refine ⟨5737993208009161469852935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122410521770862111356862613 5737993208009161469852935)
              ·
                refine ⟨8606989812013742204779403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737993208009161469852935 8606989812013742204779403)
                ·
                  refine ⟨12910484718020613307169105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8606989812013742204779403 12910484718020613307169105)
                  ·
                    refine ⟨9682863538515459980376829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12910484718020613307169105 9682863538515459980376829)
                    ·
                      refine ⟨3631073826943297492641311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682863538515459980376829 3631073826943297492641311)
                      ·
                        rfl

theorem cell23_7071491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_7071491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071491 prefixEnd_7071491 := by exact prefixLift 7071491
  have htrace : WordTrace (prefixWord ++ tailWord_7071491) baseStart_7071491 baseEnd_7071491 := by
    simpa [prefixWord, tailWord_7071491, baseEnd_7071491] using wordTrace_append hprefix tailTrace_7071491
  have hstable : (prefixWord ++ tailWord_7071491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071491).length < 2 ^ (prefixWord ++ tailWord_7071491).sum := by decide
  have hdescent : baseEnd_7071491 < baseStart_7071491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071518 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7071518 : Nat := 118140960795 + 7071518 * 2 ^ 59
def prefixEnd_7071518 : Nat := 4983230072969 + 3 ^ 40 * 7071518 * 2
def baseEnd_7071518 : Nat := 3631087690920968887003687

theorem tailTrace_7071518 : CollatzResearch.WordTrace tailWord_7071518 prefixEnd_7071518 3631087690920968887003687 := by
  unfold tailWord_7071518
  simp only [CollatzResearch.WordTrace]
  refine ⟨32239931299388184996009901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171946300263403653312052805 32239931299388184996009901)
  ·
    refine ⟨12089974237270569373503713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32239931299388184996009901 12089974237270569373503713)
    ·
      refine ⟨9067480677952927030127785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12089974237270569373503713 9067480677952927030127785)
      ·
        refine ⟨6800610508464695272595839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9067480677952927030127785 6800610508464695272595839)
        ·
          refine ⟨10200915762697042908893759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800610508464695272595839 10200915762697042908893759)
          ·
            refine ⟨15301373644045564363340639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200915762697042908893759 15301373644045564363340639)
            ·
              refine ⟨22952060466068346545010959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301373644045564363340639 22952060466068346545010959)
              ·
                refine ⟨34428090699102519817516439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22952060466068346545010959 34428090699102519817516439)
                ·
                  refine ⟨51642136048653779726274659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34428090699102519817516439 51642136048653779726274659)
                  ·
                    refine ⟨77463204072980669589411989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51642136048653779726274659 77463204072980669589411989)
                    ·
                      refine ⟨3631087690920968887003687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77463204072980669589411989 3631087690920968887003687)
                      ·
                        rfl

theorem cell23_7071518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7071518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071518 prefixEnd_7071518 := by exact prefixLift 7071518
  have htrace : WordTrace (prefixWord ++ tailWord_7071518) baseStart_7071518 baseEnd_7071518 := by
    simpa [prefixWord, tailWord_7071518, baseEnd_7071518] using wordTrace_append hprefix tailTrace_7071518
  have hstable : (prefixWord ++ tailWord_7071518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071518).length < 2 ^ (prefixWord ++ tailWord_7071518).sum := by decide
  have hdescent : baseEnd_7071518 < baseStart_7071518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071521 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7071521 : Nat := 118140960795 + 7071521 * 2 ^ 59
def prefixEnd_7071521 : Nat := 4983230072969 + 3 ^ 40 * 7071521 * 2
def baseEnd_7071521 : Nat := 3631089231362932375266173

theorem tailTrace_7071521 : CollatzResearch.WordTrace tailWord_7071521 prefixEnd_7071521 3631089231362932375266173 := by
  unfold tailWord_7071521
  simp only [CollatzResearch.WordTrace]
  refine ⟨257919559814094611480438417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171946373209396407653625611 257919559814094611480438417)
  ·
    refine ⟨193439669860570958610328813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257919559814094611480438417 193439669860570958610328813)
    ·
      refine ⟨72539876197714109478873305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193439669860570958610328813 72539876197714109478873305)
      ·
        refine ⟨54404907148285582109154979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72539876197714109478873305 54404907148285582109154979)
        ·
          refine ⟨81607360722428373163732469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54404907148285582109154979 81607360722428373163732469)
          ·
            refine ⟨7650690067727659984099919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81607360722428373163732469 7650690067727659984099919)
            ·
              refine ⟨11476035101591489976149879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7650690067727659984099919 11476035101591489976149879)
              ·
                refine ⟨17214052652387234964224819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476035101591489976149879 17214052652387234964224819)
                ·
                  refine ⟨25821078978580852446337229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17214052652387234964224819 25821078978580852446337229)
                  ·
                    refine ⟨9682904616967819667376461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25821078978580852446337229 9682904616967819667376461)
                    ·
                      refine ⟨3631089231362932375266173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9682904616967819667376461 3631089231362932375266173)
                      ·
                        rfl

theorem cell23_7071521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7071521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071521 prefixEnd_7071521 := by exact prefixLift 7071521
  have htrace : WordTrace (prefixWord ++ tailWord_7071521) baseStart_7071521 baseEnd_7071521 := by
    simpa [prefixWord, tailWord_7071521, baseEnd_7071521] using wordTrace_append hprefix tailTrace_7071521
  have hstable : (prefixWord ++ tailWord_7071521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071521).length < 2 ^ (prefixWord ++ tailWord_7071521).sum := by decide
  have hdescent : baseEnd_7071521 < baseStart_7071521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071561 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 4, 2, 2]
def baseStart_7071561 : Nat := 118140960795 + 7071561 * 2 ^ 59
def prefixEnd_7071561 : Nat := 4983230072969 + 3 ^ 40 * 7071561 * 2
def baseEnd_7071561 : Nat := 3631109770589112218765989

theorem tailTrace_7071561 : CollatzResearch.WordTrace tailWord_7071561 prefixEnd_7071561 3631109770589112218765989 := by
  unfold tailWord_7071561
  simp only [CollatzResearch.WordTrace]
  refine ⟨257921018733949698311894537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171947345822633132207929691 257921018733949698311894537)
  ·
    refine ⟨193440764050462273733920903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257921018733949698311894537 193440764050462273733920903)
    ·
      refine ⟨290161146075693410600881355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193440764050462273733920903 290161146075693410600881355)
      ·
        refine ⟨435241719113540115901322033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290161146075693410600881355 435241719113540115901322033)
        ·
          refine ⟨326431289335155086925991525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435241719113540115901322033 326431289335155086925991525)
          ·
            refine ⟨61205866750341578798623411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326431289335155086925991525 61205866750341578798623411)
            ·
              refine ⟨91808800125512368197935117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61205866750341578798623411 91808800125512368197935117)
              ·
                refine ⟨34428300047067138074225669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91808800125512368197935117 34428300047067138074225669)
                ·
                  refine ⟨6455306258825088388917313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34428300047067138074225669 6455306258825088388917313)
                  ·
                    refine ⟨4841479694118816291687985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455306258825088388917313 4841479694118816291687985)
                    ·
                      refine ⟨3631109770589112218765989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841479694118816291687985 3631109770589112218765989)
                      ·
                        rfl

theorem cell23_7071561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2, 2].length) (baseStart_7071561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071561 prefixEnd_7071561 := by exact prefixLift 7071561
  have htrace : WordTrace (prefixWord ++ tailWord_7071561) baseStart_7071561 baseEnd_7071561 := by
    simpa [prefixWord, tailWord_7071561, baseEnd_7071561] using wordTrace_append hprefix tailTrace_7071561
  have hstable : (prefixWord ++ tailWord_7071561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071561).length < 2 ^ (prefixWord ++ tailWord_7071561).sum := by decide
  have hdescent : baseEnd_7071561 < baseStart_7071561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071578 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_7071578 : Nat := 118140960795 + 7071578 * 2 ^ 59
def prefixEnd_7071578 : Nat := 4983230072969 + 3 ^ 40 * 7071578 * 2
def baseEnd_7071578 : Nat := 3631118499760238652253411

theorem tailTrace_7071578 : CollatzResearch.WordTrace tailWord_7071578 prefixEnd_7071578 3631118499760238652253411 := by
  unfold tailWord_7071578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64480409693722027553815847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171947759183258740143508925 64480409693722027553815847)
  ·
    refine ⟨96720614540583041330723771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64480409693722027553815847 96720614540583041330723771)
    ·
      refine ⟨145080921810874561996085657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96720614540583041330723771 145080921810874561996085657)
      ·
        refine ⟨108810691358155921497064243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145080921810874561996085657 108810691358155921497064243)
        ·
          refine ⟨163216037037233882245596365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108810691358155921497064243 163216037037233882245596365)
          ·
            refine ⟨61206013888962705842098637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163216037037233882245596365 61206013888962705842098637)
            ·
              refine ⟨22952255208361014690786989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61206013888962705842098637 22952255208361014690786989)
              ·
                refine ⟨8607095703135380509045121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22952255208361014690786989 8607095703135380509045121)
                ·
                  refine ⟨6455321777351535381783841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8607095703135380509045121 6455321777351535381783841)
                  ·
                    refine ⟨4841491333013651536337881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455321777351535381783841 4841491333013651536337881)
                    ·
                      refine ⟨3631118499760238652253411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841491333013651536337881 3631118499760238652253411)
                      ·
                        rfl

theorem cell23_7071578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_7071578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071578 prefixEnd_7071578 := by exact prefixLift 7071578
  have htrace : WordTrace (prefixWord ++ tailWord_7071578) baseStart_7071578 baseEnd_7071578 := by
    simpa [prefixWord, tailWord_7071578, baseEnd_7071578] using wordTrace_append hprefix tailTrace_7071578
  have hstable : (prefixWord ++ tailWord_7071578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071578).length < 2 ^ (prefixWord ++ tailWord_7071578).sum := by decide
  have hdescent : baseEnd_7071578 < baseStart_7071578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071627 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 8]
def baseStart_7071627 : Nat := 118140960795 + 7071627 * 2 ^ 59
def prefixEnd_7071627 : Nat := 4983230072969 + 3 ^ 40 * 7071627 * 2
def baseEnd_7071627 : Nat := 1210381220104102986846895

theorem tailTrace_7071627 : CollatzResearch.WordTrace tailWord_7071627 prefixEnd_7071627 1210381220104102986846895 := by
  unfold tailWord_7071627
  simp only [CollatzResearch.WordTrace]
  refine ⟨257923425951710591583797135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171948950634473727722531423 257923425951710591583797135)
  ·
    refine ⟨386885138927565887375695703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257923425951710591583797135 386885138927565887375695703)
    ·
      refine ⟨580327708391348831063543555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386885138927565887375695703 580327708391348831063543555)
      ·
        refine ⟨870491562587023246595315333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580327708391348831063543555 870491562587023246595315333)
        ·
          refine ⟨163217167985066858736621625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 870491562587023246595315333 163217167985066858736621625)
          ·
            refine ⟨122412875988800144052466219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163217167985066858736621625 122412875988800144052466219)
            ·
              refine ⟨183619313983200216078699329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122412875988800144052466219 183619313983200216078699329)
              ·
                refine ⟨137714485487400162059024497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183619313983200216078699329 137714485487400162059024497)
                ·
                  refine ⟨103285864115550121544268373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137714485487400162059024497 103285864115550121544268373)
                  ·
                    refine ⟨1210381220104102986846895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103285864115550121544268373 1210381220104102986846895)
                    ·
                      rfl

theorem cell23_7071627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_7071627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071627 prefixEnd_7071627 := by exact prefixLift 7071627
  have htrace : WordTrace (prefixWord ++ tailWord_7071627) baseStart_7071627 baseEnd_7071627 := by
    simpa [prefixWord, tailWord_7071627, baseEnd_7071627] using wordTrace_append hprefix tailTrace_7071627
  have hstable : (prefixWord ++ tailWord_7071627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071627).length < 2 ^ (prefixWord ++ tailWord_7071627).sum := by decide
  have hdescent : baseEnd_7071627 < baseStart_7071627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071674 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_7071674 : Nat := 118140960795 + 7071674 * 2 ^ 59
def prefixEnd_7071674 : Nat := 4983230072969 + 3 ^ 40 * 7071674 * 2
def baseEnd_7071674 : Nat := 403463088211452252961441

theorem tailTrace_7071674 : CollatzResearch.WordTrace tailWord_7071674 prefixEnd_7071674 403463088211452252961441 := by
  unfold tailWord_7071674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64481285045635079652689519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171950093455026879073838717 64481285045635079652689519)
  ·
    refine ⟨96721927568452619479034279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64481285045635079652689519 96721927568452619479034279)
    ·
      refine ⟨145082891352678929218551419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96721927568452619479034279 145082891352678929218551419)
      ·
        refine ⟨217624337029018393827827129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145082891352678929218551419 217624337029018393827827129)
        ·
          refine ⟨163218252771763795370870347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217624337029018393827827129 163218252771763795370870347)
          ·
            refine ⟨244827379157645693056305521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163218252771763795370870347 244827379157645693056305521)
            ·
              refine ⟨183620534368234269792229141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244827379157645693056305521 183620534368234269792229141)
              ·
                refine ⟨8607212548510981396510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183620534368234269792229141 8607212548510981396510741)
                ·
                  refine ⟨403463088211452252961441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8607212548510981396510741 403463088211452252961441)
                  ·
                    rfl

theorem cell23_7071674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_7071674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071674 prefixEnd_7071674 := by exact prefixLift 7071674
  have htrace : WordTrace (prefixWord ++ tailWord_7071674) baseStart_7071674 baseEnd_7071674 := by
    simpa [prefixWord, tailWord_7071674, baseEnd_7071674] using wordTrace_append hprefix tailTrace_7071674
  have hstable : (prefixWord ++ tailWord_7071674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071674).length < 2 ^ (prefixWord ++ tailWord_7071674).sum := by decide
  have hdescent : baseEnd_7071674 < baseStart_7071674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071678 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_7071678 : Nat := 118140960795 + 7071678 * 2 ^ 59
def prefixEnd_7071678 : Nat := 4983230072969 + 3 ^ 40 * 7071678 * 2
def baseEnd_7071678 : Nat := 1210389949275229420334317

theorem tailTrace_7071678 : CollatzResearch.WordTrace tailWord_7071678 prefixEnd_7071678 1210389949275229420334317 := by
  unfold tailWord_7071678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32240660759315728411737961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171950190716350551529269125 32240660759315728411737961)
  ·
    refine ⟨24180495569486796308803471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32240660759315728411737961 24180495569486796308803471)
    ·
      refine ⟨36270743354230194463205207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24180495569486796308803471 36270743354230194463205207)
      ·
        refine ⟨54406115031345291694807811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36270743354230194463205207 54406115031345291694807811)
        ·
          refine ⟨81609172547017937542211717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54406115031345291694807811 81609172547017937542211717)
          ·
            refine ⟨15301719852565863289164697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81609172547017937542211717 15301719852565863289164697)
            ·
              refine ⟨11476289889424397466873523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15301719852565863289164697 11476289889424397466873523)
              ·
                refine ⟨17214434834136596200310285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476289889424397466873523 17214434834136596200310285)
                ·
                  refine ⟨6455413062801223575116357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17214434834136596200310285 6455413062801223575116357)
                  ·
                    refine ⟨1210389949275229420334317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6455413062801223575116357 1210389949275229420334317)
                    ·
                      rfl

theorem cell23_7071678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_7071678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071678 prefixEnd_7071678 := by exact prefixLift 7071678
  have htrace : WordTrace (prefixWord ++ tailWord_7071678) baseStart_7071678 baseEnd_7071678 := by
    simpa [prefixWord, tailWord_7071678, baseEnd_7071678] using wordTrace_append hprefix tailTrace_7071678
  have hstable : (prefixWord ++ tailWord_7071678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071678).length < 2 ^ (prefixWord ++ tailWord_7071678).sum := by decide
  have hdescent : baseEnd_7071678 < baseStart_7071678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071691 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 6]
def baseStart_7071691 : Nat := 118140960795 + 7071691 * 2 ^ 59
def prefixEnd_7071691 : Nat := 4983230072969 + 3 ^ 40 * 7071691 * 2
def baseEnd_7071691 : Nat := 403464058119355190015599

theorem tailTrace_7071691 : CollatzResearch.WordTrace tailWord_7071691 prefixEnd_7071691 403464058119355190015599 := by
  unfold tailWord_7071691
  simp only [CollatzResearch.WordTrace]
  refine ⟨257925760223478730514126927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171950506815652487009417951 257925760223478730514126927)
  ·
    refine ⟨386888640335218095771190391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257925760223478730514126927 386888640335218095771190391)
    ·
      refine ⟨580332960502827143656785587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386888640335218095771190391 580332960502827143656785587)
      ·
        refine ⟨870499440754240715485178381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580332960502827143656785587 870499440754240715485178381)
        ·
          refine ⟨326437290282840268306941893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 870499440754240715485178381 326437290282840268306941893)
          ·
            refine ⟨61206991928032550307551605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326437290282840268306941893 61206991928032550307551605)
            ·
              refine ⟨5738155493253051591332963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61206991928032550307551605 5738155493253051591332963)
              ·
                refine ⟨8607233239879577386999445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738155493253051591332963 8607233239879577386999445)
                ·
                  refine ⟨403464058119355190015599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8607233239879577386999445 403464058119355190015599)
                  ·
                    rfl

theorem cell23_7071691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 6].length) (baseStart_7071691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071691 prefixEnd_7071691 := by exact prefixLift 7071691
  have htrace : WordTrace (prefixWord ++ tailWord_7071691) baseStart_7071691 baseEnd_7071691 := by
    simpa [prefixWord, tailWord_7071691, baseEnd_7071691] using wordTrace_append hprefix tailTrace_7071691
  have hstable : (prefixWord ++ tailWord_7071691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071691).length < 2 ^ (prefixWord ++ tailWord_7071691).sum := by decide
  have hdescent : baseEnd_7071691 < baseStart_7071691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071694 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_7071694 : Nat := 118140960795 + 7071694 * 2 ^ 59
def prefixEnd_7071694 : Nat := 4983230072969 + 3 ^ 40 * 7071694 * 2
def baseEnd_7071694 : Nat := 3631178063516160198402877

theorem tailTrace_7071694 : CollatzResearch.WordTrace tailWord_7071694 prefixEnd_7071694 3631178063516160198402877 := by
  unfold tailWord_7071694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32240733705308482753310767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171950579761645241350990757 32240733705308482753310767)
  ·
    refine ⟨48361100557962724129966151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32240733705308482753310767 48361100557962724129966151)
    ·
      refine ⟨72541650836944086194949227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48361100557962724129966151 72541650836944086194949227)
      ·
        refine ⟨108812476255416129292423841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72541650836944086194949227 108812476255416129292423841)
        ·
          refine ⟨81609357191562096969317881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108812476255416129292423841 81609357191562096969317881)
          ·
            refine ⟨61207017893671572726988411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81609357191562096969317881 61207017893671572726988411)
            ·
              refine ⟨91810526840507359090482617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61207017893671572726988411 91810526840507359090482617)
              ·
                refine ⟨68857895130380519317861963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91810526840507359090482617 68857895130380519317861963)
                ·
                  refine ⟨103286842695570778976792945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68857895130380519317861963 103286842695570778976792945)
                  ·
                    refine ⟨77465132021678084232594709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103286842695570778976792945 77465132021678084232594709)
                    ·
                      refine ⟨3631178063516160198402877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77465132021678084232594709 3631178063516160198402877)
                      ·
                        rfl

theorem cell23_7071694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_7071694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071694 prefixEnd_7071694 := by exact prefixLift 7071694
  have htrace : WordTrace (prefixWord ++ tailWord_7071694) baseStart_7071694 baseEnd_7071694 := by
    simpa [prefixWord, tailWord_7071694, baseEnd_7071694] using wordTrace_append hprefix tailTrace_7071694
  have hstable : (prefixWord ++ tailWord_7071694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071694).length < 2 ^ (prefixWord ++ tailWord_7071694).sum := by decide
  have hdescent : baseEnd_7071694 < baseStart_7071694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071744 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_7071744 : Nat := 118140960795 + 7071744 * 2 ^ 59
def prefixEnd_7071744 : Nat := 4983230072969 + 3 ^ 40 * 7071744 * 2
def baseEnd_7071744 : Nat := 3631203737548885002777647

theorem tailTrace_7071744 : CollatzResearch.WordTrace tailWord_7071744 prefixEnd_7071744 3631203737548885002777647 := by
  unfold tailWord_7071744
  simp only [CollatzResearch.WordTrace]
  refine ⟨128963846646143360282903143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171951795528191147043870857 128963846646143360282903143)
  ·
    refine ⟨193445769969215040424354715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128963846646143360282903143 193445769969215040424354715)
    ·
      refine ⟨290168654953822560636532073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193445769969215040424354715 290168654953822560636532073)
      ·
        refine ⟨217626491215366920477399055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290168654953822560636532073 217626491215366920477399055)
        ·
          refine ⟨326439736823050380716098583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217626491215366920477399055 326439736823050380716098583)
          ·
            refine ⟨489659605234575571074147875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326439736823050380716098583 489659605234575571074147875)
            ·
              refine ⟨734489407851863356611221813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489659605234575571074147875 734489407851863356611221813)
              ·
                refine ⟨68858381986112189682302045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 734489407851863356611221813 68858381986112189682302045)
                ·
                  refine ⟨25821893244792071130863267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68858381986112189682302045 25821893244792071130863267)
                  ·
                    refine ⟨38732839867188106696294901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25821893244792071130863267 38732839867188106696294901)
                    ·
                      refine ⟨3631203737548885002777647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38732839867188106696294901 3631203737548885002777647)
                      ·
                        rfl

theorem cell23_7071744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_7071744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071744 prefixEnd_7071744 := by exact prefixLift 7071744
  have htrace : WordTrace (prefixWord ++ tailWord_7071744) baseStart_7071744 baseEnd_7071744 := by
    simpa [prefixWord, tailWord_7071744, baseEnd_7071744] using wordTrace_append hprefix tailTrace_7071744
  have hstable : (prefixWord ++ tailWord_7071744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071744).length < 2 ^ (prefixWord ++ tailWord_7071744).sum := by decide
  have hdescent : baseEnd_7071744 < baseStart_7071744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071792 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 1, 2, 2]
def baseStart_7071792 : Nat := 118140960795 + 7071792 * 2 ^ 59
def prefixEnd_7071792 : Nat := 4983230072969 + 3 ^ 40 * 7071792 * 2
def baseEnd_7071792 : Nat := 3631228384620300814977427

theorem tailTrace_7071792 : CollatzResearch.WordTrace tailWord_7071792 prefixEnd_7071792 3631228384620300814977427 := by
  unfold tailWord_7071792
  simp only [CollatzResearch.WordTrace]
  refine ⟨128964721998056412381776815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171952962664075216509035753 128964721998056412381776815)
  ·
    refine ⟨193447082997084618572665223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128964721998056412381776815 193447082997084618572665223)
    ·
      refine ⟨290170624495626927858997835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193447082997084618572665223 290170624495626927858997835)
      ·
        refine ⟨435255936743440391788496753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290170624495626927858997835 435255936743440391788496753)
        ·
          refine ⟨326441952557580293841372565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435255936743440391788496753 326441952557580293841372565)
          ·
            refine ⟨15301966526136576273814339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326441952557580293841372565 15301966526136576273814339)
            ·
              refine ⟨22952949789204864410721509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301966526136576273814339 22952949789204864410721509)
              ·
                refine ⟨4303678085475912077010283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22952949789204864410721509 4303678085475912077010283)
                ·
                  refine ⟨6455517128213868115515425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303678085475912077010283 6455517128213868115515425)
                  ·
                    refine ⟨4841637846160401086636569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455517128213868115515425 4841637846160401086636569)
                    ·
                      refine ⟨3631228384620300814977427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841637846160401086636569 3631228384620300814977427)
                      ·
                        rfl

theorem cell23_7071792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 2, 2].length) (baseStart_7071792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071792 prefixEnd_7071792 := by exact prefixLift 7071792
  have htrace : WordTrace (prefixWord ++ tailWord_7071792) baseStart_7071792 baseEnd_7071792 := by
    simpa [prefixWord, tailWord_7071792, baseEnd_7071792] using wordTrace_append hprefix tailTrace_7071792
  have hstable : (prefixWord ++ tailWord_7071792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071792).length < 2 ^ (prefixWord ++ tailWord_7071792).sum := by decide
  have hdescent : baseEnd_7071792 < baseStart_7071792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071808 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_7071808 : Nat := 118140960795 + 7071808 * 2 ^ 59
def prefixEnd_7071808 : Nat := 4983230072969 + 3 ^ 40 * 7071808 * 2
def baseEnd_7071808 : Nat := 3631236600310772752377353

theorem tailTrace_7071808 : CollatzResearch.WordTrace tailWord_7071808 prefixEnd_7071808 3631236600310772752377353 := by
  unfold tailWord_7071808
  simp only [CollatzResearch.WordTrace]
  refine ⟨128965013782027429748068039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171953351709369906330757385 128965013782027429748068039)
  ·
    refine ⟨193447520673041144622102059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128965013782027429748068039 193447520673041144622102059)
    ·
      refine ⟨290171281009561716933153089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193447520673041144622102059 290171281009561716933153089)
      ·
        refine ⟨217628460757171287699864817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290171281009561716933153089 217628460757171287699864817)
        ·
          refine ⟨163221345567878465774898613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217628460757171287699864817 163221345567878465774898613)
          ·
            refine ⟨15302001146988606166396745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163221345567878465774898613 15302001146988606166396745)
            ·
              refine ⟨11476500860241454624797559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15302001146988606166396745 11476500860241454624797559)
              ·
                refine ⟨17214751290362181937196339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476500860241454624797559 17214751290362181937196339)
                ·
                  refine ⟨25822126935543272905794509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17214751290362181937196339 25822126935543272905794509)
                  ·
                    refine ⟨9683297600828727339672941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25822126935543272905794509 9683297600828727339672941)
                    ·
                      refine ⟨3631236600310772752377353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9683297600828727339672941 3631236600310772752377353)
                      ·
                        rfl

theorem cell23_7071808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_7071808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071808 prefixEnd_7071808 := by exact prefixLift 7071808
  have htrace : WordTrace (prefixWord ++ tailWord_7071808) baseStart_7071808 baseEnd_7071808 := by
    simpa [prefixWord, tailWord_7071808, baseEnd_7071808] using wordTrace_append hprefix tailTrace_7071808
  have hstable : (prefixWord ++ tailWord_7071808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071808).length < 2 ^ (prefixWord ++ tailWord_7071808).sum := by decide
  have hdescent : baseEnd_7071808 < baseStart_7071808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071842 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7071842 : Nat := 118140960795 + 7071842 * 2 ^ 59
def prefixEnd_7071842 : Nat := 4983230072969 + 3 ^ 40 * 7071842 * 2
def baseEnd_7071842 : Nat := 3631254058653025619352197

theorem tailTrace_7071842 : CollatzResearch.WordTrace tailWord_7071842 prefixEnd_7071842 3631254058653025619352197 := by
  unfold tailWord_7071842
  simp only [CollatzResearch.WordTrace]
  refine ⟨64482816911482920825718445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171954178430621122201915853 64482816911482920825718445)
  ·
    refine ⟨24181056341806095309644417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64482816911482920825718445 24181056341806095309644417)
    ·
      refine ⟨18135792256354571482233313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24181056341806095309644417 18135792256354571482233313)
      ·
        refine ⟨13601844192265928611674985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18135792256354571482233313 13601844192265928611674985)
        ·
          refine ⟨10201383144199446458756239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13601844192265928611674985 10201383144199446458756239)
          ·
            refine ⟨15302074716299169688134359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201383144199446458756239 15302074716299169688134359)
            ·
              refine ⟨22953112074448754532201539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15302074716299169688134359 22953112074448754532201539)
              ·
                refine ⟨34429668111673131798302309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22953112074448754532201539 34429668111673131798302309)
                ·
                  refine ⟨6455562770938712212181683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34429668111673131798302309 6455562770938712212181683)
                  ·
                    refine ⟨9683344156408068318272525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6455562770938712212181683 9683344156408068318272525)
                    ·
                      refine ⟨3631254058653025619352197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9683344156408068318272525 3631254058653025619352197)
                      ·
                        rfl

theorem cell23_7071842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7071842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071842 prefixEnd_7071842 := by exact prefixLift 7071842
  have htrace : WordTrace (prefixWord ++ tailWord_7071842) baseStart_7071842 baseEnd_7071842 := by
    simpa [prefixWord, tailWord_7071842, baseEnd_7071842] using wordTrace_append hprefix tailTrace_7071842
  have hstable : (prefixWord ++ tailWord_7071842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071842).length < 2 ^ (prefixWord ++ tailWord_7071842).sum := by decide
  have hdescent : baseEnd_7071842 < baseStart_7071842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071865 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 1, 4, 2]
def baseStart_7071865 : Nat := 118140960795 + 7071865 * 2 ^ 59
def prefixEnd_7071865 : Nat := 4983230072969 + 3 ^ 40 * 7071865 * 2
def baseEnd_7071865 : Nat := 3631265868708079029364591

theorem tailTrace_7071865 : CollatzResearch.WordTrace tailWord_7071865 prefixEnd_7071865 3631265868708079029364591 := by
  unfold tailWord_7071865
  simp only [CollatzResearch.WordTrace]
  refine ⟨257932106524848358230961049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171954737683232238820640699 257932106524848358230961049)
  ·
    refine ⟨193449079893636268673220787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257932106524848358230961049 193449079893636268673220787)
    ·
      refine ⟨290173619840454403009831181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193449079893636268673220787 290173619840454403009831181)
      ·
        refine ⟨108815107440170401128686693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290173619840454403009831181 108815107440170401128686693)
        ·
          refine ⟨20402832645031950211628755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108815107440170401128686693 20402832645031950211628755)
          ·
            refine ⟨30604248967547925317443133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20402832645031950211628755 30604248967547925317443133)
            ·
              refine ⟨11476593362830471994041175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30604248967547925317443133 11476593362830471994041175)
              ·
                refine ⟨17214890044245707991061763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11476593362830471994041175 17214890044245707991061763)
                ·
                  refine ⟨25822335066368561986592645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17214890044245707991061763 25822335066368561986592645)
                  ·
                    refine ⟨4841687824944105372486121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25822335066368561986592645 4841687824944105372486121)
                    ·
                      refine ⟨3631265868708079029364591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841687824944105372486121 3631265868708079029364591)
                      ·
                        rfl

theorem cell23_7071865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_7071865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071865 prefixEnd_7071865 := by exact prefixLift 7071865
  have htrace : WordTrace (prefixWord ++ tailWord_7071865) baseStart_7071865 baseEnd_7071865 := by
    simpa [prefixWord, tailWord_7071865, baseEnd_7071865] using wordTrace_append hprefix tailTrace_7071865
  have hstable : (prefixWord ++ tailWord_7071865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071865).length < 2 ^ (prefixWord ++ tailWord_7071865).sum := by decide
  have hdescent : baseEnd_7071865 < baseStart_7071865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071951 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_7071951 : Nat := 118140960795 + 7071951 * 2 ^ 59
def prefixEnd_7071951 : Nat := 4983230072969 + 3 ^ 40 * 7071951 * 2
def baseEnd_7071951 : Nat := 3631310028044365692889195

theorem tailTrace_7071951 : CollatzResearch.WordTrace tailWord_7071951 prefixEnd_7071951 3631310028044365692889195 := by
  unfold tailWord_7071951
  simp only [CollatzResearch.WordTrace]
  refine ⟨257935243202536794918591707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171956828801691196612394471 257935243202536794918591707)
  ·
    refine ⟨386902864803805192377887561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257935243202536794918591707 386902864803805192377887561)
    ·
      refine ⟨290177148602853894283415671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386902864803805192377887561 290177148602853894283415671)
      ·
        refine ⟨435265722904280841425123507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290177148602853894283415671 435265722904280841425123507)
        ·
          refine ⟨652898584356421262137685261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435265722904280841425123507 652898584356421262137685261)
          ·
            refine ⟨244836969133657973301631973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652898584356421262137685261 244836969133657973301631973)
            ·
              refine ⟨45906931712560869994055995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244836969133657973301631973 45906931712560869994055995)
              ·
                refine ⟨68860397568841304991083993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45906931712560869994055995 68860397568841304991083993)
                ·
                  refine ⟨51645298176630978743312995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68860397568841304991083993 51645298176630978743312995)
                  ·
                    refine ⟨77467947264946468114969493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51645298176630978743312995 77467947264946468114969493)
                    ·
                      refine ⟨3631310028044365692889195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77467947264946468114969493 3631310028044365692889195)
                      ·
                        rfl

theorem cell23_7071951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_7071951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071951 prefixEnd_7071951 := by exact prefixLift 7071951
  have htrace : WordTrace (prefixWord ++ tailWord_7071951) baseStart_7071951 baseEnd_7071951 := by
    simpa [prefixWord, tailWord_7071951, baseEnd_7071951] using wordTrace_append hprefix tailTrace_7071951
  have hstable : (prefixWord ++ tailWord_7071951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071951).length < 2 ^ (prefixWord ++ tailWord_7071951).sum := by decide
  have hdescent : baseEnd_7071951 < baseStart_7071951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071961 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 8]
def baseStart_7071961 : Nat := 118140960795 + 7071961 * 2 ^ 59
def prefixEnd_7071961 : Nat := 4983230072969 + 3 ^ 40 * 7071961 * 2
def baseEnd_7071961 : Nat := 403479462538990072640461

theorem tailTrace_7071961 : CollatzResearch.WordTrace tailWord_7071961 prefixEnd_7071961 403479462538990072640461 := by
  unfold tailWord_7071961
  simp only [CollatzResearch.WordTrace]
  refine ⟨257935607932500566626455737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171957071955000377750970491 257935607932500566626455737)
  ·
    refine ⟨193451705949375424969841803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257935607932500566626455737 193451705949375424969841803)
    ·
      refine ⟨290177558924063137454762705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193451705949375424969841803 290177558924063137454762705)
      ·
        refine ⟨217633169193047353091072029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290177558924063137454762705 217633169193047353091072029)
        ·
          refine ⟨81612438447392757409152011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217633169193047353091072029 81612438447392757409152011)
          ·
            refine ⟨122418657671089136113728017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81612438447392757409152011 122418657671089136113728017)
            ·
              refine ⟨91813993253316852085296013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122418657671089136113728017 91813993253316852085296013)
              ·
                refine ⟨34430247469993819531986005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91813993253316852085296013 34430247469993819531986005)
                ·
                  refine ⟨403479462538990072640461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34430247469993819531986005 403479462538990072640461)
                  ·
                    rfl

theorem cell23_7071961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_7071961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071961 prefixEnd_7071961 := by exact prefixLift 7071961
  have htrace : WordTrace (prefixWord ++ tailWord_7071961) baseStart_7071961 baseEnd_7071961 := by
    simpa [prefixWord, tailWord_7071961, baseEnd_7071961] using wordTrace_append hprefix tailTrace_7071961
  have hstable : (prefixWord ++ tailWord_7071961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071961).length < 2 ^ (prefixWord ++ tailWord_7071961).sum := by decide
  have hdescent : baseEnd_7071961 < baseStart_7071961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7071978 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_7071978 : Nat := 118140960795 + 7071978 * 2 ^ 59
def prefixEnd_7071978 : Nat := 4983230072969 + 3 ^ 40 * 7071978 * 2
def baseEnd_7071978 : Nat := 403480432446893009694619

theorem tailTrace_7071978 : CollatzResearch.WordTrace tailWord_7071978 prefixEnd_7071978 403480432446893009694619 := by
  unfold tailWord_7071978
  simp only [CollatzResearch.WordTrace]
  refine ⟨64484056993359744632456147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171957485315625985686549725 64484056993359744632456147)
  ·
    refine ⟨96726085490039616948684221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64484056993359744632456147 96726085490039616948684221)
    ·
      refine ⟨36272282058764856355756583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96726085490039616948684221 36272282058764856355756583)
      ·
        refine ⟨54408423088147284533634875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36272282058764856355756583 54408423088147284533634875)
        ·
          refine ⟨81612634632220926800452313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54408423088147284533634875 81612634632220926800452313)
          ·
            refine ⟨61209475974165695100339235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81612634632220926800452313 61209475974165695100339235)
            ·
              refine ⟨91814213961248542650508853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61209475974165695100339235 91814213961248542650508853)
              ·
                refine ⟨8607582558867050873485205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91814213961248542650508853 8607582558867050873485205)
                ·
                  refine ⟨403480432446893009694619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8607582558867050873485205 403480432446893009694619)
                  ·
                    rfl

theorem cell23_7071978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_7071978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7071978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7071978 prefixEnd_7071978 := by exact prefixLift 7071978
  have htrace : WordTrace (prefixWord ++ tailWord_7071978) baseStart_7071978 baseEnd_7071978 := by
    simpa [prefixWord, tailWord_7071978, baseEnd_7071978] using wordTrace_append hprefix tailTrace_7071978
  have hstable : (prefixWord ++ tailWord_7071978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7071978).length < 2 ^ (prefixWord ++ tailWord_7071978).sum := by decide
  have hdescent : baseEnd_7071978 < baseStart_7071978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7071978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072015 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 2, 3, 2]
def baseStart_7072015 : Nat := 118140960795 + 7072015 * 2 ^ 59
def prefixEnd_7072015 : Nat := 4983230072969 + 3 ^ 40 * 7072015 * 2
def baseEnd_7072015 : Nat := 3631342890806253442488901

theorem tailTrace_7072015 : CollatzResearch.WordTrace tailWord_7072015 prefixEnd_7072015 3631342890806253442488901 := by
  unfold tailWord_7072015
  simp only [CollatzResearch.WordTrace]
  refine ⟨257937577474304933848921499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171958384982869955899280999 257937577474304933848921499)
  ·
    refine ⟨386906366211457400773382249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257937577474304933848921499 386906366211457400773382249)
    ·
      refine ⟨290179774658593050580036687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386906366211457400773382249 290179774658593050580036687)
      ·
        refine ⟨435269661987889575870055031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290179774658593050580036687 435269661987889575870055031)
        ·
          refine ⟨652904492981834363805082547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435269661987889575870055031 652904492981834363805082547)
          ·
            refine ⟨979356739472751545707623821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652904492981834363805082547 979356739472751545707623821)
            ·
              refine ⟨367258777302281829640358933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979356739472751545707623821 367258777302281829640358933)
              ·
                refine ⟨17215255186044460764391825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367258777302281829640358933 17215255186044460764391825)
                ·
                  refine ⟨12911441389533345573293869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17215255186044460764391825 12911441389533345573293869)
                  ·
                    refine ⟨4841790521075004589985201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12911441389533345573293869 4841790521075004589985201)
                    ·
                      refine ⟨3631342890806253442488901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841790521075004589985201 3631342890806253442488901)
                      ·
                        rfl

theorem cell23_7072015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3, 2].length) (baseStart_7072015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072015 prefixEnd_7072015 := by exact prefixLift 7072015
  have htrace : WordTrace (prefixWord ++ tailWord_7072015) baseStart_7072015 baseEnd_7072015 := by
    simpa [prefixWord, tailWord_7072015, baseEnd_7072015] using wordTrace_append hprefix tailTrace_7072015
  have hstable : (prefixWord ++ tailWord_7072015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072015).length < 2 ^ (prefixWord ++ tailWord_7072015).sum := by decide
  have hdescent : baseEnd_7072015 < baseStart_7072015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072062 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_7072062 : Nat := 118140960795 + 7072062 * 2 ^ 59
def prefixEnd_7072062 : Nat := 4983230072969 + 3 ^ 40 * 7072062 * 2
def baseEnd_7072062 : Nat := 3631367024397014758601185

theorem tailTrace_7072062 : CollatzResearch.WordTrace tailWord_7072062 prefixEnd_7072062 3631367024397014758601185 := by
  unfold tailWord_7072062
  simp only [CollatzResearch.WordTrace]
  refine ⟨32242411463141832609485305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171959527803423107250588293 32242411463141832609485305)
  ·
    refine ⟨24181808597356374457113979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32242411463141832609485305 24181808597356374457113979)
    ·
      refine ⟨36272712896034561685670969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24181808597356374457113979 36272712896034561685670969)
      ·
        refine ⟨27204534672025921264253227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36272712896034561685670969 27204534672025921264253227)
        ·
          refine ⟨40806802008038881896379841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27204534672025921264253227 40806802008038881896379841)
          ·
            refine ⟨30605101506029161422284881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40806802008038881896379841 30605101506029161422284881)
            ·
              refine ⟨22953826129521871066713661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30605101506029161422284881 22953826129521871066713661)
              ·
                refine ⟨8607684798570701650017623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22953826129521871066713661 8607684798570701650017623)
                ·
                  refine ⟨12911527197856052475026435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8607684798570701650017623 12911527197856052475026435)
                  ·
                    refine ⟨19367290796784078712539653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12911527197856052475026435 19367290796784078712539653)
                    ·
                      refine ⟨3631367024397014758601185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19367290796784078712539653 3631367024397014758601185)
                      ·
                        rfl

theorem cell23_7072062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_7072062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072062 prefixEnd_7072062 := by exact prefixLift 7072062
  have htrace : WordTrace (prefixWord ++ tailWord_7072062) baseStart_7072062 baseEnd_7072062 := by
    simpa [prefixWord, tailWord_7072062, baseEnd_7072062] using wordTrace_append hprefix tailTrace_7072062
  have hstable : (prefixWord ++ tailWord_7072062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072062).length < 2 ^ (prefixWord ++ tailWord_7072062).sum := by decide
  have hdescent : baseEnd_7072062 < baseStart_7072062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072085 : List Nat := [1, 3, 2, 2, 4, 1, 2, 8]
def baseStart_7072085 : Nat := 118140960795 + 7072085 * 2 ^ 59
def prefixEnd_7072085 : Nat := 4983230072969 + 3 ^ 40 * 7072085 * 2
def baseEnd_7072085 : Nat := 134495512387113635874577

theorem tailTrace_7072085 : CollatzResearch.WordTrace tailWord_7072085 prefixEnd_7072085 134495512387113635874577 := by
  unfold tailWord_7072085
  simp only [CollatzResearch.WordTrace]
  refine ⟨257940130584051335803969709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171960087056034223869313139 257940130584051335803969709)
  ·
    refine ⟨96727548969019250926488641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257940130584051335803969709 96727548969019250926488641)
    ·
      refine ⟨72545661726764438194866481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96727548969019250926488641 72545661726764438194866481)
      ·
        refine ⟨54409246295073328646149861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72545661726764438194866481 54409246295073328646149861)
        ·
          refine ⟨10201733680326249121153099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54409246295073328646149861 10201733680326249121153099)
          ·
            refine ⟨15302600520489373681729649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201733680326249121153099 15302600520489373681729649)
            ·
              refine ⟨11476950390367030261297237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15302600520489373681729649 11476950390367030261297237)
              ·
                refine ⟨134495512387113635874577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11476950390367030261297237 134495512387113635874577)
                ·
                  rfl

theorem cell23_7072085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 8].length) (baseStart_7072085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072085 prefixEnd_7072085 := by exact prefixLift 7072085
  have htrace : WordTrace (prefixWord ++ tailWord_7072085) baseStart_7072085 baseEnd_7072085 := by
    simpa [prefixWord, tailWord_7072085, baseEnd_7072085] using wordTrace_append hprefix tailTrace_7072085
  have hstable : (prefixWord ++ tailWord_7072085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072085).length < 2 ^ (prefixWord ++ tailWord_7072085).sum := by decide
  have hdescent : baseEnd_7072085 < baseStart_7072085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072129 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_7072129 : Nat := 118140960795 + 7072129 * 2 ^ 59
def prefixEnd_7072129 : Nat := 4983230072969 + 3 ^ 40 * 7072129 * 2
def baseEnd_7072129 : Nat := 3631401427600865996463377

theorem tailTrace_7072129 : CollatzResearch.WordTrace tailWord_7072129 prefixEnd_7072129 3631401427600865996463377 := by
  unfold tailWord_7072129
  simp only [CollatzResearch.WordTrace]
  refine ⟨257941735395891931318571441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171961156930594620879047627 257941735395891931318571441)
  ·
    refine ⟨193456301546918948488928581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257941735395891931318571441 193456301546918948488928581)
    ·
      refine ⟨36273056540047302841674109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193456301546918948488928581 36273056540047302841674109)
      ·
        refine ⟨13602396202517738565627791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36273056540047302841674109 13602396202517738565627791)
        ·
          refine ⟨20403594303776607848441687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13602396202517738565627791 20403594303776607848441687)
          ·
            refine ⟨30605391455664911772662531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20403594303776607848441687 30605391455664911772662531)
            ·
              refine ⟨45908087183497367658993797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30605391455664911772662531 45908087183497367658993797)
              ·
                refine ⟨8607766346905756436061337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45908087183497367658993797 8607766346905756436061337)
                ·
                  refine ⟨6455824760179317327046003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8607766346905756436061337 6455824760179317327046003)
                  ·
                    refine ⟨9683737140268975990569005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6455824760179317327046003 9683737140268975990569005)
                    ·
                      refine ⟨3631401427600865996463377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9683737140268975990569005 3631401427600865996463377)
                      ·
                        rfl

theorem cell23_7072129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_7072129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072129 prefixEnd_7072129 := by exact prefixLift 7072129
  have htrace : WordTrace (prefixWord ++ tailWord_7072129) baseStart_7072129 baseEnd_7072129 := by
    simpa [prefixWord, tailWord_7072129, baseEnd_7072129] using wordTrace_append hprefix tailTrace_7072129
  have hstable : (prefixWord ++ tailWord_7072129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072129).length < 2 ^ (prefixWord ++ tailWord_7072129).sum := by decide
  have hdescent : baseEnd_7072129 < baseStart_7072129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072130 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7072130 : Nat := 118140960795 + 7072130 * 2 ^ 59
def prefixEnd_7072130 : Nat := 4983230072969 + 3 ^ 40 * 7072130 * 2
def baseEnd_7072130 : Nat := 3631401941081520492550873

theorem tailTrace_7072130 : CollatzResearch.WordTrace tailWord_7072130 prefixEnd_7072130 3631401941081520492550873 := by
  unfold tailWord_7072130
  simp only [CollatzResearch.WordTrace]
  refine ⟨64485442967222077122339461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171961181245925538992905229 64485442967222077122339461)
  ·
    refine ⟨12091020556354139460438649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64485442967222077122339461 12091020556354139460438649)
    ·
      refine ⟨9068265417265604595328987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12091020556354139460438649 9068265417265604595328987)
      ·
        refine ⟨13602398125898406892993481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068265417265604595328987 13602398125898406892993481)
        ·
          refine ⟨10201798594423805169745111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13602398125898406892993481 10201798594423805169745111)
          ·
            refine ⟨15302697891635707754617667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201798594423805169745111 15302697891635707754617667)
            ·
              refine ⟨22954046837453561631926501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15302697891635707754617667 22954046837453561631926501)
              ·
                refine ⟨4303883782022542805986219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22954046837453561631926501 4303883782022542805986219)
                ·
                  refine ⟨6455825673033814208979329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303883782022542805986219 6455825673033814208979329)
                  ·
                    refine ⟨4841869254775360656734497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6455825673033814208979329 4841869254775360656734497)
                    ·
                      refine ⟨3631401941081520492550873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4841869254775360656734497 3631401941081520492550873)
                      ·
                        rfl

theorem cell23_7072130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7072130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072130 prefixEnd_7072130 := by exact prefixLift 7072130
  have htrace : WordTrace (prefixWord ++ tailWord_7072130) baseStart_7072130 baseEnd_7072130 := by
    simpa [prefixWord, tailWord_7072130, baseEnd_7072130] using wordTrace_append hprefix tailTrace_7072130
  have hstable : (prefixWord ++ tailWord_7072130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072130).length < 2 ^ (prefixWord ++ tailWord_7072130).sum := by decide
  have hdescent : baseEnd_7072130 < baseStart_7072130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072180 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7072180 : Nat := 118140960795 + 7072180 * 2 ^ 59
def prefixEnd_7072180 : Nat := 4983230072969 + 3 ^ 40 * 7072180 * 2
def baseEnd_7072180 : Nat := 3631427615114245296925643

theorem tailTrace_7072180 : CollatzResearch.WordTrace tailWord_7072180 prefixEnd_7072180 3631427615114245296925643 := by
  unfold tailWord_7072180
  simp only [CollatzResearch.WordTrace]
  refine ⟨128971797759353583514338997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171962397012471444685785329 128971797759353583514338997)
  ·
    refine ⟨12091106039939398454469281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128971797759353583514338997 12091106039939398454469281)
    ·
      refine ⟨9068329529954548840851961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12091106039939398454469281 9068329529954548840851961)
      ·
        refine ⟨6801247147465911630638971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9068329529954548840851961 6801247147465911630638971)
        ·
          refine ⟨10201870721198867445958457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801247147465911630638971 10201870721198867445958457)
          ·
            refine ⟨7651403040899150584468843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10201870721198867445958457 7651403040899150584468843)
            ·
              refine ⟨11477104561348725876703265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7651403040899150584468843 11477104561348725876703265)
              ·
                refine ⟨8607828421011544407527449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11477104561348725876703265 8607828421011544407527449)
                ·
                  refine ⟨6455871315758658305645587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8607828421011544407527449 6455871315758658305645587)
                  ·
                    refine ⟨9683806973637987458468381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6455871315758658305645587 9683806973637987458468381)
                    ·
                      refine ⟨3631427615114245296925643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9683806973637987458468381 3631427615114245296925643)
                      ·
                        rfl

theorem cell23_7072180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7072180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072180 prefixEnd_7072180 := by exact prefixLift 7072180
  have htrace : WordTrace (prefixWord ++ tailWord_7072180) baseStart_7072180 baseEnd_7072180 := by
    simpa [prefixWord, tailWord_7072180, baseEnd_7072180] using wordTrace_append hprefix tailTrace_7072180
  have hstable : (prefixWord ++ tailWord_7072180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072180).length < 2 ^ (prefixWord ++ tailWord_7072180).sum := by decide
  have hdescent : baseEnd_7072180 < baseStart_7072180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072225 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7072225 : Nat := 118140960795 + 7072225 * 2 ^ 59
def prefixEnd_7072225 : Nat := 4983230072969 + 3 ^ 40 * 7072225 * 2
def baseEnd_7072225 : Nat := 3631450721743697620862935

theorem tailTrace_7072225 : CollatzResearch.WordTrace tailWord_7072225 prefixEnd_7072225 3631450721743697620862935 := by
  unfold tailWord_7072225
  simp only [CollatzResearch.WordTrace]
  refine ⟨257945236803544139714066129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171963491202362759809377419 257945236803544139714066129)
  ·
    refine ⟨193458927602658104785549597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257945236803544139714066129 193458927602658104785549597)
    ·
      refine ⟨72547097850996789294581099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193458927602658104785549597 72547097850996789294581099)
      ·
        refine ⟨108820646776495183941871649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72547097850996789294581099 108820646776495183941871649)
        ·
          refine ⟨81615485082371387956403737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108820646776495183941871649 81615485082371387956403737)
          ·
            refine ⟨61211613811778540967302803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81615485082371387956403737 61211613811778540967302803)
            ·
              refine ⟨91817420717667811450954205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61211613811778540967302803 91817420717667811450954205)
              ·
                refine ⟨34431532769125429294107827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91817420717667811450954205 34431532769125429294107827)
                ·
                  refine ⟨51647299153688143941161741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34431532769125429294107827 51647299153688143941161741)
                  ·
                    refine ⟨19367737182633053977935653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51647299153688143941161741 19367737182633053977935653)
                    ·
                      refine ⟨3631450721743697620862935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19367737182633053977935653 3631450721743697620862935)
                      ·
                        rfl

theorem cell23_7072225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7072225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072225 prefixEnd_7072225 := by exact prefixLift 7072225
  have htrace : WordTrace (prefixWord ++ tailWord_7072225) baseStart_7072225 baseEnd_7072225 := by
    simpa [prefixWord, tailWord_7072225, baseEnd_7072225] using wordTrace_append hprefix tailTrace_7072225
  have hstable : (prefixWord ++ tailWord_7072225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072225).length < 2 ^ (prefixWord ++ tailWord_7072225).sum := by decide
  have hdescent : baseEnd_7072225 < baseStart_7072225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072276 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7072276 : Nat := 118140960795 + 7072276 * 2 ^ 59
def prefixEnd_7072276 : Nat := 4983230072969 + 3 ^ 40 * 7072276 * 2
def baseEnd_7072276 : Nat := 3631476909257076921325201

theorem tailTrace_7072276 : CollatzResearch.WordTrace tailWord_7072276 prefixEnd_7072276 3631476909257076921325201 := by
  unfold tailWord_7072276
  simp only [CollatzResearch.WordTrace]
  refine ⟨128973548463179687712086341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171964731284239583616115121 128973548463179687712086341)
  ·
    refine ⟨24182540336846191446016189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128973548463179687712086341 24182540336846191446016189)
    ·
      refine ⟨9068452626317321792256071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24182540336846191446016189 9068452626317321792256071)
      ·
        refine ⟨13602678939475982688384107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068452626317321792256071 13602678939475982688384107)
        ·
          refine ⟨20404018409213974032576161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13602678939475982688384107 20404018409213974032576161)
          ·
            refine ⟨15303013806910480524432121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20404018409213974032576161 15303013806910480524432121)
            ·
              refine ⟨11477260355182860393324091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15303013806910480524432121 11477260355182860393324091)
              ·
                refine ⟨17215890532774290589986137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11477260355182860393324091 17215890532774290589986137)
                ·
                  refine ⟨12911917899580717942489603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17215890532774290589986137 12911917899580717942489603)
                  ·
                    refine ⟨19367876849371076913734405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12911917899580717942489603 19367876849371076913734405)
                    ·
                      refine ⟨3631476909257076921325201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19367876849371076913734405 3631476909257076921325201)
                      ·
                        rfl

theorem cell23_7072276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7072276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072276 prefixEnd_7072276 := by exact prefixLift 7072276
  have htrace : WordTrace (prefixWord ++ tailWord_7072276) baseStart_7072276 baseEnd_7072276 := by
    simpa [prefixWord, tailWord_7072276, baseEnd_7072276] using wordTrace_append hprefix tailTrace_7072276
  have hstable : (prefixWord ++ tailWord_7072276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072276).length < 2 ^ (prefixWord ++ tailWord_7072276).sum := by decide
  have hdescent : baseEnd_7072276 < baseStart_7072276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072309 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_7072309 : Nat := 118140960795 + 7072309 * 2 ^ 59
def prefixEnd_7072309 : Nat := 4983230072969 + 3 ^ 40 * 7072309 * 2
def baseEnd_7072309 : Nat := 3631493854118675292212549

theorem tailTrace_7072309 : CollatzResearch.WordTrace tailWord_7072309 prefixEnd_7072309 3631493854118675292212549 := by
  unfold tailWord_7072309
  simp only [CollatzResearch.WordTrace]
  refine ⟨257948300535239822060123981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171965533690159881373415987 257948300535239822060123981)
  ·
    refine ⟨96730612700714933272546493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257948300535239822060123981 96730612700714933272546493)
    ·
      refine ⟨36273979762768099977204935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96730612700714933272546493 36273979762768099977204935)
      ·
        refine ⟨54410969644152149965807403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36273979762768099977204935 54410969644152149965807403)
        ·
          refine ⟨81616454466228224948711105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54410969644152149965807403 81616454466228224948711105)
          ·
            refine ⟨61212340849671168711533329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81616454466228224948711105 61212340849671168711533329)
            ·
              refine ⟨45909255637253376533649997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61212340849671168711533329 45909255637253376533649997)
              ·
                refine ⟨17215970863970016200118749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45909255637253376533649997 17215970863970016200118749)
                ·
                  refine ⟨6455989073988756075044531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17215970863970016200118749 6455989073988756075044531)
                  ·
                    refine ⟨9683983610983134112566797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6455989073988756075044531 9683983610983134112566797)
                    ·
                      refine ⟨3631493854118675292212549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9683983610983134112566797 3631493854118675292212549)
                      ·
                        rfl

theorem cell23_7072309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_7072309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072309 prefixEnd_7072309 := by exact prefixLift 7072309
  have htrace : WordTrace (prefixWord ++ tailWord_7072309) baseStart_7072309 baseEnd_7072309 := by
    simpa [prefixWord, tailWord_7072309, baseEnd_7072309] using wordTrace_append hprefix tailTrace_7072309
  have hstable : (prefixWord ++ tailWord_7072309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072309).length < 2 ^ (prefixWord ++ tailWord_7072309).sum := by decide
  have hdescent : baseEnd_7072309 < baseStart_7072309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072332 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7072332 : Nat := 118140960795 + 7072332 * 2 ^ 59
def prefixEnd_7072332 : Nat := 4983230072969 + 3 ^ 40 * 7072332 * 2
def baseEnd_7072332 : Nat := 3631505664173728702224943

theorem tailTrace_7072332 : CollatzResearch.WordTrace tailWord_7072332 prefixEnd_7072332 3631505664173728702224943 := by
  unfold tailWord_7072332
  simp only [CollatzResearch.WordTrace]
  refine ⟨128974569707078248494105625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171966092942770997992140833 128974569707078248494105625)
  ·
    refine ⟨96730927280308686370579219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128974569707078248494105625 96730927280308686370579219)
    ·
      refine ⟨145096390920463029555868829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96730927280308686370579219 145096390920463029555868829)
      ·
        refine ⟨54411146595173636083450811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145096390920463029555868829 54411146595173636083450811)
        ·
          refine ⟨81616719892760454125176217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54411146595173636083450811 81616719892760454125176217)
          ·
            refine ⟨61212539919570340593882163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81616719892760454125176217 61212539919570340593882163)
            ·
              refine ⟨91818809879355510890823245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61212539919570340593882163 91818809879355510890823245)
              ·
                refine ⟨34432053704758316584058717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91818809879355510890823245 34432053704758316584058717)
                ·
                  refine ⟨12912020139284368719022019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34432053704758316584058717 12912020139284368719022019)
                  ·
                    refine ⟨19368030208926553078533029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12912020139284368719022019 19368030208926553078533029)
                    ·
                      refine ⟨3631505664173728702224943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19368030208926553078533029 3631505664173728702224943)
                      ·
                        rfl

theorem cell23_7072332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7072332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072332 prefixEnd_7072332 := by exact prefixLift 7072332
  have htrace : WordTrace (prefixWord ++ tailWord_7072332) baseStart_7072332 baseEnd_7072332 := by
    simpa [prefixWord, tailWord_7072332, baseEnd_7072332] using wordTrace_append hprefix tailTrace_7072332
  have hstable : (prefixWord ++ tailWord_7072332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072332).length < 2 ^ (prefixWord ++ tailWord_7072332).sum := by decide
  have hdescent : baseEnd_7072332 < baseStart_7072332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072345 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_7072345 : Nat := 118140960795 + 7072345 * 2 ^ 59
def prefixEnd_7072345 : Nat := 4983230072969 + 3 ^ 40 * 7072345 * 2
def baseEnd_7072345 : Nat := 3631512339422237151362383

theorem tailTrace_7072345 : CollatzResearch.WordTrace tailWord_7072345 prefixEnd_7072345 3631512339422237151362383 := by
  unfold tailWord_7072345
  simp only [CollatzResearch.WordTrace]
  refine ⟨257949613563109400208434489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171966409042072933472289659 257949613563109400208434489)
  ·
    refine ⟨193462210172332050156325867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257949613563109400208434489 193462210172332050156325867)
    ·
      refine ⟨290193315258498075234488801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193462210172332050156325867 290193315258498075234488801)
      ·
        refine ⟨217644986443873556425866601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290193315258498075234488801 217644986443873556425866601)
        ·
          refine ⟨163233739832905167319399951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217644986443873556425866601 163233739832905167319399951)
          ·
            refine ⟨244850609749357750979099927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163233739832905167319399951 244850609749357750979099927)
            ·
              refine ⟨367275914624036626468649891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244850609749357750979099927 367275914624036626468649891)
              ·
                refine ⟨550913871936054939702974837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367275914624036626468649891 550913871936054939702974837)
                ·
                  refine ⟨51648175494005150597153891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 550913871936054939702974837 51648175494005150597153891)
                  ·
                    refine ⟨77472263241007725895730837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51648175494005150597153891 77472263241007725895730837)
                    ·
                      refine ⟨3631512339422237151362383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77472263241007725895730837 3631512339422237151362383)
                      ·
                        rfl

theorem cell23_7072345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_7072345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072345 prefixEnd_7072345 := by exact prefixLift 7072345
  have htrace : WordTrace (prefixWord ++ tailWord_7072345) baseStart_7072345 baseEnd_7072345 := by
    simpa [prefixWord, tailWord_7072345, baseEnd_7072345] using wordTrace_append hprefix tailTrace_7072345
  have hstable : (prefixWord ++ tailWord_7072345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072345).length < 2 ^ (prefixWord ++ tailWord_7072345).sum := by decide
  have hdescent : baseEnd_7072345 < baseStart_7072345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072350 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_7072350 : Nat := 118140960795 + 7072350 * 2 ^ 59
def prefixEnd_7072350 : Nat := 4983230072969 + 3 ^ 40 * 7072350 * 2
def baseEnd_7072350 : Nat := 403501656313945514644429

theorem tailTrace_7072350 : CollatzResearch.WordTrace tailWord_7072350 prefixEnd_7072350 403501656313945514644429 := by
  unfold tailWord_7072350
  simp only [CollatzResearch.WordTrace]
  refine ⟨32243724491011410757795813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171966530618727524041577669 32243724491011410757795813)
  ·
    refine ⟨6045698342064639517086715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32243724491011410757795813 6045698342064639517086715)
    ·
      refine ⟨9068547513096959275630073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045698342064639517086715 9068547513096959275630073)
      ·
        refine ⟨6801410634822719456722555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9068547513096959275630073 6801410634822719456722555)
        ·
          refine ⟨10202115952234079185083833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801410634822719456722555 10202115952234079185083833)
          ·
            refine ⟨7651586964175559388812875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10202115952234079185083833 7651586964175559388812875)
            ·
              refine ⟨11477380446263339083219313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7651586964175559388812875 11477380446263339083219313)
              ·
                refine ⟨8608035334697504312414485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11477380446263339083219313 8608035334697504312414485)
                ·
                  refine ⟨403501656313945514644429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8608035334697504312414485 403501656313945514644429)
                  ·
                    rfl

theorem cell23_7072350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_7072350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072350 prefixEnd_7072350 := by exact prefixLift 7072350
  have htrace : WordTrace (prefixWord ++ tailWord_7072350) baseStart_7072350 baseEnd_7072350 := by
    simpa [prefixWord, tailWord_7072350, baseEnd_7072350] using wordTrace_append hprefix tailTrace_7072350
  have hstable : (prefixWord ++ tailWord_7072350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072350).length < 2 ^ (prefixWord ++ tailWord_7072350).sum := by decide
  have hdescent : baseEnd_7072350 < baseStart_7072350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072355 : List Nat := [1, 1, 1, 5, 1, 2, 12]
def baseStart_7072355 : Nat := 118140960795 + 7072355 * 2 ^ 59
def prefixEnd_7072355 : Nat := 4983230072969 + 3 ^ 40 * 7072355 * 2
def baseEnd_7072355 : Nat := 44833549064552865583177

theorem tailTrace_7072355 : CollatzResearch.WordTrace tailWord_7072355 prefixEnd_7072355 44833549064552865583177 := by
  unfold tailWord_7072355
  simp only [CollatzResearch.WordTrace]
  refine ⟨257949978293073171916298519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171966652195382114610865679 257949978293073171916298519)
  ·
    refine ⟨386924967439609757874447779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257949978293073171916298519 386924967439609757874447779)
    ·
      refine ⟨580387451159414636811671669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386924967439609757874447779 580387451159414636811671669)
      ·
        refine ⟨54411323546195122201094219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 580387451159414636811671669 54411323546195122201094219)
        ·
          refine ⟨81616985319292683301641329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54411323546195122201094219 81616985319292683301641329)
          ·
            refine ⟨61212738989469512476230997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81616985319292683301641329 61212738989469512476230997)
            ·
              refine ⟨44833549064552865583177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 61212738989469512476230997 44833549064552865583177)
              ·
                rfl

theorem cell23_7072355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 12].length) (baseStart_7072355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072355 prefixEnd_7072355 := by exact prefixLift 7072355
  have htrace : WordTrace (prefixWord ++ tailWord_7072355) baseStart_7072355 baseEnd_7072355 := by
    simpa [prefixWord, tailWord_7072355, baseEnd_7072355] using wordTrace_append hprefix tailTrace_7072355
  have hstable : (prefixWord ++ tailWord_7072355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072355).length < 2 ^ (prefixWord ++ tailWord_7072355).sum := by decide
  have hdescent : baseEnd_7072355 < baseStart_7072355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072362 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7072362 : Nat := 118140960795 + 7072362 * 2 ^ 59
def prefixEnd_7072362 : Nat := 4983230072969 + 3 ^ 40 * 7072362 * 2
def baseEnd_7072362 : Nat := 3631521068593363584849805

theorem tailTrace_7072362 : CollatzResearch.WordTrace tailWord_7072362 prefixEnd_7072362 3631521068593363584849805 := by
  unfold tailWord_7072362
  simp only [CollatzResearch.WordTrace]
  refine ⟨64487558401011953027950835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171966822402698541407868893 64487558401011953027950835)
  ·
    refine ⟨96731337601517929541926253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64487558401011953027950835 96731337601517929541926253)
    ·
      refine ⟨36274251600569223578222345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96731337601517929541926253 36274251600569223578222345)
      ·
        refine ⟨27205688700426917683666759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36274251600569223578222345 27205688700426917683666759)
        ·
          refine ⟨40808533050640376525500139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27205688700426917683666759 40808533050640376525500139)
          ·
            refine ⟨61212799575960564788250209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40808533050640376525500139 61212799575960564788250209)
            ·
              refine ⟨45909599681970423591187657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61212799575960564788250209 45909599681970423591187657)
              ·
                refine ⟨34432199761477817693390743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45909599681970423591187657 34432199761477817693390743)
                ·
                  refine ⟨51648299642216726540086115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34432199761477817693390743 51648299642216726540086115)
                  ·
                    refine ⟨77472449463325089810129173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51648299642216726540086115 77472449463325089810129173)
                    ·
                      refine ⟨3631521068593363584849805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77472449463325089810129173 3631521068593363584849805)
                      ·
                        rfl

theorem cell23_7072362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7072362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072362 prefixEnd_7072362 := by exact prefixLift 7072362
  have htrace : WordTrace (prefixWord ++ tailWord_7072362) baseStart_7072362 baseEnd_7072362 := by
    simpa [prefixWord, tailWord_7072362, baseEnd_7072362] using wordTrace_append hprefix tailTrace_7072362
  have hstable : (prefixWord ++ tailWord_7072362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072362).length < 2 ^ (prefixWord ++ tailWord_7072362).sum := by decide
  have hdescent : baseEnd_7072362 < baseStart_7072362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072389 : List Nat := [1, 3, 1, 1, 4, 4, 2, 7]
def baseStart_7072389 : Nat := 118140960795 + 7072389 * 2 ^ 59
def prefixEnd_7072389 : Nat := 4983230072969 + 3 ^ 40 * 7072389 * 2
def baseEnd_7072389 : Nat := 134501293798927221452303

theorem tailTrace_7072389 : CollatzResearch.WordTrace tailWord_7072389 prefixEnd_7072389 134501293798927221452303 := by
  unfold tailWord_7072389
  simp only [CollatzResearch.WordTrace]
  refine ⟨257951218374949995723036221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171967478916633330482024147 257951218374949995723036221)
  ·
    refine ⟨96731706890606248396138583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257951218374949995723036221 96731706890606248396138583)
    ·
      refine ⟨145097560335909372594207875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96731706890606248396138583 145097560335909372594207875)
      ·
        refine ⟨217646340503864058891311813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145097560335909372594207875 217646340503864058891311813)
        ·
          refine ⟨40808688844474511042120965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217646340503864058891311813 40808688844474511042120965)
          ·
            refine ⟨7651629158338970820397681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40808688844474511042120965 7651629158338970820397681)
            ·
              refine ⟨5738721868754228115298261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7651629158338970820397681 5738721868754228115298261)
              ·
                refine ⟨134501293798927221452303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5738721868754228115298261 134501293798927221452303)
                ·
                  rfl

theorem cell23_7072389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 7].length) (baseStart_7072389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072389 prefixEnd_7072389 := by exact prefixLift 7072389
  have htrace : WordTrace (prefixWord ++ tailWord_7072389) baseStart_7072389 baseEnd_7072389 := by
    simpa [prefixWord, tailWord_7072389, baseEnd_7072389] using wordTrace_append hprefix tailTrace_7072389
  have hstable : (prefixWord ++ tailWord_7072389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072389).length < 2 ^ (prefixWord ++ tailWord_7072389).sum := by decide
  have hdescent : baseEnd_7072389 < baseStart_7072389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072417 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7072417 : Nat := 118140960795 + 7072417 * 2 ^ 59
def prefixEnd_7072417 : Nat := 4983230072969 + 3 ^ 40 * 7072417 * 2
def baseEnd_7072417 : Nat := 3631549310029360869662053

theorem tailTrace_7072417 : CollatzResearch.WordTrace tailWord_7072417 prefixEnd_7072417 3631549310029360869662053 := by
  unfold tailWord_7072417
  simp only [CollatzResearch.WordTrace]
  refine ⟨257952239618848556505055505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171968159745899037670037003 257952239618848556505055505)
  ·
    refine ⟨193464179714136417378791629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257952239618848556505055505 193464179714136417378791629)
    ·
      refine ⟨72549067392801156517046861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193464179714136417378791629 72549067392801156517046861)
      ·
        refine ⟨27205900272300433693892573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72549067392801156517046861 27205900272300433693892573)
        ·
          refine ⟨10202212602112662635209715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27205900272300433693892573 10202212602112662635209715)
          ·
            refine ⟨15303318903168993952814573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10202212602112662635209715 15303318903168993952814573)
            ·
              refine ⟨5738744588688372732305465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15303318903168993952814573 5738744588688372732305465)
              ·
                refine ⟨4304058441516279549229099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738744588688372732305465 4304058441516279549229099)
                ·
                  refine ⟨6456087662274419323843649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304058441516279549229099 6456087662274419323843649)
                  ·
                    refine ⟨4842065746705814492882737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456087662274419323843649 4842065746705814492882737)
                    ·
                      refine ⟨3631549310029360869662053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842065746705814492882737 3631549310029360869662053)
                      ·
                        rfl

theorem cell23_7072417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7072417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072417 prefixEnd_7072417 := by exact prefixLift 7072417
  have htrace : WordTrace (prefixWord ++ tailWord_7072417) baseStart_7072417 baseEnd_7072417 := by
    simpa [prefixWord, tailWord_7072417, baseEnd_7072417] using wordTrace_append hprefix tailTrace_7072417
  have hstable : (prefixWord ++ tailWord_7072417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072417).length < 2 ^ (prefixWord ++ tailWord_7072417).sum := by decide
  have hdescent : baseEnd_7072417 < baseStart_7072417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072442 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_7072442 : Nat := 118140960795 + 7072442 * 2 ^ 59
def prefixEnd_7072442 : Nat := 4983230072969 + 3 ^ 40 * 7072442 * 2
def baseEnd_7072442 : Nat := 3631562147045723271849437

theorem tailTrace_7072442 : CollatzResearch.WordTrace tailWord_7072442 prefixEnd_7072442 3631562147045723271849437 := by
  unfold tailWord_7072442
  simp only [CollatzResearch.WordTrace]
  refine ⟨64488287860939496443678895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171968767629171990516477053 64488287860939496443678895)
  ·
    refine ⟨96732431791409244665518343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64488287860939496443678895 96732431791409244665518343)
    ·
      refine ⟨145098647687113866998277515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96732431791409244665518343 145098647687113866998277515)
      ·
        refine ⟨217647971530670800497416273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145098647687113866998277515 217647971530670800497416273)
        ·
          refine ⟨163235978648003100373062205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217647971530670800497416273 163235978648003100373062205)
          ·
            refine ⟨61213491993001162639898327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163235978648003100373062205 61213491993001162639898327)
            ·
              refine ⟨91820237989501743959847491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61213491993001162639898327 91820237989501743959847491)
              ·
                refine ⟨137730356984252615939771237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91820237989501743959847491 137730356984252615939771237)
                ·
                  refine ⟨25824441934547365488707107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137730356984252615939771237 25824441934547365488707107)
                  ·
                    refine ⟨38736662901821048233060661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25824441934547365488707107 38736662901821048233060661)
                    ·
                      refine ⟨3631562147045723271849437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38736662901821048233060661 3631562147045723271849437)
                      ·
                        rfl

theorem cell23_7072442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_7072442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072442 prefixEnd_7072442 := by exact prefixLift 7072442
  have htrace : WordTrace (prefixWord ++ tailWord_7072442) baseStart_7072442 baseEnd_7072442 := by
    simpa [prefixWord, tailWord_7072442, baseEnd_7072442] using wordTrace_append hprefix tailTrace_7072442
  have hstable : (prefixWord ++ tailWord_7072442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072442).length < 2 ^ (prefixWord ++ tailWord_7072442).sum := by decide
  have hdescent : baseEnd_7072442 < baseStart_7072442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072456 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_7072456 : Nat := 118140960795 + 7072456 * 2 ^ 59
def prefixEnd_7072456 : Nat := 4983230072969 + 3 ^ 40 * 7072456 * 2
def baseEnd_7072456 : Nat := 3631569335774886217074373

theorem tailTrace_7072456 : CollatzResearch.WordTrace tailWord_7072456 prefixEnd_7072456 3631569335774886217074373 := by
  unfold tailWord_7072456
  simp only [CollatzResearch.WordTrace]
  refine ⟨128976831032853633082862611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171969108043804844110483481 128976831032853633082862611)
  ·
    refine ⟨193465246549280449624293917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128976831032853633082862611 193465246549280449624293917)
    ·
      refine ⟨72549467455980168609110219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193465246549280449624293917 72549467455980168609110219)
      ·
        refine ⟨108824201183970252913665329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72549467455980168609110219 108824201183970252913665329)
        ·
          refine ⟨81618150887977689685248997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108824201183970252913665329 81618150887977689685248997)
          ·
            refine ⟨15303403291495816815984187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81618150887977689685248997 15303403291495816815984187)
            ·
              refine ⟨22955104937243725223976281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15303403291495816815984187 22955104937243725223976281)
              ·
                refine ⟨17216328702932793917982211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22955104937243725223976281 17216328702932793917982211)
                ·
                  refine ⟨25824493054399190876973317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17216328702932793917982211 25824493054399190876973317)
                  ·
                    refine ⟨4842092447699848289432497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25824493054399190876973317 4842092447699848289432497)
                    ·
                      refine ⟨3631569335774886217074373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842092447699848289432497 3631569335774886217074373)
                      ·
                        rfl

theorem cell23_7072456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_7072456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072456 prefixEnd_7072456 := by exact prefixLift 7072456
  have htrace : WordTrace (prefixWord ++ tailWord_7072456) baseStart_7072456 baseEnd_7072456 := by
    simpa [prefixWord, tailWord_7072456, baseEnd_7072456] using wordTrace_append hprefix tailTrace_7072456
  have hstable : (prefixWord ++ tailWord_7072456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072456).length < 2 ^ (prefixWord ++ tailWord_7072456).sum := by decide
  have hdescent : baseEnd_7072456 < baseStart_7072456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072460 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7072460 : Nat := 118140960795 + 7072460 * 2 ^ 59
def prefixEnd_7072460 : Nat := 4983230072969 + 3 ^ 40 * 7072460 * 2
def baseEnd_7072460 : Nat := 3631571389697504201424355

theorem tailTrace_7072460 : CollatzResearch.WordTrace tailWord_7072460 prefixEnd_7072460 3631571389697504201424355 := by
  unfold tailWord_7072460
  simp only [CollatzResearch.WordTrace]
  refine ⟨128976903978846387424435417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171969205305128516565913889 128976903978846387424435417)
  ·
    refine ⟨96732677984134790568326563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128976903978846387424435417 96732677984134790568326563)
    ·
      refine ⟨145099016976202185852489845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96732677984134790568326563 145099016976202185852489845)
      ·
        refine ⟨13603032841518954923670923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145099016976202185852489845 13603032841518954923670923)
        ·
          refine ⟨20404549262278432385506385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13603032841518954923670923 20404549262278432385506385)
          ·
            refine ⟨15303411946708824289129789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20404549262278432385506385 15303411946708824289129789)
            ·
              refine ⟨5738779480015809108423671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15303411946708824289129789 5738779480015809108423671)
              ·
                refine ⟨8608169220023713662635507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738779480015809108423671 8608169220023713662635507)
                ·
                  refine ⟨12912253830035570493953261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608169220023713662635507 12912253830035570493953261)
                  ·
                    refine ⟨4842095186263338935232473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12912253830035570493953261 4842095186263338935232473)
                    ·
                      refine ⟨3631571389697504201424355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842095186263338935232473 3631571389697504201424355)
                      ·
                        rfl

theorem cell23_7072460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7072460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072460 prefixEnd_7072460 := by exact prefixLift 7072460
  have htrace : WordTrace (prefixWord ++ tailWord_7072460) baseStart_7072460 baseEnd_7072460 := by
    simpa [prefixWord, tailWord_7072460, baseEnd_7072460] using wordTrace_append hprefix tailTrace_7072460
  have hstable : (prefixWord ++ tailWord_7072460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072460).length < 2 ^ (prefixWord ++ tailWord_7072460).sum := by decide
  have hdescent : baseEnd_7072460 < baseStart_7072460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072473 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 2, 2, 2]
def baseStart_7072473 : Nat := 118140960795 + 7072473 * 2 ^ 59
def prefixEnd_7072473 : Nat := 4983230072969 + 3 ^ 40 * 7072473 * 2
def baseEnd_7072473 : Nat := 3631578064946012650561795

theorem tailTrace_7072473 : CollatzResearch.WordTrace tailWord_7072473 prefixEnd_7072473 3631578064946012650561795 := by
  unfold tailWord_7072473
  simp only [CollatzResearch.WordTrace]
  refine ⟨257954282106645678069094073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171969521404430452046062715 257954282106645678069094073)
  ·
    refine ⟨193465711579984258551820555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257954282106645678069094073 193465711579984258551820555)
    ·
      refine ⟨290198567369976387827730833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193465711579984258551820555 290198567369976387827730833)
      ·
        refine ⟨217648925527482290870798125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290198567369976387827730833 217648925527482290870798125)
        ·
          refine ⟨81618347072805859076549297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217648925527482290870798125 81618347072805859076549297)
          ·
            refine ⟨61213760304604394307411973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81618347072805859076549297 61213760304604394307411973)
            ·
              refine ⟨11477580057113323932639745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61213760304604394307411973 11477580057113323932639745)
              ·
                refine ⟨8608185042834992949479809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11477580057113323932639745 8608185042834992949479809)
                ·
                  refine ⟨6456138782126244712109857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8608185042834992949479809 6456138782126244712109857)
                  ·
                    refine ⟨4842104086594683534082393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456138782126244712109857 4842104086594683534082393)
                    ·
                      refine ⟨3631578064946012650561795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842104086594683534082393 3631578064946012650561795)
                      ·
                        rfl

theorem cell23_7072473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_7072473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072473 prefixEnd_7072473 := by exact prefixLift 7072473
  have htrace : WordTrace (prefixWord ++ tailWord_7072473) baseStart_7072473 baseEnd_7072473 := by
    simpa [prefixWord, tailWord_7072473, baseEnd_7072473] using wordTrace_append hprefix tailTrace_7072473
  have hstable : (prefixWord ++ tailWord_7072473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072473).length < 2 ^ (prefixWord ++ tailWord_7072473).sum := by decide
  have hdescent : baseEnd_7072473 < baseStart_7072473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072476 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7072476 : Nat := 118140960795 + 7072476 * 2 ^ 59
def prefixEnd_7072476 : Nat := 4983230072969 + 3 ^ 40 * 7072476 * 2
def baseEnd_7072476 : Nat := 3631579605387976138824281

theorem tailTrace_7072476 : CollatzResearch.WordTrace tailWord_7072476 prefixEnd_7072476 3631579605387976138824281 := by
  unfold tailWord_7072476
  simp only [CollatzResearch.WordTrace]
  refine ⟨128977195762817404790726641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171969594350423206387635521 128977195762817404790726641)
  ·
    refine ⟨96732896822113053593044981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128977195762817404790726641 96732896822113053593044981)
    ·
      refine ⟨9068709077073098774347967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96732896822113053593044981 9068709077073098774347967)
      ·
        refine ⟨13603063615609648161521951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068709077073098774347967 13603063615609648161521951)
        ·
          refine ⟨20404595423414472242282927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13603063615609648161521951 20404595423414472242282927)
          ·
            refine ⟨30606893135121708363424391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20404595423414472242282927 30606893135121708363424391)
            ·
              refine ⟨45910339702682562545136587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30606893135121708363424391 45910339702682562545136587)
              ·
                refine ⟨68865509554023843817704881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45910339702682562545136587 68865509554023843817704881)
                ·
                  refine ⟨51649132165517882863278661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68865509554023843817704881 51649132165517882863278661)
                  ·
                    refine ⟨9684212281034603036864749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51649132165517882863278661 9684212281034603036864749)
                    ·
                      refine ⟨3631579605387976138824281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684212281034603036864749 3631579605387976138824281)
                      ·
                        rfl

theorem cell23_7072476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7072476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072476 prefixEnd_7072476 := by exact prefixLift 7072476
  have htrace : WordTrace (prefixWord ++ tailWord_7072476) baseStart_7072476 baseEnd_7072476 := by
    simpa [prefixWord, tailWord_7072476, baseEnd_7072476] using wordTrace_append hprefix tailTrace_7072476
  have hstable : (prefixWord ++ tailWord_7072476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072476).length < 2 ^ (prefixWord ++ tailWord_7072476).sum := by decide
  have hdescent : baseEnd_7072476 < baseStart_7072476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072492 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_7072492 : Nat := 118140960795 + 7072492 * 2 ^ 59
def prefixEnd_7072492 : Nat := 4983230072969 + 3 ^ 40 * 7072492 * 2
def baseEnd_7072492 : Nat := 1210529273692816025408069

theorem tailTrace_7072492 : CollatzResearch.WordTrace tailWord_7072492 prefixEnd_7072492 1210529273692816025408069 := by
  unfold tailWord_7072492
  simp only [CollatzResearch.WordTrace]
  refine ⟨128977487546788422157017865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171969983395717896209357153 128977487546788422157017865)
  ·
    refine ⟨96733115660091316617763399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128977487546788422157017865 96733115660091316617763399)
    ·
      refine ⟨145099673490136974926645099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96733115660091316617763399 145099673490136974926645099)
      ·
        refine ⟨217649510235205462389967649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145099673490136974926645099 217649510235205462389967649)
        ·
          refine ⟨163237132676404096792475737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217649510235205462389967649 163237132676404096792475737)
          ·
            refine ⟨122427849507303072594356803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163237132676404096792475737 122427849507303072594356803)
            ·
              refine ⟨183641774260954608891535205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122427849507303072594356803 183641774260954608891535205)
              ·
                refine ⟨34432832673928989167162851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183641774260954608891535205 34432832673928989167162851)
                ·
                  refine ⟨51649249010893483750744277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34432832673928989167162851 51649249010893483750744277)
                  ·
                    refine ⟨1210529273692816025408069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51649249010893483750744277 1210529273692816025408069)
                    ·
                      rfl

theorem cell23_7072492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_7072492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072492 prefixEnd_7072492 := by exact prefixLift 7072492
  have htrace : WordTrace (prefixWord ++ tailWord_7072492) baseStart_7072492 baseEnd_7072492 := by
    simpa [prefixWord, tailWord_7072492, baseEnd_7072492] using wordTrace_append hprefix tailTrace_7072492
  have hstable : (prefixWord ++ tailWord_7072492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072492).length < 2 ^ (prefixWord ++ tailWord_7072492).sum := by decide
  have hdescent : baseEnd_7072492 < baseStart_7072492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072499 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 5, 2]
def baseStart_7072499 : Nat := 118140960795 + 7072499 * 2 ^ 59
def prefixEnd_7072499 : Nat := 4983230072969 + 3 ^ 40 * 7072499 * 2
def baseEnd_7072499 : Nat := 3631591415443029548836675

theorem tailTrace_7072499 : CollatzResearch.WordTrace tailWord_7072499 prefixEnd_7072499 3631591415443029548836675 := by
  unfold tailWord_7072499
  simp only [CollatzResearch.WordTrace]
  refine ⟨257955230404551484509540551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171970153603034323006360367 257955230404551484509540551)
  ·
    refine ⟨386932845606827226764310827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257955230404551484509540551 386932845606827226764310827)
    ·
      refine ⟨580399268410240840146466241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386932845606827226764310827 580399268410240840146466241)
      ·
        refine ⟨435299451307680630109849681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580399268410240840146466241 435299451307680630109849681)
        ·
          refine ⟨326474588480760472582387261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435299451307680630109849681 326474588480760472582387261)
          ·
            refine ⟨122427970680285177218395223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326474588480760472582387261 122427970680285177218395223)
            ·
              refine ⟨183641956020427765827592835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122427970680285177218395223 183641956020427765827592835)
              ·
                refine ⟨275462934030641648741389253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183641956020427765827592835 275462934030641648741389253)
                ·
                  refine ⟨51649300130745309139010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 275462934030641648741389253 51649300130745309139010485)
                  ·
                    refine ⟨4842121887257372731782233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51649300130745309139010485 4842121887257372731782233)
                    ·
                      refine ⟨3631591415443029548836675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842121887257372731782233 3631591415443029548836675)
                      ·
                        rfl

theorem cell23_7072499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5, 2].length) (baseStart_7072499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072499 prefixEnd_7072499 := by exact prefixLift 7072499
  have htrace : WordTrace (prefixWord ++ tailWord_7072499) baseStart_7072499 baseEnd_7072499 := by
    simpa [prefixWord, tailWord_7072499, baseEnd_7072499] using wordTrace_append hprefix tailTrace_7072499
  have hstable : (prefixWord ++ tailWord_7072499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072499).length < 2 ^ (prefixWord ++ tailWord_7072499).sum := by decide
  have hdescent : baseEnd_7072499 < baseStart_7072499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072529 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_7072529 : Nat := 118140960795 + 7072529 * 2 ^ 59
def prefixEnd_7072529 : Nat := 4983230072969 + 3 ^ 40 * 7072529 * 2
def baseEnd_7072529 : Nat := 3631606819862664431461537

theorem tailTrace_7072529 : CollatzResearch.WordTrace tailWord_7072529 prefixEnd_7072529 3631606819862664431461537 := by
  unfold tailWord_7072529
  simp only [CollatzResearch.WordTrace]
  refine ⟨257956324594442799633132641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171970883062961866422088427 257956324594442799633132641)
  ·
    refine ⟨193467243445832099724849481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257956324594442799633132641 193467243445832099724849481)
    ·
      refine ⟨145100432584374074793637111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193467243445832099724849481 145100432584374074793637111)
      ·
        refine ⟨217650648876561112190455667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145100432584374074793637111 217650648876561112190455667)
        ·
          refine ⟨326475973314841668285683501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217650648876561112190455667 326475973314841668285683501)
          ·
            refine ⟨122428489993065625607131313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326475973314841668285683501 122428489993065625607131313)
            ·
              refine ⟨91821367494799219205348485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122428489993065625607131313 91821367494799219205348485)
              ·
                refine ⟨17216506405274853601002841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91821367494799219205348485 17216506405274853601002841)
                ·
                  refine ⟨12912379803956140200752131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17216506405274853601002841 12912379803956140200752131)
                  ·
                    refine ⟨19368569705934210301128197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12912379803956140200752131 19368569705934210301128197)
                    ·
                      refine ⟨3631606819862664431461537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19368569705934210301128197 3631606819862664431461537)
                      ·
                        rfl

theorem cell23_7072529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_7072529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072529 prefixEnd_7072529 := by exact prefixLift 7072529
  have htrace : WordTrace (prefixWord ++ tailWord_7072529) baseStart_7072529 baseEnd_7072529 := by
    simpa [prefixWord, tailWord_7072529, baseEnd_7072529] using wordTrace_append hprefix tailTrace_7072529
  have hstable : (prefixWord ++ tailWord_7072529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072529).length < 2 ^ (prefixWord ++ tailWord_7072529).sum := by decide
  have hdescent : baseEnd_7072529 < baseStart_7072529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072549 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_7072549 : Nat := 118140960795 + 7072549 * 2 ^ 59
def prefixEnd_7072549 : Nat := 4983230072969 + 3 ^ 40 * 7072549 * 2
def baseEnd_7072549 : Nat := 3631617089475754353211445

theorem tailTrace_7072549 : CollatzResearch.WordTrace tailWord_7072549 prefixEnd_7072549 3631617089475754353211445 := by
  unfold tailWord_7072549
  simp only [CollatzResearch.WordTrace]
  refine ⟨257957054054370343048860701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171971369369580228699240467 257957054054370343048860701)
  ·
    refine ⟨96733895270388878643322763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257957054054370343048860701 96733895270388878643322763)
    ·
      refine ⟨145100842905583317964984145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96733895270388878643322763 145100842905583317964984145)
      ·
        refine ⟨108825632179187488473738109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145100842905583317964984145 108825632179187488473738109)
        ·
          refine ⟨40809612067195308177651791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108825632179187488473738109 40809612067195308177651791)
          ·
            refine ⟨61214418100792962266477687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40809612067195308177651791 61214418100792962266477687)
            ·
              refine ⟨91821627151189443399716531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61214418100792962266477687 91821627151189443399716531)
              ·
                refine ⟨137732440726784165099574797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91821627151189443399716531 137732440726784165099574797)
                ·
                  refine ⟨51649665272544061912340549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137732440726784165099574797 51649665272544061912340549)
                  ·
                    refine ⟨9684312238602011608563853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51649665272544061912340549 9684312238602011608563853)
                    ·
                      refine ⟨3631617089475754353211445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684312238602011608563853 3631617089475754353211445)
                      ·
                        rfl

theorem cell23_7072549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_7072549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072549 prefixEnd_7072549 := by exact prefixLift 7072549
  have htrace : WordTrace (prefixWord ++ tailWord_7072549) baseStart_7072549 baseEnd_7072549 := by
    simpa [prefixWord, tailWord_7072549, baseEnd_7072549] using wordTrace_append hprefix tailTrace_7072549
  have hstable : (prefixWord ++ tailWord_7072549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072549).length < 2 ^ (prefixWord ++ tailWord_7072549).sum := by decide
  have hdescent : baseEnd_7072549 < baseStart_7072549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072580 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7072580 : Nat := 118140960795 + 7072580 * 2 ^ 59
def prefixEnd_7072580 : Nat := 4983230072969 + 3 ^ 40 * 7072580 * 2
def baseEnd_7072580 : Nat := 3631633007376043731923803

theorem tailTrace_7072580 : CollatzResearch.WordTrace tailWord_7072580 prefixEnd_7072580 3631633007376043731923803 := by
  unfold tailWord_7072580
  simp only [CollatzResearch.WordTrace]
  refine ⟨128979092358629017671619597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171972123144838690228826129 128979092358629017671619597)
  ·
    refine ⟨48367159634485881626857349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128979092358629017671619597 48367159634485881626857349)
    ·
      refine ⟨9068842431466102805035753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48367159634485881626857349 9068842431466102805035753)
      ·
        refine ⟨6801631823599577103776815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9068842431466102805035753 6801631823599577103776815)
        ·
          refine ⟨10202447735399365655665223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801631823599577103776815 10202447735399365655665223)
          ·
            refine ⟨15303671603099048483497835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10202447735399365655665223 15303671603099048483497835)
            ·
              refine ⟨22955507404648572725246753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15303671603099048483497835 22955507404648572725246753)
              ·
                refine ⟨17216630553486429543935065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22955507404648572725246753 17216630553486429543935065)
                ·
                  refine ⟨12912472915114822157951299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17216630553486429543935065 12912472915114822157951299)
                  ·
                    refine ⟨19368709372672233236926949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12912472915114822157951299 19368709372672233236926949)
                    ·
                      refine ⟨3631633007376043731923803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19368709372672233236926949 3631633007376043731923803)
                      ·
                        rfl

theorem cell23_7072580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7072580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072580 prefixEnd_7072580 := by exact prefixLift 7072580
  have htrace : WordTrace (prefixWord ++ tailWord_7072580) baseStart_7072580 baseEnd_7072580 := by
    simpa [prefixWord, tailWord_7072580, baseEnd_7072580] using wordTrace_append hprefix tailTrace_7072580
  have hstable : (prefixWord ++ tailWord_7072580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072580).length < 2 ^ (prefixWord ++ tailWord_7072580).sum := by decide
  have hdescent : baseEnd_7072580 < baseStart_7072580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072616 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7072616 : Nat := 118140960795 + 7072616 * 2 ^ 59
def prefixEnd_7072616 : Nat := 4983230072969 + 3 ^ 40 * 7072616 * 2
def baseEnd_7072616 : Nat := 1210550497559868530357879

theorem tailTrace_7072616 : CollatzResearch.WordTrace tailWord_7072616 prefixEnd_7072616 1210550497559868530357879 := by
  unfold tailWord_7072616
  simp only [CollatzResearch.WordTrace]
  refine ⟨128979748872563806745774851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171972998496751742327699801 128979748872563806745774851)
  ·
    refine ⟨193469623308845710118662277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128979748872563806745774851 193469623308845710118662277)
    ·
      refine ⟨36275554370408570647249177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193469623308845710118662277 36275554370408570647249177)
      ·
        refine ⟨27206665777806427985436883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36275554370408570647249177 27206665777806427985436883)
        ·
          refine ⟨40809998666709641978155325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27206665777806427985436883 40809998666709641978155325)
          ·
            refine ⟨15303749500016115741808247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40809998666709641978155325 15303749500016115741808247)
            ·
              refine ⟨22955624250024173612712371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15303749500016115741808247 22955624250024173612712371)
              ·
                refine ⟨34433436375036260419068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22955624250024173612712371 34433436375036260419068557)
                ·
                  refine ⟨12912538640638597657150709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34433436375036260419068557 12912538640638597657150709)
                  ·
                    refine ⟨1210550497559868530357879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12912538640638597657150709 1210550497559868530357879)
                    ·
                      rfl

theorem cell23_7072616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7072616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072616 prefixEnd_7072616 := by exact prefixLift 7072616
  have htrace : WordTrace (prefixWord ++ tailWord_7072616) baseStart_7072616 baseEnd_7072616 := by
    simpa [prefixWord, tailWord_7072616, baseEnd_7072616] using wordTrace_append hprefix tailTrace_7072616
  have hstable : (prefixWord ++ tailWord_7072616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072616).length < 2 ^ (prefixWord ++ tailWord_7072616).sum := by decide
  have hdescent : baseEnd_7072616 < baseStart_7072616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072633 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 1, 5]
def baseStart_7072633 : Nat := 118140960795 + 7072633 * 2 ^ 59
def prefixEnd_7072633 : Nat := 4983230072969 + 3 ^ 40 * 7072633 * 2
def baseEnd_7072633 : Nat := 1210553407283577341520353

theorem tailTrace_7072633 : CollatzResearch.WordTrace tailWord_7072633 prefixEnd_7072633 1210553407283577341520353 := by
  unfold tailWord_7072633
  simp only [CollatzResearch.WordTrace]
  refine ⟨257960117786066025394918553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171973411857377350263279035 257960117786066025394918553)
  ·
    refine ⟨193470088339549519046188915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257960117786066025394918553 193470088339549519046188915)
    ·
      refine ⟨290205132509324278569283373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193470088339549519046188915 290205132509324278569283373)
      ·
        refine ⟨108826924690996604463481265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290205132509324278569283373 108826924690996604463481265)
        ·
          refine ⟨81620193518247453347610949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108826924690996604463481265 81620193518247453347610949)
          ·
            refine ⟨15303786284671397502677053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81620193518247453347610949 15303786284671397502677053)
            ·
              refine ⟨5738919856751774063503895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15303786284671397502677053 5738919856751774063503895)
              ·
                refine ⟨8608379785127661095255843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738919856751774063503895 8608379785127661095255843)
                ·
                  refine ⟨12912569677691491642883765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608379785127661095255843 12912569677691491642883765)
                  ·
                    refine ⟨1210553407283577341520353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12912569677691491642883765 1210553407283577341520353)
                    ·
                      rfl

theorem cell23_7072633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_7072633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072633 prefixEnd_7072633 := by exact prefixLift 7072633
  have htrace : WordTrace (prefixWord ++ tailWord_7072633) baseStart_7072633 baseEnd_7072633 := by
    simpa [prefixWord, tailWord_7072633, baseEnd_7072633] using wordTrace_append hprefix tailTrace_7072633
  have hstable : (prefixWord ++ tailWord_7072633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072633).length < 2 ^ (prefixWord ++ tailWord_7072633).sum := by decide
  have hdescent : baseEnd_7072633 < baseStart_7072633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072636 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_7072636 : Nat := 118140960795 + 7072636 * 2 ^ 59
def prefixEnd_7072636 : Nat := 4983230072969 + 3 ^ 40 * 7072636 * 2
def baseEnd_7072636 : Nat := 3631661762292695512823545

theorem tailTrace_7072636 : CollatzResearch.WordTrace tailWord_7072636 prefixEnd_7072636 3631661762292695512823545 := by
  unfold tailWord_7072636
  simp only [CollatzResearch.WordTrace]
  refine ⟨128980113602527578453638881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171973484803370104604851841 128980113602527578453638881)
  ·
    refine ⟨96735085201895683840229161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128980113602527578453638881 96735085201895683840229161)
    ·
      refine ⟨72551313901421762880171871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96735085201895683840229161 72551313901421762880171871)
      ·
        refine ⟨108826970852132644320257807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72551313901421762880171871 108826970852132644320257807)
        ·
          refine ⟨163240456278198966480386711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108826970852132644320257807 163240456278198966480386711)
          ·
            refine ⟨244860684417298449720580067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163240456278198966480386711 244860684417298449720580067)
            ·
              refine ⟨367291026625947674580870101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244860684417298449720580067 367291026625947674580870101)
              ·
                refine ⟨8608383436545648622989143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367291026625947674580870101 8608383436545648622989143)
                ·
                  refine ⟨12912575154818472934483715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608383436545648622989143 12912575154818472934483715)
                  ·
                    refine ⟨19368862732227709401725573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12912575154818472934483715 19368862732227709401725573)
                    ·
                      refine ⟨3631661762292695512823545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19368862732227709401725573 3631661762292695512823545)
                      ·
                        rfl

theorem cell23_7072636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_7072636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072636 prefixEnd_7072636 := by exact prefixLift 7072636
  have htrace : WordTrace (prefixWord ++ tailWord_7072636) baseStart_7072636 baseEnd_7072636 := by
    simpa [prefixWord, tailWord_7072636, baseEnd_7072636] using wordTrace_append hprefix tailTrace_7072636
  have hstable : (prefixWord ++ tailWord_7072636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072636).length < 2 ^ (prefixWord ++ tailWord_7072636).sum := by decide
  have hdescent : baseEnd_7072636 < baseStart_7072636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072647 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_7072647 : Nat := 118140960795 + 7072647 * 2 ^ 59
def prefixEnd_7072647 : Nat := 4983230072969 + 3 ^ 40 * 7072647 * 2
def baseEnd_7072647 : Nat := 3631667410579894969785995

theorem tailTrace_7072647 : CollatzResearch.WordTrace tailWord_7072647 prefixEnd_7072647 3631667410579894969785995 := by
  unfold tailWord_7072647
  simp only [CollatzResearch.WordTrace]
  refine ⟨257960628408015305785928195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171973752272010203857285463 257960628408015305785928195)
  ·
    refine ⟨386940942612022958678892293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257960628408015305785928195 386940942612022958678892293)
    ·
      refine ⟨72551426739754304752292305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 386940942612022958678892293 72551426739754304752292305)
      ·
        refine ⟨54413570054815728564219229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72551426739754304752292305 54413570054815728564219229)
        ·
          refine ⟨20405088770555898211582211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54413570054815728564219229 20405088770555898211582211)
          ·
            refine ⟨30607633155833847317373317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405088770555898211582211 30607633155833847317373317)
            ·
              refine ⟨5738931216718846372007497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30607633155833847317373317 5738931216718846372007497)
              ·
                refine ⟨4304198412539134779005623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738931216718846372007497 4304198412539134779005623)
                ·
                  refine ⟨6456297618808702168508435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304198412539134779005623 6456297618808702168508435)
                  ·
                    refine ⟨9684446428213053252762653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6456297618808702168508435 9684446428213053252762653)
                    ·
                      refine ⟨3631667410579894969785995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684446428213053252762653 3631667410579894969785995)
                      ·
                        rfl

theorem cell23_7072647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_7072647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072647 prefixEnd_7072647 := by exact prefixLift 7072647
  have htrace : WordTrace (prefixWord ++ tailWord_7072647) baseStart_7072647 baseEnd_7072647 := by
    simpa [prefixWord, tailWord_7072647, baseEnd_7072647] using wordTrace_append hprefix tailTrace_7072647
  have hstable : (prefixWord ++ tailWord_7072647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072647).length < 2 ^ (prefixWord ++ tailWord_7072647).sum := by decide
  have hdescent : baseEnd_7072647 < baseStart_7072647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072673 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7072673 : Nat := 118140960795 + 7072673 * 2 ^ 59
def prefixEnd_7072673 : Nat := 4983230072969 + 3 ^ 40 * 7072673 * 2
def baseEnd_7072673 : Nat := 3631680761076911868060875

theorem tailTrace_7072673 : CollatzResearch.WordTrace tailWord_7072673 prefixEnd_7072673 3631680761076911868060875 := by
  unfold tailWord_7072673
  simp only [CollatzResearch.WordTrace]
  refine ⟨257961576705921112226374673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171974384470614074817583115 257961576705921112226374673)
  ·
    refine ⟨193471182529440834169781005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257961576705921112226374673 193471182529440834169781005)
    ·
      refine ⟨72551693448540312813667877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193471182529440834169781005 72551693448540312813667877)
      ·
        refine ⟨13603442521601308652562727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72551693448540312813667877 13603442521601308652562727)
        ·
          refine ⟨20405163782401962978844091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13603442521601308652562727 20405163782401962978844091)
          ·
            refine ⟨30607745673602944468266137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405163782401962978844091 30607745673602944468266137)
            ·
              refine ⟨22955809255202208351199603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30607745673602944468266137 22955809255202208351199603)
              ·
                refine ⟨34433713882803312526799405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22955809255202208351199603 34433713882803312526799405)
                ·
                  refine ⟨12912642706051242197549777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34433713882803312526799405 12912642706051242197549777)
                  ·
                    refine ⟨9684482029538431648162333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12912642706051242197549777 9684482029538431648162333)
                    ·
                      refine ⟨3631680761076911868060875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684482029538431648162333 3631680761076911868060875)
                      ·
                        rfl

theorem cell23_7072673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7072673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072673 prefixEnd_7072673 := by exact prefixLift 7072673
  have htrace : WordTrace (prefixWord ++ tailWord_7072673) baseStart_7072673 baseEnd_7072673 := by
    simpa [prefixWord, tailWord_7072673, baseEnd_7072673] using wordTrace_append hprefix tailTrace_7072673
  have hstable : (prefixWord ++ tailWord_7072673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072673).length < 2 ^ (prefixWord ++ tailWord_7072673).sum := by decide
  have hdescent : baseEnd_7072673 < baseStart_7072673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072676 : List Nat := [2, 3, 1, 2, 1, 2, 5, 7]
def baseStart_7072676 : Nat := 118140960795 + 7072676 * 2 ^ 59
def prefixEnd_7072676 : Nat := 4983230072969 + 3 ^ 40 * 7072676 * 2
def baseEnd_7072676 : Nat := 134506751908106494678643

theorem tailTrace_7072676 : CollatzResearch.WordTrace tailWord_7072676 prefixEnd_7072676 134506751908106494678643 := by
  unfold tailWord_7072676
  simp only [CollatzResearch.WordTrace]
  refine ⟨128980843062455121869366941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171974457416606829159155921 128980843062455121869366941)
  ·
    refine ⟨48367816148420670701012603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128980843062455121869366941 48367816148420670701012603)
    ·
      refine ⟨72551724222631006051518905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48367816148420670701012603 72551724222631006051518905)
      ·
        refine ⟨54413793166973254538639179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72551724222631006051518905 54413793166973254538639179)
        ·
          refine ⟨81620689750459881807958769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54413793166973254538639179 81620689750459881807958769)
          ·
            refine ⟨61215517312844911355969077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81620689750459881807958769 61215517312844911355969077)
            ·
              refine ⟨5738954748079210439622101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61215517312844911355969077 5738954748079210439622101)
              ·
                refine ⟨134506751908106494678643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5738954748079210439622101 134506751908106494678643)
                ·
                  rfl

theorem cell23_7072676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 7].length) (baseStart_7072676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072676 prefixEnd_7072676 := by exact prefixLift 7072676
  have htrace : WordTrace (prefixWord ++ tailWord_7072676) baseStart_7072676 baseEnd_7072676 := by
    simpa [prefixWord, tailWord_7072676, baseEnd_7072676] using wordTrace_append hprefix tailTrace_7072676
  have hstable : (prefixWord ++ tailWord_7072676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072676).length < 2 ^ (prefixWord ++ tailWord_7072676).sum := by decide
  have hdescent : baseEnd_7072676 < baseStart_7072676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072703 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 3]
def baseStart_7072703 : Nat := 118140960795 + 7072703 * 2 ^ 59
def prefixEnd_7072703 : Nat := 4983230072969 + 3 ^ 40 * 7072703 * 2
def baseEnd_7072703 : Nat := 3631696165496546750685737

theorem tailTrace_7072703 : CollatzResearch.WordTrace tailWord_7072703 prefixEnd_7072703 3631696165496546750685737 := by
  unfold tailWord_7072703
  simp only [CollatzResearch.WordTrace]
  refine ⟨257962670895812427349966763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171975113930541618233311175 257962670895812427349966763)
  ·
    refine ⟨386944006343718641024950145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257962670895812427349966763 386944006343718641024950145)
    ·
      refine ⟨290208004757788980768712609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386944006343718641024950145 290208004757788980768712609)
      ·
        refine ⟨217656003568341735576534457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290208004757788980768712609 217656003568341735576534457)
        ·
          refine ⟨163242002676256301682400843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217656003568341735576534457 163242002676256301682400843)
          ·
            refine ⟨244863004014384452523601265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163242002676256301682400843 244863004014384452523601265)
            ·
              refine ⟨183647253010788339392700949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244863004014384452523601265 183647253010788339392700949)
              ·
                refine ⟨8608464984880703409032857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183647253010788339392700949 8608464984880703409032857)
                ·
                  refine ⟨6456348738660527556774643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8608464984880703409032857 6456348738660527556774643)
                  ·
                    refine ⟨9684523107990791335161965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6456348738660527556774643 9684523107990791335161965)
                    ·
                      refine ⟨3631696165496546750685737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684523107990791335161965 3631696165496546750685737)
                      ·
                        rfl

theorem cell23_7072703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_7072703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072703 prefixEnd_7072703 := by exact prefixLift 7072703
  have htrace : WordTrace (prefixWord ++ tailWord_7072703) baseStart_7072703 baseEnd_7072703 := by
    simpa [prefixWord, tailWord_7072703, baseEnd_7072703] using wordTrace_append hprefix tailTrace_7072703
  have hstable : (prefixWord ++ tailWord_7072703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072703).length < 2 ^ (prefixWord ++ tailWord_7072703).sum := by decide
  have hdescent : baseEnd_7072703 < baseStart_7072703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072717 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7072717 : Nat := 118140960795 + 7072717 * 2 ^ 59
def prefixEnd_7072717 : Nat := 4983230072969 + 3 ^ 40 * 7072717 * 2
def baseEnd_7072717 : Nat := 3631703354225709695910673

theorem tailTrace_7072717 : CollatzResearch.WordTrace tailWord_7072717 prefixEnd_7072717 3631703354225709695910673 := by
  unfold tailWord_7072717
  simp only [CollatzResearch.WordTrace]
  refine ⟨257963181517761707740976405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171975454345174471827317603 257963181517761707740976405)
  ·
    refine ⟨12092024133645080050358269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 257963181517761707740976405 12092024133645080050358269)
    ·
      refine ⟨4534509050116905018884351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12092024133645080050358269 4534509050116905018884351)
      ·
        refine ⟨6801763575175357528326527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534509050116905018884351 6801763575175357528326527)
        ·
          refine ⟨10202645362763036292489791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801763575175357528326527 10202645362763036292489791)
          ·
            refine ⟨15303968044144554438734687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10202645362763036292489791 15303968044144554438734687)
            ·
              refine ⟨22955952066216831658102031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15303968044144554438734687 22955952066216831658102031)
              ·
                refine ⟨34433928099325247487153047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22955952066216831658102031 34433928099325247487153047)
                ·
                  refine ⟨51650892148987871230729571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34433928099325247487153047 51650892148987871230729571)
                  ·
                    refine ⟨77476338223481806846094357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51650892148987871230729571 77476338223481806846094357)
                    ·
                      refine ⟨3631703354225709695910673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77476338223481806846094357 3631703354225709695910673)
                      ·
                        rfl

theorem cell23_7072717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7072717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072717 prefixEnd_7072717 := by exact prefixLift 7072717
  have htrace : WordTrace (prefixWord ++ tailWord_7072717) baseStart_7072717 baseEnd_7072717 := by
    simpa [prefixWord, tailWord_7072717, baseEnd_7072717] using wordTrace_append hprefix tailTrace_7072717
  have hstable : (prefixWord ++ tailWord_7072717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072717).length < 2 ^ (prefixWord ++ tailWord_7072717).sum := by decide
  have hdescent : baseEnd_7072717 < baseStart_7072717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072730 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_7072730 : Nat := 118140960795 + 7072730 * 2 ^ 59
def prefixEnd_7072730 : Nat := 4983230072969 + 3 ^ 40 * 7072730 * 2
def baseEnd_7072730 : Nat := 3631710029474218145048113

theorem tailTrace_7072730 : CollatzResearch.WordTrace tailWord_7072730 prefixEnd_7072730 3631710029474218145048113 := by
  unfold tailWord_7072730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64490913916678652740299911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171975770444476407307466429 64490913916678652740299911)
  ·
    refine ⟨96736370875017979110449867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64490913916678652740299911 96736370875017979110449867)
    ·
      refine ⟨145104556312526968665674801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96736370875017979110449867 145104556312526968665674801)
      ·
        refine ⟨108828417234395226499256101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145104556312526968665674801 108828417234395226499256101)
        ·
          refine ⟨20405328231449104968610519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108828417234395226499256101 20405328231449104968610519)
          ·
            refine ⟨30607992347173657452915779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405328231449104968610519 30607992347173657452915779)
            ·
              refine ⟨45911988520760486179373669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30607992347173657452915779 45911988520760486179373669)
              ·
                refine ⟨8608497847642591158632563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45911988520760486179373669 8608497847642591158632563)
                ·
                  refine ⟨12912746771463886737948845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608497847642591158632563 12912746771463886737948845)
                  ·
                    refine ⟨4842280039298957526730817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12912746771463886737948845 4842280039298957526730817)
                    ·
                      refine ⟨3631710029474218145048113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842280039298957526730817 3631710029474218145048113)
                      ·
                        rfl

theorem cell23_7072730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_7072730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072730 prefixEnd_7072730 := by exact prefixLift 7072730
  have htrace : WordTrace (prefixWord ++ tailWord_7072730) baseStart_7072730 baseEnd_7072730 := by
    simpa [prefixWord, tailWord_7072730, baseEnd_7072730] using wordTrace_append hprefix tailTrace_7072730
  have hstable : (prefixWord ++ tailWord_7072730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072730).length < 2 ^ (prefixWord ++ tailWord_7072730).sum := by decide
  have hdescent : baseEnd_7072730 < baseStart_7072730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072746 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7072746 : Nat := 118140960795 + 7072746 * 2 ^ 59
def prefixEnd_7072746 : Nat := 4983230072969 + 3 ^ 40 * 7072746 * 2
def baseEnd_7072746 : Nat := 3631718245164690082448039

theorem tailTrace_7072746 : CollatzResearch.WordTrace tailWord_7072746 prefixEnd_7072746 3631718245164690082448039 := by
  unfold tailWord_7072746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64491059808664161423445523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171976159489771097129188061 64491059808664161423445523)
  ·
    refine ⟨96736589712996242135168285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64491059808664161423445523 96736589712996242135168285)
    ·
      refine ⟨36276221142373590800688107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96736589712996242135168285 36276221142373590800688107)
      ·
        refine ⟨54414331713560386201032161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36276221142373590800688107 54414331713560386201032161)
        ·
          refine ⟨40810748785170289650774121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54414331713560386201032161 40810748785170289650774121)
          ·
            refine ⟨30608061588877717238080591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40810748785170289650774121 30608061588877717238080591)
            ·
              refine ⟨45912092383316575857120887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30608061588877717238080591 45912092383316575857120887)
              ·
                refine ⟨68868138574974863785681331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45912092383316575857120887 68868138574974863785681331)
                ·
                  refine ⟨103302207862462295678521997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68868138574974863785681331 103302207862462295678521997)
                  ·
                    refine ⟨38738327948423360879445749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103302207862462295678521997 38738327948423360879445749)
                    ·
                      refine ⟨3631718245164690082448039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38738327948423360879445749 3631718245164690082448039)
                      ·
                        rfl

theorem cell23_7072746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7072746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072746 prefixEnd_7072746 := by exact prefixLift 7072746
  have htrace : WordTrace (prefixWord ++ tailWord_7072746) baseStart_7072746 baseEnd_7072746 := by
    simpa [prefixWord, tailWord_7072746, baseEnd_7072746] using wordTrace_append hprefix tailTrace_7072746
  have hstable : (prefixWord ++ tailWord_7072746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072746).length < 2 ^ (prefixWord ++ tailWord_7072746).sum := by decide
  have hdescent : baseEnd_7072746 < baseStart_7072746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072760 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_7072760 : Nat := 118140960795 + 7072760 * 2 ^ 59
def prefixEnd_7072760 : Nat := 4983230072969 + 3 ^ 40 * 7072760 * 2
def baseEnd_7072760 : Nat := 3631725433893853027672975

theorem tailTrace_7072760 : CollatzResearch.WordTrace tailWord_7072760 prefixEnd_7072760 3631725433893853027672975 := by
  unfold tailWord_7072760
  simp only [CollatzResearch.WordTrace]
  refine ⟨128982374928302963042395867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171976499904403950723194489 128982374928302963042395867)
  ·
    refine ⟨193473562392454444563593801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128982374928302963042395867 193473562392454444563593801)
    ·
      refine ⟨145105171794340833422695351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193473562392454444563593801 145105171794340833422695351)
      ·
        refine ⟨217657757691511250134043027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145105171794340833422695351 217657757691511250134043027)
        ·
          refine ⟨326486636537266875201064541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217657757691511250134043027 326486636537266875201064541)
          ·
            refine ⟨122432488701475078200399203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326486636537266875201064541 122432488701475078200399203)
            ·
              refine ⟨183648733052212617300598805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122432488701475078200399203 183648733052212617300598805)
              ·
                refine ⟨8608534361822466435965569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183648733052212617300598805 8608534361822466435965569)
                ·
                  refine ⟨6456400771366849826974177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8608534361822466435965569 6456400771366849826974177)
                  ·
                    refine ⟨4842300578525137370230633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456400771366849826974177 4842300578525137370230633)
                    ·
                      refine ⟨3631725433893853027672975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842300578525137370230633 3631725433893853027672975)
                      ·
                        rfl

theorem cell23_7072760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_7072760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072760 prefixEnd_7072760 := by exact prefixLift 7072760
  have htrace : WordTrace (prefixWord ++ tailWord_7072760) baseStart_7072760 baseEnd_7072760 := by
    simpa [prefixWord, tailWord_7072760, baseEnd_7072760] using wordTrace_append hprefix tailTrace_7072760
  have hstable : (prefixWord ++ tailWord_7072760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072760).length < 2 ^ (prefixWord ++ tailWord_7072760).sum := by decide
  have hdescent : baseEnd_7072760 < baseStart_7072760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072850 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_7072850 : Nat := 118140960795 + 7072850 * 2 ^ 59
def prefixEnd_7072850 : Nat := 4983230072969 + 3 ^ 40 * 7072850 * 2
def baseEnd_7072850 : Nat := 3631771647152757675547561

theorem tailTrace_7072850 : CollatzResearch.WordTrace tailWord_7072850 prefixEnd_7072850 3631771647152757675547561 := by
  unfold tailWord_7072850
  simp only [CollatzResearch.WordTrace]
  refine ⟨64492008106569967863892001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171978688284186580970378669 64492008106569967863892001)
  ·
    refine ⟨48369006079927475897919001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64492008106569967863892001 48369006079927475897919001)
    ·
      refine ⟨36276754559945606923439251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48369006079927475897919001 36276754559945606923439251)
      ·
        refine ⟨54415131839918410385158877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36276754559945606923439251 54415131839918410385158877)
        ·
          refine ⟨20405674439969403894434579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54415131839918410385158877 20405674439969403894434579)
          ·
            refine ⟨30608511659954105841651869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405674439969403894434579 30608511659954105841651869)
            ·
              refine ⟨11478191872482789690619451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30608511659954105841651869 11478191872482789690619451)
              ·
                refine ⟨17217287808724184535929177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11478191872482789690619451 17217287808724184535929177)
                ·
                  refine ⟨12912965856543138401946883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17217287808724184535929177 12912965856543138401946883)
                  ·
                    refine ⟨19369448784814707602920325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12912965856543138401946883 19369448784814707602920325)
                    ·
                      refine ⟨3631771647152757675547561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19369448784814707602920325 3631771647152757675547561)
                      ·
                        rfl

theorem cell23_7072850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_7072850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072850 prefixEnd_7072850 := by exact prefixLift 7072850
  have htrace : WordTrace (prefixWord ++ tailWord_7072850) baseStart_7072850 baseEnd_7072850 := by
    simpa [prefixWord, tailWord_7072850, baseEnd_7072850] using wordTrace_append hprefix tailTrace_7072850
  have hstable : (prefixWord ++ tailWord_7072850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072850).length < 2 ^ (prefixWord ++ tailWord_7072850).sum := by decide
  have hdescent : baseEnd_7072850 < baseStart_7072850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072853 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_7072853 : Nat := 118140960795 + 7072853 * 2 ^ 59
def prefixEnd_7072853 : Nat := 4983230072969 + 3 ^ 40 * 7072853 * 2
def baseEnd_7072853 : Nat := 3631773187594721163810047

theorem tailTrace_7072853 : CollatzResearch.WordTrace tailWord_7072853 prefixEnd_7072853 3631773187594721163810047 := by
  unfold tailWord_7072853
  simp only [CollatzResearch.WordTrace]
  refine ⟨257968141845269002967927213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171978761230179335311951475 257968141845269002967927213)
  ·
    refine ⟨96738053191975876112972705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257968141845269002967927213 96738053191975876112972705)
    ·
      refine ⟨72553539893981907084729529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96738053191975876112972705 72553539893981907084729529)
      ·
        refine ⟨54415154920486430313547147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72553539893981907084729529 54415154920486430313547147)
        ·
          refine ⟨81622732380729645470320721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54415154920486430313547147 81622732380729645470320721)
          ·
            refine ⟨61217049285547234102740541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81622732380729645470320721 61217049285547234102740541)
            ·
              refine ⟨22956393482080212788527703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61217049285547234102740541 22956393482080212788527703)
              ·
                refine ⟨34434590223120319182791555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22956393482080212788527703 34434590223120319182791555)
                ·
                  refine ⟨51651885334680478774187333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34434590223120319182791555 51651885334680478774187333)
                  ·
                    refine ⟨9684728500252589770160125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51651885334680478774187333 9684728500252589770160125)
                    ·
                      refine ⟨3631773187594721163810047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684728500252589770160125 3631773187594721163810047)
                      ·
                        rfl

theorem cell23_7072853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_7072853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072853 prefixEnd_7072853 := by exact prefixLift 7072853
  have htrace : WordTrace (prefixWord ++ tailWord_7072853) baseStart_7072853 baseEnd_7072853 := by
    simpa [prefixWord, tailWord_7072853, baseEnd_7072853] using wordTrace_append hprefix tailTrace_7072853
  have hstable : (prefixWord ++ tailWord_7072853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072853).length < 2 ^ (prefixWord ++ tailWord_7072853).sum := by decide
  have hdescent : baseEnd_7072853 < baseStart_7072853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072856 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 8]
def baseStart_7072856 : Nat := 118140960795 + 7072856 * 2 ^ 59
def prefixEnd_7072856 : Nat := 4983230072969 + 3 ^ 40 * 7072856 * 2
def baseEnd_7072856 : Nat := 403530525337409405785837

theorem tailTrace_7072856 : CollatzResearch.WordTrace tailWord_7072856 prefixEnd_7072856 403530525337409405785837 := by
  unfold tailWord_7072856
  simp only [CollatzResearch.WordTrace]
  refine ⟨128984125632129067240143211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171978834176172089653524281 128984125632129067240143211)
  ·
    refine ⟨193476188448193600860214817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128984125632129067240143211 193476188448193600860214817)
    ·
      refine ⟨145107141336145200645161113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193476188448193600860214817 145107141336145200645161113)
      ·
        refine ⟨108830356002108900483870835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145107141336145200645161113 108830356002108900483870835)
        ·
          refine ⟨163245534003163350725806253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108830356002108900483870835 163245534003163350725806253)
          ·
            refine ⟨61217075251186256522177345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163245534003163350725806253 61217075251186256522177345)
            ·
              refine ⟨45912806438389692391633009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61217075251186256522177345 45912806438389692391633009)
              ·
                refine ⟨34434604828792269293724757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45912806438389692391633009 34434604828792269293724757)
                ·
                  refine ⟨403530525337409405785837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34434604828792269293724757 403530525337409405785837)
                  ·
                    rfl

theorem cell23_7072856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_7072856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072856 prefixEnd_7072856 := by exact prefixLift 7072856
  have htrace : WordTrace (prefixWord ++ tailWord_7072856) baseStart_7072856 baseEnd_7072856 := by
    simpa [prefixWord, tailWord_7072856, baseEnd_7072856] using wordTrace_append hprefix tailTrace_7072856
  have hstable : (prefixWord ++ tailWord_7072856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072856).length < 2 ^ (prefixWord ++ tailWord_7072856).sum := by decide
  have hdescent : baseEnd_7072856 < baseStart_7072856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072873 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 6]
def baseStart_7072873 : Nat := 118140960795 + 7072873 * 2 ^ 59
def prefixEnd_7072873 : Nat := 4983230072969 + 3 ^ 40 * 7072873 * 2
def baseEnd_7072873 : Nat := 403531495245312342839995

theorem tailTrace_7072873 : CollatzResearch.WordTrace tailWord_7072873 prefixEnd_7072873 403531495245312342839995 := by
  unfold tailWord_7072873
  simp only [CollatzResearch.WordTrace]
  refine ⟨257968871305196546383655273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171979247536797697589103515 257968871305196546383655273)
  ·
    refine ⟨193476653478897409787741455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257968871305196546383655273 193476653478897409787741455)
    ·
      refine ⟨290214980218346114681612183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193476653478897409787741455 290214980218346114681612183)
      ·
        refine ⟨435322470327519172022418275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290214980218346114681612183 435322470327519172022418275)
        ·
          refine ⟨652983705491278758033627413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435322470327519172022418275 652983705491278758033627413)
          ·
            refine ⟨30608611194903691782826285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 652983705491278758033627413 30608611194903691782826285)
            ·
              refine ⟨11478229198088884418559857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30608611194903691782826285 11478229198088884418559857)
              ·
                refine ⟨8608671898566663313919893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11478229198088884418559857 8608671898566663313919893)
                ·
                  refine ⟨403531495245312342839995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8608671898566663313919893 403531495245312342839995)
                  ·
                    rfl

theorem cell23_7072873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_7072873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072873 prefixEnd_7072873 := by exact prefixLift 7072873
  have htrace : WordTrace (prefixWord ++ tailWord_7072873) baseStart_7072873 baseEnd_7072873 := by
    simpa [prefixWord, tailWord_7072873, baseEnd_7072873] using wordTrace_append hprefix tailTrace_7072873
  have hstable : (prefixWord ++ tailWord_7072873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072873).length < 2 ^ (prefixWord ++ tailWord_7072873).sum := by decide
  have hdescent : baseEnd_7072873 < baseStart_7072873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072876 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7072876 : Nat := 118140960795 + 7072876 * 2 ^ 59
def prefixEnd_7072876 : Nat := 4983230072969 + 3 ^ 40 * 7072876 * 2
def baseEnd_7072876 : Nat := 3631784997649774573822441

theorem tailTrace_7072876 : CollatzResearch.WordTrace tailWord_7072876 prefixEnd_7072876 3631784997649774573822441 := by
  unfold tailWord_7072876
  simp only [CollatzResearch.WordTrace]
  refine ⟨128984490362092838948007241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171979320482790451930676321 128984490362092838948007241)
  ·
    refine ⟨96738367771569629211005431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128984490362092838948007241 96738367771569629211005431)
    ·
      refine ⟨145107551657354443816508147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96738367771569629211005431 145107551657354443816508147)
      ·
        refine ⟨217661327486031665724762221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145107551657354443816508147 217661327486031665724762221)
        ·
          refine ⟨81622997807261874646785833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217661327486031665724762221 81622997807261874646785833)
          ·
            refine ⟨61217248355446405985089375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81622997807261874646785833 61217248355446405985089375)
            ·
              refine ⟨91825872533169608977634063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61217248355446405985089375 91825872533169608977634063)
              ·
                refine ⟨137738808799754413466451095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91825872533169608977634063 137738808799754413466451095)
                ·
                  refine ⟨206608213199631620199676643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137738808799754413466451095 206608213199631620199676643)
                  ·
                    refine ⟨309912319799447430299514965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206608213199631620199676643 309912319799447430299514965)
                    ·
                      refine ⟨3631784997649774573822441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 309912319799447430299514965 3631784997649774573822441)
                      ·
                        rfl

theorem cell23_7072876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7072876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072876 prefixEnd_7072876 := by exact prefixLift 7072876
  have htrace : WordTrace (prefixWord ++ tailWord_7072876) baseStart_7072876 baseEnd_7072876 := by
    simpa [prefixWord, tailWord_7072876, baseEnd_7072876] using wordTrace_append hprefix tailTrace_7072876
  have hstable : (prefixWord ++ tailWord_7072876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072876).length < 2 ^ (prefixWord ++ tailWord_7072876).sum := by decide
  have hdescent : baseEnd_7072876 < baseStart_7072876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072877 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_7072877 : Nat := 118140960795 + 7072877 * 2 ^ 59
def prefixEnd_7072877 : Nat := 4983230072969 + 3 ^ 40 * 7072877 * 2
def baseEnd_7072877 : Nat := 1210595170376809689969979

theorem tailTrace_7072877 : CollatzResearch.WordTrace tailWord_7072877 prefixEnd_7072877 1210595170376809689969979 := by
  unfold tailWord_7072877
  simp only [CollatzResearch.WordTrace]
  refine ⟨257969017197182055066800885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171979344798121370044533923 257969017197182055066800885)
  ·
    refine ⟨24184595362235817662512583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 257969017197182055066800885 24184595362235817662512583)
    ·
      refine ⟨36276893043353726493768875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24184595362235817662512583 36276893043353726493768875)
      ·
        refine ⟨54415339565030589740653313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36276893043353726493768875 54415339565030589740653313)
        ·
          refine ⟨40811504673772942305489985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54415339565030589740653313 40811504673772942305489985)
          ·
            refine ⟨30608628505329706729117489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40811504673772942305489985 30608628505329706729117489)
            ·
              refine ⟨22956471378997280046838117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30608628505329706729117489 22956471378997280046838117)
              ·
                refine ⟨4304338383561990008782147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22956471378997280046838117 4304338383561990008782147)
                ·
                  refine ⟨6456507575342985013173221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304338383561990008782147 6456507575342985013173221)
                  ·
                    refine ⟨1210595170376809689969979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6456507575342985013173221 1210595170376809689969979)
                    ·
                      rfl

theorem cell23_7072877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_7072877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072877 prefixEnd_7072877 := by exact prefixLift 7072877
  have htrace : WordTrace (prefixWord ++ tailWord_7072877) baseStart_7072877 baseEnd_7072877 := by
    simpa [prefixWord, tailWord_7072877, baseEnd_7072877] using wordTrace_append hprefix tailTrace_7072877
  have hstable : (prefixWord ++ tailWord_7072877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072877).length < 2 ^ (prefixWord ++ tailWord_7072877).sum := by decide
  have hdescent : baseEnd_7072877 < baseStart_7072877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072896 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_7072896 : Nat := 118140960795 + 7072896 * 2 ^ 59
def prefixEnd_7072896 : Nat := 4983230072969 + 3 ^ 40 * 7072896 * 2
def baseEnd_7072896 : Nat := 3631795267262864495572349

theorem tailTrace_7072896 : CollatzResearch.WordTrace tailWord_7072896 prefixEnd_7072896 3631795267262864495572349 := by
  unfold tailWord_7072896
  simp only [CollatzResearch.WordTrace]
  refine ⟨128984855092056610655871271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171979806789408814207828361 128984855092056610655871271)
  ·
    refine ⟨193477282638084915983806907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128984855092056610655871271 193477282638084915983806907)
    ·
      refine ⟨290215923957127373975710361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193477282638084915983806907 290215923957127373975710361)
      ·
        refine ⟨217661942967845530481782771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290215923957127373975710361 217661942967845530481782771)
        ·
          refine ⟨326492914451768295722674157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217661942967845530481782771 326492914451768295722674157)
          ·
            refine ⟨122434842919413110896002809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326492914451768295722674157 122434842919413110896002809)
            ·
              refine ⟨91826132189559833172002107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122434842919413110896002809 91826132189559833172002107)
              ·
                refine ⟨137739198284339749758003161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91826132189559833172002107 137739198284339749758003161)
                ·
                  refine ⟨103304398713254812318502371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137739198284339749758003161 103304398713254812318502371)
                  ·
                    refine ⟨154956598069882218477753557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103304398713254812318502371 154956598069882218477753557)
                    ·
                      refine ⟨3631795267262864495572349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154956598069882218477753557 3631795267262864495572349)
                      ·
                        rfl

theorem cell23_7072896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_7072896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072896 prefixEnd_7072896 := by exact prefixLift 7072896
  have htrace : WordTrace (prefixWord ++ tailWord_7072896) baseStart_7072896 baseEnd_7072896 := by
    simpa [prefixWord, tailWord_7072896, baseEnd_7072896] using wordTrace_append hprefix tailTrace_7072896
  have hstable : (prefixWord ++ tailWord_7072896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072896).length < 2 ^ (prefixWord ++ tailWord_7072896).sum := by decide
  have hdescent : baseEnd_7072896 < baseStart_7072896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072917 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_7072917 : Nat := 118140960795 + 7072917 * 2 ^ 59
def prefixEnd_7072917 : Nat := 4983230072969 + 3 ^ 40 * 7072917 * 2
def baseEnd_7072917 : Nat := 3631806050356608913409753

theorem tailTrace_7072917 : CollatzResearch.WordTrace tailWord_7072917 prefixEnd_7072917 3631806050356608913409753 := by
  unfold tailWord_7072917
  simp only [CollatzResearch.WordTrace]
  refine ⟨257970476117037141898257005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171980317411358094598838003 257970476117037141898257005)
  ·
    refine ⟨96738928543888928211846377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257970476117037141898257005 96738928543888928211846377)
    ·
      refine ⟨72554196407916696158884783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96738928543888928211846377 72554196407916696158884783)
      ·
        refine ⟨108831294611875044238327175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72554196407916696158884783 108831294611875044238327175)
        ·
          refine ⟨163246941917812566357490763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108831294611875044238327175 163246941917812566357490763)
          ·
            refine ⟨244870412876718849536236145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163246941917812566357490763 244870412876718849536236145)
            ·
              refine ⟨183652809657539137152177109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244870412876718849536236145 183652809657539137152177109)
              ·
                refine ⟨4304362726348573527004151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 183652809657539137152177109 4304362726348573527004151)
                ·
                  refine ⟨6456544089522860290506227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304362726348573527004151 6456544089522860290506227)
                  ·
                    refine ⟨9684816134284290435759341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6456544089522860290506227 9684816134284290435759341)
                    ·
                      refine ⟨3631806050356608913409753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684816134284290435759341 3631806050356608913409753)
                      ·
                        rfl

theorem cell23_7072917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_7072917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072917 prefixEnd_7072917 := by exact prefixLift 7072917
  have htrace : WordTrace (prefixWord ++ tailWord_7072917) baseStart_7072917 baseEnd_7072917 := by
    simpa [prefixWord, tailWord_7072917, baseEnd_7072917] using wordTrace_append hprefix tailTrace_7072917
  have hstable : (prefixWord ++ tailWord_7072917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072917).length < 2 ^ (prefixWord ++ tailWord_7072917).sum := by decide
  have hdescent : baseEnd_7072917 < baseStart_7072917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072920 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_7072920 : Nat := 118140960795 + 7072920 * 2 ^ 59
def prefixEnd_7072920 : Nat := 4983230072969 + 3 ^ 40 * 7072920 * 2
def baseEnd_7072920 : Nat := 1210602530266190800557413

theorem tailTrace_7072920 : CollatzResearch.WordTrace tailWord_7072920 prefixEnd_7072920 1210602530266190800557413 := by
  unfold tailWord_7072920
  simp only [CollatzResearch.WordTrace]
  refine ⟨128985292768013136705308107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171980390357350848940410809 128985292768013136705308107)
  ·
    refine ⟨193477939152019705057962161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128985292768013136705308107 193477939152019705057962161)
    ·
      refine ⟨145108454364014778793471621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193477939152019705057962161 145108454364014778793471621)
      ·
        refine ⟨27207835193252771023775929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145108454364014778793471621 27207835193252771023775929)
        ·
          refine ⟨20405876394939578267831947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27207835193252771023775929 20405876394939578267831947)
          ·
            refine ⟨30608814592409367401747921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405876394939578267831947 30608814592409367401747921)
            ·
              refine ⟨22956610944307025551310941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30608814592409367401747921 22956610944307025551310941)
              ·
                refine ⟨8608729104115134581741603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22956610944307025551310941 8608729104115134581741603)
                ·
                  refine ⟨12913093656172701872612405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608729104115134581741603 12913093656172701872612405)
                  ·
                    refine ⟨1210602530266190800557413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12913093656172701872612405 1210602530266190800557413)
                    ·
                      rfl

theorem cell23_7072920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_7072920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072920 prefixEnd_7072920 := by exact prefixLift 7072920
  have htrace : WordTrace (prefixWord ++ tailWord_7072920) baseStart_7072920 baseEnd_7072920 := by
    simpa [prefixWord, tailWord_7072920, baseEnd_7072920] using wordTrace_append hprefix tailTrace_7072920
  have hstable : (prefixWord ++ tailWord_7072920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072920).length < 2 ^ (prefixWord ++ tailWord_7072920).sum := by decide
  have hdescent : baseEnd_7072920 < baseStart_7072920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072943 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_7072943 : Nat := 118140960795 + 7072943 * 2 ^ 59
def prefixEnd_7072943 : Nat := 4983230072969 + 3 ^ 40 * 7072943 * 2
def baseEnd_7072943 : Nat := 3631819400853625811684633

theorem tailTrace_7072943 : CollatzResearch.WordTrace tailWord_7072943 prefixEnd_7072943 3631819400853625811684633 := by
  unfold tailWord_7072943
  simp only [CollatzResearch.WordTrace]
  refine ⟨257971424414942948338703483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171980949609961965559135655 257971424414942948338703483)
  ·
    refine ⟨386957136622414422508055225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257971424414942948338703483 386957136622414422508055225)
    ·
      refine ⟨290217852466810816881041419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386957136622414422508055225 290217852466810816881041419)
      ·
        refine ⟨435326778700216225321562129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290217852466810816881041419 435326778700216225321562129)
        ·
          refine ⟨326495084025162168991171597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435326778700216225321562129 326495084025162168991171597)
          ·
            refine ⟨122435656509435813371689349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326495084025162168991171597 122435656509435813371689349)
            ·
              refine ⟨22956685595519215007191753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122435656509435813371689349 22956685595519215007191753)
              ·
                refine ⟨17217514196639411255393815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22956685595519215007191753 17217514196639411255393815)
                ·
                  refine ⟨25826271294959116883090723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17217514196639411255393815 25826271294959116883090723)
                  ·
                    refine ⟨38739406942438675324636085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25826271294959116883090723 38739406942438675324636085)
                    ·
                      refine ⟨3631819400853625811684633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38739406942438675324636085 3631819400853625811684633)
                      ·
                        rfl

theorem cell23_7072943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_7072943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072943 prefixEnd_7072943 := by exact prefixLift 7072943
  have htrace : WordTrace (prefixWord ++ tailWord_7072943) baseStart_7072943 baseEnd_7072943 := by
    simpa [prefixWord, tailWord_7072943, baseEnd_7072943] using wordTrace_append hprefix tailTrace_7072943
  have hstable : (prefixWord ++ tailWord_7072943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072943).length < 2 ^ (prefixWord ++ tailWord_7072943).sum := by decide
  have hdescent : baseEnd_7072943 < baseStart_7072943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072953 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7072953 : Nat := 118140960795 + 7072953 * 2 ^ 59
def prefixEnd_7072953 : Nat := 4983230072969 + 3 ^ 40 * 7072953 * 2
def baseEnd_7072953 : Nat := 3631824535660170772559587

theorem tailTrace_7072953 : CollatzResearch.WordTrace tailWord_7072953 prefixEnd_7072953 3631824535660170772559587 := by
  unfold tailWord_7072953
  simp only [CollatzResearch.WordTrace]
  refine ⟨257971789144906720046567513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171981192763271146697711675 257971789144906720046567513)
  ·
    refine ⟨193478841858680040034925635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257971789144906720046567513 193478841858680040034925635)
    ·
      refine ⟨290218262788020060052388453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193478841858680040034925635 290218262788020060052388453)
      ·
        refine ⟨54415924272753761259822835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290218262788020060052388453 54415924272753761259822835)
        ·
          refine ⟨81623886409130641889734253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54415924272753761259822835 81623886409130641889734253)
          ·
            refine ⟨30608957403423990708650345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81623886409130641889734253 30608957403423990708650345)
            ·
              refine ⟨22956718052567993031487759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30608957403423990708650345 22956718052567993031487759)
              ·
                refine ⟨34435077078851989547231639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22956718052567993031487759 34435077078851989547231639)
                ·
                  refine ⟨51652615618277984320847459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34435077078851989547231639 51652615618277984320847459)
                  ·
                    refine ⟨77478923427416976481271189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51652615618277984320847459 77478923427416976481271189)
                    ·
                      refine ⟨3631824535660170772559587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77478923427416976481271189 3631824535660170772559587)
                      ·
                        rfl

theorem cell23_7072953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7072953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072953 prefixEnd_7072953 := by exact prefixLift 7072953
  have htrace : WordTrace (prefixWord ++ tailWord_7072953) baseStart_7072953 baseEnd_7072953 := by
    simpa [prefixWord, tailWord_7072953, baseEnd_7072953] using wordTrace_append hprefix tailTrace_7072953
  have hstable : (prefixWord ++ tailWord_7072953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072953).length < 2 ^ (prefixWord ++ tailWord_7072953).sum := by decide
  have hdescent : baseEnd_7072953 < baseStart_7072953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072957 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_7072957 : Nat := 118140960795 + 7072957 * 2 ^ 59
def prefixEnd_7072957 : Nat := 4983230072969 + 3 ^ 40 * 7072957 * 2
def baseEnd_7072957 : Nat := 3631826589582788756909569

theorem tailTrace_7072957 : CollatzResearch.WordTrace tailWord_7072957 prefixEnd_7072957 3631826589582788756909569 := by
  unfold tailWord_7072957
  simp only [CollatzResearch.WordTrace]
  refine ⟨257971935036892228729713125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171981290024594819153142083 257971935036892228729713125)
  ·
    refine ⟨48369737819417292886821211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 257971935036892228729713125 48369737819417292886821211)
    ·
      refine ⟨72554606729125939330231817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48369737819417292886821211 72554606729125939330231817)
      ·
        refine ⟨54415955046844454497673863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72554606729125939330231817 54415955046844454497673863)
        ·
          refine ⟨81623932570266681746510795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54415955046844454497673863 81623932570266681746510795)
          ·
            refine ⟨122435898855400022619766193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81623932570266681746510795 122435898855400022619766193)
            ·
              refine ⟨91826924141550016964824645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122435898855400022619766193 91826924141550016964824645)
              ·
                refine ⟨17217548276540628180904621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91826924141550016964824645 17217548276540628180904621)
                ·
                  refine ⟨6456580603702735567839233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17217548276540628180904621 6456580603702735567839233)
                  ·
                    refine ⟨4842435452777051675879425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456580603702735567839233 4842435452777051675879425)
                    ·
                      refine ⟨3631826589582788756909569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842435452777051675879425 3631826589582788756909569)
                      ·
                        rfl

theorem cell23_7072957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_7072957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072957 prefixEnd_7072957 := by exact prefixLift 7072957
  have htrace : WordTrace (prefixWord ++ tailWord_7072957) baseStart_7072957 baseEnd_7072957 := by
    simpa [prefixWord, tailWord_7072957, baseEnd_7072957] using wordTrace_append hprefix tailTrace_7072957
  have hstable : (prefixWord ++ tailWord_7072957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072957).length < 2 ^ (prefixWord ++ tailWord_7072957).sum := by decide
  have hdescent : baseEnd_7072957 < baseStart_7072957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072970 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_7072970 : Nat := 118140960795 + 7072970 * 2 ^ 59
def prefixEnd_7072970 : Nat := 4983230072969 + 3 ^ 40 * 7072970 * 2
def baseEnd_7072970 : Nat := 3631833264831297206047009

theorem tailTrace_7072970 : CollatzResearch.WordTrace tailWord_7072970 prefixEnd_7072970 3631833264831297206047009 := by
  unfold tailWord_7072970
  simp only [CollatzResearch.WordTrace]
  refine ⟨64493102296461282987484091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171981606123896754633290909 64493102296461282987484091)
  ·
    refine ⟨96739653444691924481226137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64493102296461282987484091 96739653444691924481226137)
    ·
      refine ⟨72554740083518943360919603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96739653444691924481226137 72554740083518943360919603)
      ·
        refine ⟨108832110125278415041379405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72554740083518943360919603 108832110125278415041379405)
        ·
          refine ⟨40812041296979405640517277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108832110125278415041379405 40812041296979405640517277)
          ·
            refine ⟨15304515486367277115193979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40812041296979405640517277 15304515486367277115193979)
            ·
              refine ⟨22956773229550915672790969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15304515486367277115193979 22956773229550915672790969)
              ·
                refine ⟨17217579922163186754593227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22956773229550915672790969 17217579922163186754593227)
                ·
                  refine ⟨25826369883244780131889841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17217579922163186754593227 25826369883244780131889841)
                  ·
                    refine ⟨19369777412433585098917381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25826369883244780131889841 19369777412433585098917381)
                    ·
                      refine ⟨3631833264831297206047009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19369777412433585098917381 3631833264831297206047009)
                      ·
                        rfl

theorem cell23_7072970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_7072970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072970 prefixEnd_7072970 := by exact prefixLift 7072970
  have htrace : WordTrace (prefixWord ++ tailWord_7072970) baseStart_7072970 baseEnd_7072970 := by
    simpa [prefixWord, tailWord_7072970, baseEnd_7072970] using wordTrace_append hprefix tailTrace_7072970
  have hstable : (prefixWord ++ tailWord_7072970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072970).length < 2 ^ (prefixWord ++ tailWord_7072970).sum := by decide
  have hdescent : baseEnd_7072970 < baseStart_7072970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072974 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_7072974 : Nat := 118140960795 + 7072974 * 2 ^ 59
def prefixEnd_7072974 : Nat := 4983230072969 + 3 ^ 40 * 7072974 * 2
def baseEnd_7072974 : Nat := 3631835318753915190396991

theorem tailTrace_7072974 : CollatzResearch.WordTrace tailWord_7072974 prefixEnd_7072974 3631835318753915190396991 := by
  unfold tailWord_7072974
  simp only [CollatzResearch.WordTrace]
  refine ⟨32246569384728830079135247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171981703385220427088721317 32246569384728830079135247)
  ·
    refine ⟨48369854077093245118702871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32246569384728830079135247 48369854077093245118702871)
    ·
      refine ⟨72554781115639867678054307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48369854077093245118702871 72554781115639867678054307)
      ·
        refine ⟨108832171673459801517081461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72554781115639867678054307 108832171673459801517081461)
        ·
          refine ⟨10203016094386856392226387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108832171673459801517081461 10203016094386856392226387)
          ·
            refine ⟨15304524141580284588339581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10203016094386856392226387 15304524141580284588339581)
            ·
              refine ⟨5739196553092606720627343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15304524141580284588339581 5739196553092606720627343)
              ·
                refine ⟨8608794829638910080941015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739196553092606720627343 8608794829638910080941015)
                ·
                  refine ⟨12913192244458365121411523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608794829638910080941015 12913192244458365121411523)
                  ·
                    refine ⟨19369788366687547682117285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12913192244458365121411523 19369788366687547682117285)
                    ·
                      refine ⟨3631835318753915190396991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19369788366687547682117285 3631835318753915190396991)
                      ·
                        rfl

theorem cell23_7072974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_7072974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072974 prefixEnd_7072974 := by exact prefixLift 7072974
  have htrace : WordTrace (prefixWord ++ tailWord_7072974) baseStart_7072974 baseEnd_7072974 := by
    simpa [prefixWord, tailWord_7072974, baseEnd_7072974] using wordTrace_append hprefix tailTrace_7072974
  have hstable : (prefixWord ++ tailWord_7072974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072974).length < 2 ^ (prefixWord ++ tailWord_7072974).sum := by decide
  have hdescent : baseEnd_7072974 < baseStart_7072974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072980 : List Nat := [2, 4, 1, 4, 1, 11]
def baseStart_7072980 : Nat := 118140960795 + 7072980 * 2 ^ 59
def prefixEnd_7072980 : Nat := 4983230072969 + 3 ^ 40 * 7072980 * 2
def baseEnd_7072980 : Nat := 14945837035546675584041

theorem tailTrace_7072980 : CollatzResearch.WordTrace tailWord_7072980 prefixEnd_7072980 14945837035546675584041 := by
  unfold tailWord_7072980
  simp only [CollatzResearch.WordTrace]
  refine ⟨128986386957904451828900197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171981849277205935771866929 128986386957904451828900197)
  ·
    refine ⟨24184947554607084717918787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128986386957904451828900197 24184947554607084717918787)
    ·
      refine ⟨36277421331910627076878181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24184947554607084717918787 36277421331910627076878181)
      ·
        refine ⟨6802016499733242576914659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36277421331910627076878181 6802016499733242576914659)
        ·
          refine ⟨10203024749599863865371989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802016499733242576914659 10203024749599863865371989)
          ·
            refine ⟨14945837035546675584041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10203024749599863865371989 14945837035546675584041)
            ·
              rfl

theorem cell23_7072980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 11].length) (baseStart_7072980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072980 prefixEnd_7072980 := by exact prefixLift 7072980
  have htrace : WordTrace (prefixWord ++ tailWord_7072980) baseStart_7072980 baseEnd_7072980 := by
    simpa [prefixWord, tailWord_7072980, baseEnd_7072980] using wordTrace_append hprefix tailTrace_7072980
  have hstable : (prefixWord ++ tailWord_7072980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072980).length < 2 ^ (prefixWord ++ tailWord_7072980).sum := by decide
  have hdescent : baseEnd_7072980 < baseStart_7072980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072991 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 1, 2, 2]
def baseStart_7072991 : Nat := 118140960795 + 7072991 * 2 ^ 59
def prefixEnd_7072991 : Nat := 4983230072969 + 3 ^ 40 * 7072991 * 2
def baseEnd_7072991 : Nat := 3631844047925041623884413

theorem tailTrace_7072991 : CollatzResearch.WordTrace tailWord_7072991 prefixEnd_7072991 3631844047925041623884413 := by
  unfold tailWord_7072991
  simp only [CollatzResearch.WordTrace]
  refine ⟨257973175118769052536450827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171982116745846035024300551 257973175118769052536450827)
  ·
    refine ⟨386959762678153578804676241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257973175118769052536450827 386959762678153578804676241)
    ·
      refine ⟨290219822008615184103507181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386959762678153578804676241 290219822008615184103507181)
      ·
        refine ⟨108832433253230694038815193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290219822008615184103507181 108832433253230694038815193)
        ·
          refine ⟨81624324939923020529111395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108832433253230694038815193 81624324939923020529111395)
          ·
            refine ⟨122436487409884530793667093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81624324939923020529111395 122436487409884530793667093)
            ·
              refine ⟨5739210347338337380953145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122436487409884530793667093 5739210347338337380953145)
              ·
                refine ⟨4304407760503753035714859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5739210347338337380953145 4304407760503753035714859)
                ·
                  refine ⟨6456611640755629553572289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304407760503753035714859 6456611640755629553572289)
                  ·
                    refine ⟨4842458730566722165179217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6456611640755629553572289 4842458730566722165179217)
                    ·
                      refine ⟨3631844047925041623884413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842458730566722165179217 3631844047925041623884413)
                      ·
                        rfl

theorem cell23_7072991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_7072991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072991 prefixEnd_7072991 := by exact prefixLift 7072991
  have htrace : WordTrace (prefixWord ++ tailWord_7072991) baseStart_7072991 baseEnd_7072991 := by
    simpa [prefixWord, tailWord_7072991, baseEnd_7072991] using wordTrace_append hprefix tailTrace_7072991
  have hstable : (prefixWord ++ tailWord_7072991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072991).length < 2 ^ (prefixWord ++ tailWord_7072991).sum := by decide
  have hdescent : baseEnd_7072991 < baseStart_7072991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072993 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_7072993 : Nat := 118140960795 + 7072993 * 2 ^ 59
def prefixEnd_7072993 : Nat := 4983230072969 + 3 ^ 40 * 7072993 * 2
def baseEnd_7072993 : Nat := 1210615024962116872019801

theorem tailTrace_7072993 : CollatzResearch.WordTrace tailWord_7072993 prefixEnd_7072993 1210615024962116872019801 := by
  unfold tailWord_7072993
  simp only [CollatzResearch.WordTrace]
  refine ⟨257973248064761806878023633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171982165376507871252015755 257973248064761806878023633)
  ·
    refine ⟨193479936048571355158517725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257973248064761806878023633 193479936048571355158517725)
    ·
      refine ⟨72554976018214258184444147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193479936048571355158517725 72554976018214258184444147)
      ·
        refine ⟨108832464027321387276666221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72554976018214258184444147 108832464027321387276666221)
        ·
          refine ⟨40812174010245520228749833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108832464027321387276666221 40812174010245520228749833)
          ·
            refine ⟨30609130507684140171562375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40812174010245520228749833 30609130507684140171562375)
            ·
              refine ⟨45913695761526210257343563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30609130507684140171562375 45913695761526210257343563)
              ·
                refine ⟨68870543642289315386015345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45913695761526210257343563 68870543642289315386015345)
                ·
                  refine ⟨51652907731716986539511509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68870543642289315386015345 51652907731716986539511509)
                  ·
                    refine ⟨1210615024962116872019801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51652907731716986539511509 1210615024962116872019801)
                    ·
                      rfl

theorem cell23_7072993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_7072993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072993 prefixEnd_7072993 := by exact prefixLift 7072993
  have htrace : WordTrace (prefixWord ++ tailWord_7072993) baseStart_7072993 baseEnd_7072993 := by
    simpa [prefixWord, tailWord_7072993, baseEnd_7072993] using wordTrace_append hprefix tailTrace_7072993
  have hstable : (prefixWord ++ tailWord_7072993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072993).length < 2 ^ (prefixWord ++ tailWord_7072993).sum := by decide
  have hdescent : baseEnd_7072993 < baseStart_7072993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7072997 : List Nat := [1, 3, 1, 4, 4, 1, 1, 8]
def baseStart_7072997 : Nat := 118140960795 + 7072997 * 2 ^ 59
def prefixEnd_7072997 : Nat := 4983230072969 + 3 ^ 40 * 7072997 * 2
def baseEnd_7072997 : Nat := 134512856622554392607755

theorem tailTrace_7072997 : CollatzResearch.WordTrace tailWord_7072997 prefixEnd_7072997 134512856622554392607755 := by
  unfold tailWord_7072997
  simp only [CollatzResearch.WordTrace]
  refine ⟨257973393956747315561169245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171982262637831543707446163 257973393956747315561169245)
  ·
    refine ⟨96740022733780243335438467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257973393956747315561169245 96740022733780243335438467)
    ·
      refine ⟨145110034100670365003157701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96740022733780243335438467 145110034100670365003157701)
      ·
        refine ⟨27208131393875693438092069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145110034100670365003157701 27208131393875693438092069)
        ·
          refine ⟨5101524636351692519642263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27208131393875693438092069 5101524636351692519642263)
          ·
            refine ⟨7652286954527538779463395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101524636351692519642263 7652286954527538779463395)
            ·
              refine ⟨11478430431791308169195093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7652286954527538779463395 11478430431791308169195093)
              ·
                refine ⟨134512856622554392607755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11478430431791308169195093 134512856622554392607755)
                ·
                  rfl

theorem cell23_7072997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 8].length) (baseStart_7072997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7072997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7072997 prefixEnd_7072997 := by exact prefixLift 7072997
  have htrace : WordTrace (prefixWord ++ tailWord_7072997) baseStart_7072997 baseEnd_7072997 := by
    simpa [prefixWord, tailWord_7072997, baseEnd_7072997] using wordTrace_append hprefix tailTrace_7072997
  have hstable : (prefixWord ++ tailWord_7072997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7072997).length < 2 ^ (prefixWord ++ tailWord_7072997).sum := by decide
  have hdescent : baseEnd_7072997 < baseStart_7072997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7072997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073007 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_7073007 : Nat := 118140960795 + 7073007 * 2 ^ 59
def prefixEnd_7073007 : Nat := 4983230072969 + 3 ^ 40 * 7073007 * 2
def baseEnd_7073007 : Nat := 3631852263615513561284339

theorem tailTrace_7073007 : CollatzResearch.WordTrace tailWord_7073007 prefixEnd_7073007 3631852263615513561284339 := by
  unfold tailWord_7073007
  simp only [CollatzResearch.WordTrace]
  refine ⟨257973758686711087269033275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171982505791140724846022183 257973758686711087269033275)
  ·
    refine ⟨386960638030066630903549913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257973758686711087269033275 386960638030066630903549913)
    ·
      refine ⟨290220478522549973177662435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386960638030066630903549913 290220478522549973177662435)
      ·
        refine ⟨435330717783824959766493653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290220478522549973177662435 435330717783824959766493653)
        ·
          refine ⟨10203063698058397494527195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 435330717783824959766493653 10203063698058397494527195)
          ·
            refine ⟨15304595547087596241790793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10203063698058397494527195 15304595547087596241790793)
            ·
              refine ⟨11478446660315697181343095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15304595547087596241790793 11478446660315697181343095)
              ·
                refine ⟨17217669990473545772014643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11478446660315697181343095 17217669990473545772014643)
                ·
                  refine ⟨25826504985710318658021965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17217669990473545772014643 25826504985710318658021965)
                  ·
                    refine ⟨9684939369641369496758237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25826504985710318658021965 9684939369641369496758237)
                    ·
                      refine ⟨3631852263615513561284339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9684939369641369496758237 3631852263615513561284339)
                      ·
                        rfl

theorem cell23_7073007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_7073007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073007 prefixEnd_7073007 := by exact prefixLift 7073007
  have htrace : WordTrace (prefixWord ++ tailWord_7073007) baseStart_7073007 baseEnd_7073007 := by
    simpa [prefixWord, tailWord_7073007, baseEnd_7073007] using wordTrace_append hprefix tailTrace_7073007
  have hstable : (prefixWord ++ tailWord_7073007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073007).length < 2 ^ (prefixWord ++ tailWord_7073007).sum := by decide
  have hdescent : baseEnd_7073007 < baseStart_7073007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073017 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 1, 3, 2]
def baseStart_7073017 : Nat := 118140960795 + 7073017 * 2 ^ 59
def prefixEnd_7073017 : Nat := 4983230072969 + 3 ^ 40 * 7073017 * 2
def baseEnd_7073017 : Nat := 3631857398422058522159293

theorem tailTrace_7073017 : CollatzResearch.WordTrace tailWord_7073017 prefixEnd_7073017 3631857398422058522159293 := by
  unfold tailWord_7073017
  simp only [CollatzResearch.WordTrace]
  refine ⟨257974123416674858976897305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171982748944449905984598203 257974123416674858976897305)
  ·
    refine ⟨193480592562506144232672979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257974123416674858976897305 193480592562506144232672979)
    ·
      refine ⟨290220888843759216349009469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193480592562506144232672979 290220888843759216349009469)
      ·
        refine ⟨108832833316409706130878551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290220888843759216349009469 108832833316409706130878551)
        ·
          refine ⟨163249249974614559196317827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108832833316409706130878551 163249249974614559196317827)
          ·
            refine ⟨244873874961921838794476741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163249249974614559196317827 244873874961921838794476741)
            ·
              refine ⟨45913851555360344773964389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244873874961921838794476741 45913851555360344773964389)
              ·
                refine ⟨8608847166630064645118323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45913851555360344773964389 8608847166630064645118323)
                ·
                  refine ⟨12913270749945096967677485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608847166630064645118323 12913270749945096967677485)
                  ·
                    refine ⟨4842476531229411362879057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12913270749945096967677485 4842476531229411362879057)
                    ·
                      refine ⟨3631857398422058522159293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842476531229411362879057 3631857398422058522159293)
                      ·
                        rfl

theorem cell23_7073017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_7073017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073017 prefixEnd_7073017 := by exact prefixLift 7073017
  have htrace : WordTrace (prefixWord ++ tailWord_7073017) baseStart_7073017 baseEnd_7073017 := by
    simpa [prefixWord, tailWord_7073017, baseEnd_7073017] using wordTrace_append hprefix tailTrace_7073017
  have hstable : (prefixWord ++ tailWord_7073017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073017).length < 2 ^ (prefixWord ++ tailWord_7073017).sum := by decide
  have hdescent : baseEnd_7073017 < baseStart_7073017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073033 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_7073033 : Nat := 118140960795 + 7073033 * 2 ^ 59
def prefixEnd_7073033 : Nat := 4983230072969 + 3 ^ 40 * 7073033 * 2
def baseEnd_7073033 : Nat := 3631865614112530459559219

theorem tailTrace_7073033 : CollatzResearch.WordTrace tailWord_7073033 prefixEnd_7073033 3631865614112530459559219 := by
  unfold tailWord_7073033
  simp only [CollatzResearch.WordTrace]
  refine ⟨257974706984616893709479753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171983137989744595806319835 257974706984616893709479753)
  ·
    refine ⟨193481030238462670282109815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257974706984616893709479753 193481030238462670282109815)
    ·
      refine ⟨290221545357694005423164723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193481030238462670282109815 290221545357694005423164723)
      ·
        refine ⟨435332318036541008134747085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290221545357694005423164723 435332318036541008134747085)
        ·
          refine ⟨163249619263702878050530157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435332318036541008134747085 163249619263702878050530157)
          ·
            refine ⟨61218607223888579268948809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163249619263702878050530157 61218607223888579268948809)
            ·
              refine ⟨45913955417916434451711607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61218607223888579268948809 45913955417916434451711607)
              ·
                refine ⟨68870933126874651677567411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45913955417916434451711607 68870933126874651677567411)
                ·
                  refine ⟨103306399690311977516351117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68870933126874651677567411 103306399690311977516351117)
                  ·
                    refine ⟨38739899883866991568631669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103306399690311977516351117 38739899883866991568631669)
                    ·
                      refine ⟨3631865614112530459559219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38739899883866991568631669 3631865614112530459559219)
                      ·
                        rfl

theorem cell23_7073033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_7073033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073033 prefixEnd_7073033 := by exact prefixLift 7073033
  have htrace : WordTrace (prefixWord ++ tailWord_7073033) baseStart_7073033 baseEnd_7073033 := by
    simpa [prefixWord, tailWord_7073033, baseEnd_7073033] using wordTrace_append hprefix tailTrace_7073033
  have hstable : (prefixWord ++ tailWord_7073033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073033).length < 2 ^ (prefixWord ++ tailWord_7073033).sum := by decide
  have hdescent : baseEnd_7073033 < baseStart_7073033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073060 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7073060 : Nat := 118140960795 + 7073060 * 2 ^ 59
def prefixEnd_7073060 : Nat := 4983230072969 + 3 ^ 40 * 7073060 * 2
def baseEnd_7073060 : Nat := 3631879478090201853921595

theorem tailTrace_7073060 : CollatzResearch.WordTrace tailWord_7073060 prefixEnd_7073060 3631879478090201853921595 := by
  unfold tailWord_7073060
  simp only [CollatzResearch.WordTrace]
  refine ⟨128987845877759538660356317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171983794503679384880475089 128987845877759538660356317)
  ·
    refine ⟨48370442204159826997633619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128987845877759538660356317 48370442204159826997633619)
    ·
      refine ⟨72555663306239740496450429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48370442204159826997633619 72555663306239740496450429)
      ·
        refine ⟨27208373739839902686168911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72555663306239740496450429 27208373739839902686168911)
        ·
          refine ⟨40812560609759854029253367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27208373739839902686168911 40812560609759854029253367)
          ·
            refine ⟨61218840914639781043880051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40812560609759854029253367 61218840914639781043880051)
            ·
              refine ⟨91828261371959671565820077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61218840914639781043880051 91828261371959671565820077)
              ·
                refine ⟨34435598014484876837182529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91828261371959671565820077 34435598014484876837182529)
                ·
                  refine ⟨25826698510863657627886897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34435598014484876837182529 25826698510863657627886897)
                  ·
                    refine ⟨19370023883147743220915173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25826698510863657627886897 19370023883147743220915173)
                    ·
                      refine ⟨3631879478090201853921595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19370023883147743220915173 3631879478090201853921595)
                      ·
                        rfl

theorem cell23_7073060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7073060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073060 prefixEnd_7073060 := by exact prefixLift 7073060
  have htrace : WordTrace (prefixWord ++ tailWord_7073060) baseStart_7073060 baseEnd_7073060 := by
    simpa [prefixWord, tailWord_7073060, baseEnd_7073060] using wordTrace_append hprefix tailTrace_7073060
  have hstable : (prefixWord ++ tailWord_7073060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073060).length < 2 ^ (prefixWord ++ tailWord_7073060).sum := by decide
  have hdescent : baseEnd_7073060 < baseStart_7073060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073064 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_7073064 : Nat := 118140960795 + 7073064 * 2 ^ 59
def prefixEnd_7073064 : Nat := 4983230072969 + 3 ^ 40 * 7073064 * 2
def baseEnd_7073064 : Nat := 3631881532012819838271577

theorem tailTrace_7073064 : CollatzResearch.WordTrace tailWord_7073064 prefixEnd_7073064 3631881532012819838271577 := by
  unfold tailWord_7073064
  simp only [CollatzResearch.WordTrace]
  refine ⟨128987918823752293001929123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171983891765003057335905497 128987918823752293001929123)
  ·
    refine ⟨193481878235628439502893685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128987918823752293001929123 193481878235628439502893685)
    ·
      refine ⟨18138926084590166203396283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193481878235628439502893685 18138926084590166203396283)
      ·
        refine ⟨27208389126885249305094425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18138926084590166203396283 27208389126885249305094425)
        ·
          refine ⟨20406291845163936978820819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27208389126885249305094425 20406291845163936978820819)
          ·
            refine ⟨30609437767745905468231229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20406291845163936978820819 30609437767745905468231229)
            ·
              refine ⟨11478539162904714550586711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30609437767745905468231229 11478539162904714550586711)
              ·
                refine ⟨17217808744357071825880067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11478539162904714550586711 17217808744357071825880067)
                ·
                  refine ⟨25826713116535607738820101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17217808744357071825880067 25826713116535607738820101)
                  ·
                    refine ⟨4842508709350426451028769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25826713116535607738820101 4842508709350426451028769)
                    ·
                      refine ⟨3631881532012819838271577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842508709350426451028769 3631881532012819838271577)
                      ·
                        rfl

theorem cell23_7073064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_7073064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073064 prefixEnd_7073064 := by exact prefixLift 7073064
  have htrace : WordTrace (prefixWord ++ tailWord_7073064) baseStart_7073064 baseEnd_7073064 := by
    simpa [prefixWord, tailWord_7073064, baseEnd_7073064] using wordTrace_append hprefix tailTrace_7073064
  have hstable : (prefixWord ++ tailWord_7073064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073064).length < 2 ^ (prefixWord ++ tailWord_7073064).sum := by decide
  have hdescent : baseEnd_7073064 < baseStart_7073064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073087 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 5]
def baseStart_7073087 : Nat := 118140960795 + 7073087 * 2 ^ 59
def prefixEnd_7073087 : Nat := 4983230072969 + 3 ^ 40 * 7073087 * 2
def baseEnd_7073087 : Nat := 403543704674208138698219

theorem tailTrace_7073087 : CollatzResearch.WordTrace tailWord_7073087 prefixEnd_7073087 403543704674208138698219 := by
  unfold tailWord_7073087
  simp only [CollatzResearch.WordTrace]
  refine ⟨257976676526421260931945515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171984451017614173954630343 257976676526421260931945515)
  ·
    refine ⟨386965014789631891397918273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257976676526421260931945515 386965014789631891397918273)
    ·
      refine ⟨290223761092223918548438705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386965014789631891397918273 290223761092223918548438705)
      ·
        refine ⟨217667820819167938911329029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290223761092223918548438705 217667820819167938911329029)
        ·
          refine ⟨40812716403593988545874193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217667820819167938911329029 40812716403593988545874193)
          ·
            refine ⟨30609537302695491409405645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40812716403593988545874193 30609537302695491409405645)
            ·
              refine ⟨11478576488510809278527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30609537302695491409405645 11478576488510809278527117)
              ·
                refine ⟨4304466183191553479447669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11478576488510809278527117 4304466183191553479447669)
                ·
                  refine ⟨403543704674208138698219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304466183191553479447669 403543704674208138698219)
                  ·
                    rfl

theorem cell23_7073087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 5].length) (baseStart_7073087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073087 prefixEnd_7073087 := by exact prefixLift 7073087
  have htrace : WordTrace (prefixWord ++ tailWord_7073087) baseStart_7073087 baseEnd_7073087 := by
    simpa [prefixWord, tailWord_7073087, baseEnd_7073087] using wordTrace_append hprefix tailTrace_7073087
  have hstable : (prefixWord ++ tailWord_7073087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073087).length < 2 ^ (prefixWord ++ tailWord_7073087).sum := by decide
  have hdescent : baseEnd_7073087 < baseStart_7073087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073093 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_7073093 : Nat := 118140960795 + 7073093 * 2 ^ 59
def prefixEnd_7073093 : Nat := 4983230072969 + 3 ^ 40 * 7073093 * 2
def baseEnd_7073093 : Nat := 3631896422951800224808943

theorem tailTrace_7073093 : CollatzResearch.WordTrace tailWord_7073093 prefixEnd_7073093 3631896422951800224808943 := by
  unfold tailWord_7073093
  simp only [CollatzResearch.WordTrace]
  refine ⟨257976895364399523956663933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171984596909599682637775955 257976895364399523956663933)
  ·
    refine ⟨96741335761649821483748975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257976895364399523956663933 96741335761649821483748975)
    ·
      refine ⟨145112003642474732225623463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96741335761649821483748975 145112003642474732225623463)
      ·
        refine ⟨217668005463712098338435195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145112003642474732225623463 217668005463712098338435195)
        ·
          refine ⟨326502008195568147507652793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217668005463712098338435195 326502008195568147507652793)
          ·
            refine ⟨244876506146676110630739595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326502008195568147507652793 244876506146676110630739595)
            ·
              refine ⟨367314759220014165946109393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244876506146676110630739595 367314759220014165946109393)
              ·
                refine ⟨275486069415010624459582045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367314759220014165946109393 275486069415010624459582045)
                ·
                  refine ⟨103307276030628984172343267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275486069415010624459582045 103307276030628984172343267)
                  ·
                    refine ⟨154960914045943476258514901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103307276030628984172343267 154960914045943476258514901)
                    ·
                      refine ⟨3631896422951800224808943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154960914045943476258514901 3631896422951800224808943)
                      ·
                        rfl

theorem cell23_7073093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_7073093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073093 prefixEnd_7073093 := by exact prefixLift 7073093
  have htrace : WordTrace (prefixWord ++ tailWord_7073093) baseStart_7073093 baseEnd_7073093 := by
    simpa [prefixWord, tailWord_7073093, baseEnd_7073093] using wordTrace_append hprefix tailTrace_7073093
  have hstable : (prefixWord ++ tailWord_7073093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073093).length < 2 ^ (prefixWord ++ tailWord_7073093).sum := by decide
  have hdescent : baseEnd_7073093 < baseStart_7073093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073100 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_7073100 : Nat := 118140960795 + 7073100 * 2 ^ 59
def prefixEnd_7073100 : Nat := 4983230072969 + 3 ^ 40 * 7073100 * 2
def baseEnd_7073100 : Nat := 1210633339105460565807137

theorem tailTrace_7073100 : CollatzResearch.WordTrace tailWord_7073100 prefixEnd_7073100 1210633339105460565807137 := by
  unfold tailWord_7073100
  simp only [CollatzResearch.WordTrace]
  refine ⟨128988575337687082076084377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171984767116916109434779169 128988575337687082076084377)
  ·
    refine ⟨96741431503265311557063283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128988575337687082076084377 96741431503265311557063283)
    ·
      refine ⟨145112147254897967335594925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96741431503265311557063283 145112147254897967335594925)
      ·
        refine ⟨54417055220586737750848097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145112147254897967335594925 54417055220586737750848097)
        ·
          refine ⟨40812791415440053313136073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54417055220586737750848097 40812791415440053313136073)
          ·
            refine ⟨30609593561580039984852055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40812791415440053313136073 30609593561580039984852055)
            ·
              refine ⟨45914390342370059977278083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30609593561580039984852055 45914390342370059977278083)
              ·
                refine ⟨68871585513555089965917125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45914390342370059977278083 68871585513555089965917125)
                ·
                  refine ⟨12913422283791579368609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68871585513555089965917125 12913422283791579368609461)
                  ·
                    refine ⟨1210633339105460565807137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12913422283791579368609461 1210633339105460565807137)
                    ·
                      rfl

theorem cell23_7073100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_7073100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073100 prefixEnd_7073100 := by exact prefixLift 7073100
  have htrace : WordTrace (prefixWord ++ tailWord_7073100) baseStart_7073100 baseEnd_7073100 := by
    simpa [prefixWord, tailWord_7073100, baseEnd_7073100] using wordTrace_append hprefix tailTrace_7073100
  have hstable : (prefixWord ++ tailWord_7073100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073100).length < 2 ^ (prefixWord ++ tailWord_7073100).sum := by decide
  have hdescent : baseEnd_7073100 < baseStart_7073100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073157 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_7073157 : Nat := 118140960795 + 7073157 * 2 ^ 59
def prefixEnd_7073157 : Nat := 4983230072969 + 3 ^ 40 * 7073157 * 2
def baseEnd_7073157 : Nat := 3631929285713687974408649

theorem tailTrace_7073157 : CollatzResearch.WordTrace tailWord_7073157 prefixEnd_7073157 3631929285713687974408649 := by
  unfold tailWord_7073157
  simp only [CollatzResearch.WordTrace]
  refine ⟨257979229636167662886993725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171986153090778441924662483 257979229636167662886993725)
  ·
    refine ⟨96742211113562873582622647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257979229636167662886993725 96742211113562873582622647)
    ·
      refine ⟨145113316670344310373933971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96742211113562873582622647 145113316670344310373933971)
      ·
        refine ⟨217669975005516465560900957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145113316670344310373933971 217669975005516465560900957)
        ·
          refine ⟨81626240627068674585337859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217669975005516465560900957 81626240627068674585337859)
          ·
            refine ⟨122439360940603011878006789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81626240627068674585337859 122439360940603011878006789)
            ·
              refine ⟨22957380176363064727126273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122439360940603011878006789 22957380176363064727126273)
              ·
                refine ⟨17218035132272298545344705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22957380176363064727126273 17218035132272298545344705)
                ·
                  refine ⟨12913526349204223909008529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17218035132272298545344705 12913526349204223909008529)
                  ·
                    refine ⟨9685144761903167931756397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12913526349204223909008529 9685144761903167931756397)
                    ·
                      refine ⟨3631929285713687974408649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9685144761903167931756397 3631929285713687974408649)
                      ·
                        rfl

theorem cell23_7073157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_7073157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073157 prefixEnd_7073157 := by exact prefixLift 7073157
  have htrace : WordTrace (prefixWord ++ tailWord_7073157) baseStart_7073157 baseEnd_7073157 := by
    simpa [prefixWord, tailWord_7073157, baseEnd_7073157] using wordTrace_append hprefix tailTrace_7073157
  have hstable : (prefixWord ++ tailWord_7073157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073157).length < 2 ^ (prefixWord ++ tailWord_7073157).sum := by decide
  have hdescent : baseEnd_7073157 < baseStart_7073157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073164 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_7073164 : Nat := 118140960795 + 7073164 * 2 ^ 59
def prefixEnd_7073164 : Nat := 4983230072969 + 3 ^ 40 * 7073164 * 2
def baseEnd_7073164 : Nat := 1210644293359423149007039

theorem tailTrace_7073164 : CollatzResearch.WordTrace tailWord_7073164 prefixEnd_7073164 1210644293359423149007039 := by
  unfold tailWord_7073164
  simp only [CollatzResearch.WordTrace]
  refine ⟨128989742473571151541249273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171986323298094868721665697 128989742473571151541249273)
  ·
    refine ⟨96742306855178363655936955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128989742473571151541249273 96742306855178363655936955)
    ·
      refine ⟨145113460282767545483905433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96742306855178363655936955 145113460282767545483905433)
      ·
        refine ⟨108835095212075659112929075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145113460282767545483905433 108835095212075659112929075)
        ·
          refine ⟨163252642818113488669393613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108835095212075659112929075 163252642818113488669393613)
          ·
            refine ⟨61219741056792558251022605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163252642818113488669393613 61219741056792558251022605)
            ·
              refine ⟨22957402896297209344133477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61219741056792558251022605 22957402896297209344133477)
              ·
                refine ⟨4304513043055726752025027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22957402896297209344133477 4304513043055726752025027)
                ·
                  refine ⟨6456769564583590128037541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304513043055726752025027 6456769564583590128037541)
                  ·
                    refine ⟨1210644293359423149007039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6456769564583590128037541 1210644293359423149007039)
                    ·
                      rfl

theorem cell23_7073164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_7073164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073164 prefixEnd_7073164 := by exact prefixLift 7073164
  have htrace : WordTrace (prefixWord ++ tailWord_7073164) baseStart_7073164 baseEnd_7073164 := by
    simpa [prefixWord, tailWord_7073164, baseEnd_7073164] using wordTrace_append hprefix tailTrace_7073164
  have hstable : (prefixWord ++ tailWord_7073164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073164).length < 2 ^ (prefixWord ++ tailWord_7073164).sum := by decide
  have hdescent : baseEnd_7073164 < baseStart_7073164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073207 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 1, 5]
def baseStart_7073207 : Nat := 118140960795 + 7073207 * 2 ^ 59
def prefixEnd_7073207 : Nat := 4983230072969 + 3 ^ 40 * 7073207 * 2
def baseEnd_7073207 : Nat := 1210651653248804259594473

theorem tailTrace_7073207 : CollatzResearch.WordTrace tailWord_7073207 prefixEnd_7073207 1210651653248804259594473 := by
  unfold tailWord_7073207
  simp only [CollatzResearch.WordTrace]
  refine ⟨257981053285986521426313875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171987368857324347617542583 257981053285986521426313875)
  ·
    refine ⟨386971579928979782139470813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257981053285986521426313875 386971579928979782139470813)
    ·
      refine ⟨145114342473367418302301555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 386971579928979782139470813 145114342473367418302301555)
      ·
        refine ⟨217671513710051127453452333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145114342473367418302301555 217671513710051127453452333)
        ·
          refine ⟨81626817641269172795044625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217671513710051127453452333 81626817641269172795044625)
          ·
            refine ⟨61220113230951879596283469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81626817641269172795044625 61220113230951879596283469)
            ·
              refine ⟨22957542461606954848606301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61220113230951879596283469 22957542461606954848606301)
              ·
                refine ⟨8609078423102608068227363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22957542461606954848606301 8609078423102608068227363)
                ·
                  refine ⟨12913617634653912102341045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609078423102608068227363 12913617634653912102341045)
                  ·
                    refine ⟨1210651653248804259594473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12913617634653912102341045 1210651653248804259594473)
                    ·
                      rfl

theorem cell23_7073207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_7073207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073207 prefixEnd_7073207 := by exact prefixLift 7073207
  have htrace : WordTrace (prefixWord ++ tailWord_7073207) baseStart_7073207 baseEnd_7073207 := by
    simpa [prefixWord, tailWord_7073207, baseEnd_7073207] using wordTrace_append hprefix tailTrace_7073207
  have hstable : (prefixWord ++ tailWord_7073207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073207).length < 2 ^ (prefixWord ++ tailWord_7073207).sum := by decide
  have hdescent : baseEnd_7073207 < baseStart_7073207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073214 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_7073214 : Nat := 118140960795 + 7073214 * 2 ^ 59
def prefixEnd_7073214 : Nat := 4983230072969 + 3 ^ 40 * 7073214 * 2
def baseEnd_7073214 : Nat := 3631958554110994251395887

theorem tailTrace_7073214 : CollatzResearch.WordTrace tailWord_7073214 prefixEnd_7073214 3631958554110994251395887 := by
  unfold tailWord_7073214
  simp only [CollatzResearch.WordTrace]
  refine ⟨32247663574620145202727337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171987539064640774414545797 32247663574620145202727337)
  ·
    refine ⟨24185747680965108902045503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32247663574620145202727337 24185747680965108902045503)
    ·
      refine ⟨36278621521447663353068255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24185747680965108902045503 36278621521447663353068255)
      ·
        refine ⟨54417932282171495029602383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36278621521447663353068255 54417932282171495029602383)
        ·
          refine ⟨81626898423257242544403575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54417932282171495029602383 81626898423257242544403575)
          ·
            refine ⟨122440347634885863816605363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81626898423257242544403575 122440347634885863816605363)
            ·
              refine ⟨183660521452328795724908045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122440347634885863816605363 183660521452328795724908045)
              ·
                refine ⟨68872695544623298396840517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183660521452328795724908045 68872695544623298396840517)
                ·
                  refine ⟨12913630414616868449407597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68872695544623298396840517 12913630414616868449407597)
                  ·
                    refine ⟨4842611405481325668527849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12913630414616868449407597 4842611405481325668527849)
                    ·
                      refine ⟨3631958554110994251395887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842611405481325668527849 3631958554110994251395887)
                      ·
                        rfl

theorem cell23_7073214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_7073214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073214 prefixEnd_7073214 := by exact prefixLift 7073214
  have htrace : WordTrace (prefixWord ++ tailWord_7073214) baseStart_7073214 baseEnd_7073214 := by
    simpa [prefixWord, tailWord_7073214, baseEnd_7073214] using wordTrace_append hprefix tailTrace_7073214
  have hstable : (prefixWord ++ tailWord_7073214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073214).length < 2 ^ (prefixWord ++ tailWord_7073214).sum := by decide
  have hdescent : baseEnd_7073214 < baseStart_7073214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073264 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_7073264 : Nat := 118140960795 + 7073264 * 2 ^ 59
def prefixEnd_7073264 : Nat := 4983230072969 + 3 ^ 40 * 7073264 * 2
def baseEnd_7073264 : Nat := 3631984228143719055770657

theorem tailTrace_7073264 : CollatzResearch.WordTrace tailWord_7073264 prefixEnd_7073264 3631984228143719055770657 := by
  unfold tailWord_7073264
  simp only [CollatzResearch.WordTrace]
  refine ⟨128991566123390010080569423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171988754831186680107425897 128991566123390010080569423)
  ·
    refine ⟨193487349185085015120854135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128991566123390010080569423 193487349185085015120854135)
    ·
      refine ⟨290231023777627522681281203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193487349185085015120854135 290231023777627522681281203)
      ·
        refine ⟨435346535666441284021921805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290231023777627522681281203 435346535666441284021921805)
        ·
          refine ⟨163254950874915481508220677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435346535666441284021921805 163254950874915481508220677)
          ·
            refine ⟨30610303289046652782791377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163254950874915481508220677 30610303289046652782791377)
            ·
              refine ⟨22957727466784989587093533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30610303289046652782791377 22957727466784989587093533)
              ·
                refine ⟨8609147800044371095160075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22957727466784989587093533 8609147800044371095160075)
                ·
                  refine ⟨12913721700066556642740113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609147800044371095160075 12913721700066556642740113)
                  ·
                    refine ⟨9685291275049917482055085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12913721700066556642740113 9685291275049917482055085)
                    ·
                      refine ⟨3631984228143719055770657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9685291275049917482055085 3631984228143719055770657)
                      ·
                        rfl

theorem cell23_7073264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_7073264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073264 prefixEnd_7073264 := by exact prefixLift 7073264
  have htrace : WordTrace (prefixWord ++ tailWord_7073264) baseStart_7073264 baseEnd_7073264 := by
    simpa [prefixWord, tailWord_7073264, baseEnd_7073264] using wordTrace_append hprefix tailTrace_7073264
  have hstable : (prefixWord ++ tailWord_7073264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073264).length < 2 ^ (prefixWord ++ tailWord_7073264).sum := by decide
  have hdescent : baseEnd_7073264 < baseStart_7073264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073284 : List Nat := [2, 3, 2, 3, 2, 1, 2, 8]
def baseStart_7073284 : Nat := 118140960795 + 7073284 * 2 ^ 59
def prefixEnd_7073284 : Nat := 4983230072969 + 3 ^ 40 * 7073284 * 2
def baseEnd_7073284 : Nat := 134518314731733665834095

theorem tailTrace_7073284 : CollatzResearch.WordTrace tailWord_7073284 prefixEnd_7073284 134518314731733665834095 := by
  unfold tailWord_7073284
  simp only [CollatzResearch.WordTrace]
  refine ⟨128991930853353781788433453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171989241137805042384577937 128991930853353781788433453)
  ·
    refine ⟨48371974070007668170662545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128991930853353781788433453 48371974070007668170662545)
    ·
      refine ⟨36278980552505751127996909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48371974070007668170662545 36278980552505751127996909)
      ·
        refine ⟨13604617707189656672998841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36278980552505751127996909 13604617707189656672998841)
        ·
          refine ⟨10203463280392242504749131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13604617707189656672998841 10203463280392242504749131)
          ·
            refine ⟨15305194920588363757123697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10203463280392242504749131 15305194920588363757123697)
            ·
              refine ⟨11478896190441272817842773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15305194920588363757123697 11478896190441272817842773)
              ·
                refine ⟨134518314731733665834095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11478896190441272817842773 134518314731733665834095)
                ·
                  rfl

theorem cell23_7073284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 8].length) (baseStart_7073284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073284 prefixEnd_7073284 := by exact prefixLift 7073284
  have htrace : WordTrace (prefixWord ++ tailWord_7073284) baseStart_7073284 baseEnd_7073284 := by
    simpa [prefixWord, tailWord_7073284, baseEnd_7073284] using wordTrace_append hprefix tailTrace_7073284
  have hstable : (prefixWord ++ tailWord_7073284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073284).length < 2 ^ (prefixWord ++ tailWord_7073284).sum := by decide
  have hdescent : baseEnd_7073284 < baseStart_7073284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073424 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2]
def baseStart_7073424 : Nat := 118140960795 + 7073424 * 2 ^ 59
def prefixEnd_7073424 : Nat := 4983230072969 + 3 ^ 40 * 7073424 * 2
def baseEnd_7073424 : Nat := 3632066385048438429769921

theorem tailTrace_7073424 : CollatzResearch.WordTrace tailWord_7073424 prefixEnd_7073424 3632066385048438429769921 := by
  unfold tailWord_7073424
  simp only [CollatzResearch.WordTrace]
  refine ⟨128994483963100183743481663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171992645284133578324642217 128994483963100183743481663)
  ·
    refine ⟨193491725944650275615222495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128994483963100183743481663 193491725944650275615222495)
    ·
      refine ⟨290237588916975413422833743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193491725944650275615222495 290237588916975413422833743)
      ·
        refine ⟨435356383375463120134250615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290237588916975413422833743 435356383375463120134250615)
        ·
          refine ⟨653034575063194680201375923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435356383375463120134250615 653034575063194680201375923)
          ·
            refine ⟨979551862594792020302063885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653034575063194680201375923 979551862594792020302063885)
            ·
              refine ⟨367331948473047007613273957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979551862594792020302063885 367331948473047007613273957)
              ·
                refine ⟨68874740338696313927488867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367331948473047007613273957 68874740338696313927488867)
                ·
                  refine ⟨103312110508044470891233301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68874740338696313927488867 103312110508044470891233301)
                  ·
                    refine ⟨4842755180064584573026561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103312110508044470891233301 4842755180064584573026561)
                    ·
                      refine ⟨3632066385048438429769921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842755180064584573026561 3632066385048438429769921)
                      ·
                        rfl

theorem cell23_7073424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 6, 2].length) (baseStart_7073424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073424 prefixEnd_7073424 := by exact prefixLift 7073424
  have htrace : WordTrace (prefixWord ++ tailWord_7073424) baseStart_7073424 baseEnd_7073424 := by
    simpa [prefixWord, tailWord_7073424, baseEnd_7073424] using wordTrace_append hprefix tailTrace_7073424
  have hstable : (prefixWord ++ tailWord_7073424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073424).length < 2 ^ (prefixWord ++ tailWord_7073424).sum := by decide
  have hdescent : baseEnd_7073424 < baseStart_7073424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073441 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7073441 : Nat := 118140960795 + 7073441 * 2 ^ 59
def prefixEnd_7073441 : Nat := 4983230072969 + 3 ^ 40 * 7073441 * 2
def baseEnd_7073441 : Nat := 3632075114219564863257343

theorem tailTrace_7073441 : CollatzResearch.WordTrace tailWord_7073441 prefixEnd_7073441 3632075114219564863257343 := by
  unfold tailWord_7073441
  simp only [CollatzResearch.WordTrace]
  refine ⟨257989587967138779390332177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171993058644759186260221451 257989587967138779390332177)
  ·
    refine ⟨193492190975354084542749133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257989587967138779390332177 193492190975354084542749133)
    ·
      refine ⟨72559571615757781703530925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193492190975354084542749133 72559571615757781703530925)
      ·
        refine ⟨27209839355909168138824097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72559571615757781703530925 27209839355909168138824097)
        ·
          refine ⟨20407379516931876104118073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27209839355909168138824097 20407379516931876104118073)
          ·
            refine ⟨15305534637698907078088555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20407379516931876104118073 15305534637698907078088555)
            ·
              refine ⟨22958301956548360617132833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15305534637698907078088555 22958301956548360617132833)
              ·
                refine ⟨17218726467411270462849625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22958301956548360617132833 17218726467411270462849625)
                ·
                  refine ⟨12914044850558452847137219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17218726467411270462849625 12914044850558452847137219)
                  ·
                    refine ⟨19371067275837679270705829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12914044850558452847137219 19371067275837679270705829)
                    ·
                      refine ⟨3632075114219564863257343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19371067275837679270705829 3632075114219564863257343)
                      ·
                        rfl

theorem cell23_7073441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7073441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073441 prefixEnd_7073441 := by exact prefixLift 7073441
  have htrace : WordTrace (prefixWord ++ tailWord_7073441) baseStart_7073441 baseEnd_7073441 := by
    simpa [prefixWord, tailWord_7073441, baseEnd_7073441] using wordTrace_append hprefix tailTrace_7073441
  have hstable : (prefixWord ++ tailWord_7073441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073441).length < 2 ^ (prefixWord ++ tailWord_7073441).sum := by decide
  have hdescent : baseEnd_7073441 < baseStart_7073441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073467 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_7073467 : Nat := 118140960795 + 7073467 * 2 ^ 59
def prefixEnd_7073467 : Nat := 4983230072969 + 3 ^ 40 * 7073467 * 2
def baseEnd_7073467 : Nat := 3632088464716581761532223

theorem tailTrace_7073467 : CollatzResearch.WordTrace tailWord_7073467 prefixEnd_7073467 3632088464716581761532223 := by
  unfold tailWord_7073467
  simp only [CollatzResearch.WordTrace]
  refine ⟨257990536265044585830778655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171993690843363057220519103 257990536265044585830778655)
  ·
    refine ⟨386985804397566878746167983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257990536265044585830778655 386985804397566878746167983)
    ·
      refine ⟨580478706596350318119251975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386985804397566878746167983 580478706596350318119251975)
      ·
        refine ⟨870718059894525477178877963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580478706596350318119251975 870718059894525477178877963)
        ·
          refine ⟨1306077089841788215768316945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870718059894525477178877963 1306077089841788215768316945)
          ·
            refine ⟨979557817381341161826237709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306077089841788215768316945 979557817381341161826237709)
            ·
              refine ⟨367334181518002935684839141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979557817381341161826237709 367334181518002935684839141)
              ·
                refine ⟨68875159034625550440907339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367334181518002935684839141 68875159034625550440907339)
                ·
                  refine ⟨103312738551938325661361009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68875159034625550440907339 103312738551938325661361009)
                  ·
                    refine ⟨77484553913953744246020757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103312738551938325661361009 77484553913953744246020757)
                    ·
                      refine ⟨3632088464716581761532223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77484553913953744246020757 3632088464716581761532223)
                      ·
                        rfl

theorem cell23_7073467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_7073467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073467 prefixEnd_7073467 := by exact prefixLift 7073467
  have htrace : WordTrace (prefixWord ++ tailWord_7073467) baseStart_7073467 baseEnd_7073467 := by
    simpa [prefixWord, tailWord_7073467, baseEnd_7073467] using wordTrace_append hprefix tailTrace_7073467
  have hstable : (prefixWord ++ tailWord_7073467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073467).length < 2 ^ (prefixWord ++ tailWord_7073467).sum := by decide
  have hdescent : baseEnd_7073467 < baseStart_7073467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073477 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_7073477 : Nat := 118140960795 + 7073477 * 2 ^ 59
def prefixEnd_7073477 : Nat := 4983230072969 + 3 ^ 40 * 7073477 * 2
def baseEnd_7073477 : Nat := 1210697866507708907469059

theorem tailTrace_7073477 : CollatzResearch.WordTrace tailWord_7073477 prefixEnd_7073477 1210697866507708907469059 := by
  unfold tailWord_7073477
  simp only [CollatzResearch.WordTrace]
  refine ⟨257990900995008357538642685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171993933996672238359095123 257990900995008357538642685)
  ·
    refine ⟨96746587873128134076991007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257990900995008357538642685 96746587873128134076991007)
    ·
      refine ⟨145119881809692201115486511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96746587873128134076991007 145119881809692201115486511)
      ·
        refine ⟨217679822714538301673229767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145119881809692201115486511 217679822714538301673229767)
        ·
          refine ⟨326519734071807452509844651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217679822714538301673229767 326519734071807452509844651)
          ·
            refine ⟨489779601107711178764766977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326519734071807452509844651 489779601107711178764766977)
            ·
              refine ⟨367334700830783384073575233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489779601107711178764766977 367334700830783384073575233)
              ·
                refine ⟨275501025623087538055181425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367334700830783384073575233 275501025623087538055181425)
                ·
                  refine ⟨206625769217315653541386069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275501025623087538055181425 206625769217315653541386069)
                  ·
                    refine ⟨1210697866507708907469059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 206625769217315653541386069 1210697866507708907469059)
                    ·
                      rfl

theorem cell23_7073477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_7073477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073477 prefixEnd_7073477 := by exact prefixLift 7073477
  have htrace : WordTrace (prefixWord ++ tailWord_7073477) baseStart_7073477 baseEnd_7073477 := by
    simpa [prefixWord, tailWord_7073477, baseEnd_7073477] using wordTrace_append hprefix tailTrace_7073477
  have hstable : (prefixWord ++ tailWord_7073477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073477).length < 2 ^ (prefixWord ++ tailWord_7073477).sum := by decide
  have hdescent : baseEnd_7073477 < baseStart_7073477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073487 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_7073487 : Nat := 118140960795 + 7073487 * 2 ^ 59
def prefixEnd_7073487 : Nat := 4983230072969 + 3 ^ 40 * 7073487 * 2
def baseEnd_7073487 : Nat := 3632098734329671683282131

theorem tailTrace_7073487 : CollatzResearch.WordTrace tailWord_7073487 prefixEnd_7073487 3632098734329671683282131 := by
  unfold tailWord_7073487
  simp only [CollatzResearch.WordTrace]
  refine ⟨257991265724972129246506715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171994177149981419497671143 257991265724972129246506715)
  ·
    refine ⟨386986898587458193869760073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257991265724972129246506715 386986898587458193869760073)
    ·
      refine ⟨290240173940593645402320055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386986898587458193869760073 290240173940593645402320055)
      ·
        refine ⟨435360260910890468103480083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290240173940593645402320055 435360260910890468103480083)
        ·
          refine ⟨653040391366335702155220125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435360260910890468103480083 653040391366335702155220125)
          ·
            refine ⟨244890146762375888308207547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 653040391366335702155220125 244890146762375888308207547)
            ·
              refine ⟨367335220143563832462311321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244890146762375888308207547 367335220143563832462311321)
              ·
                refine ⟨275501415107672874346733491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367335220143563832462311321 275501415107672874346733491)
                ·
                  refine ⟨413252122661509311520100237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275501415107672874346733491 413252122661509311520100237)
                  ·
                    refine ⟨154969545998065991820037589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 413252122661509311520100237 154969545998065991820037589)
                    ·
                      refine ⟨3632098734329671683282131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 154969545998065991820037589 3632098734329671683282131)
                      ·
                        rfl

theorem cell23_7073487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_7073487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073487 prefixEnd_7073487 := by exact prefixLift 7073487
  have htrace : WordTrace (prefixWord ++ tailWord_7073487) baseStart_7073487 baseEnd_7073487 := by
    simpa [prefixWord, tailWord_7073487, baseEnd_7073487] using wordTrace_append hprefix tailTrace_7073487
  have hstable : (prefixWord ++ tailWord_7073487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073487).length < 2 ^ (prefixWord ++ tailWord_7073487).sum := by decide
  have hdescent : baseEnd_7073487 < baseStart_7073487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073548 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_7073548 : Nat := 118140960795 + 7073548 * 2 ^ 59
def prefixEnd_7073548 : Nat := 4983230072969 + 3 ^ 40 * 7073548 * 2
def baseEnd_7073548 : Nat := 3632130056649595944619351

theorem tailTrace_7073548 : CollatzResearch.WordTrace tailWord_7073548 prefixEnd_7073548 3632130056649595944619351 := by
  unfold tailWord_7073548
  simp only [CollatzResearch.WordTrace]
  refine ⟨128996745288875568332238649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171995660385167424442984865 128996745288875568332238649)
  ·
    refine ⟨96747558966656676249178987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128996745288875568332238649 96747558966656676249178987)
    ·
      refine ⟨145121338449985014373768481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96747558966656676249178987 145121338449985014373768481)
      ·
        refine ⟨108841003837488760780326361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145121338449985014373768481 108841003837488760780326361)
        ·
          refine ⟨81630752878116570585244771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108841003837488760780326361 81630752878116570585244771)
          ·
            refine ⟨122446129317174855877867157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81630752878116570585244771 122446129317174855877867157)
            ·
              refine ⟨5739662311742571369275023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122446129317174855877867157 5739662311742571369275023)
              ·
                refine ⟨8609493467613857053912535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739662311742571369275023 8609493467613857053912535)
                ·
                  refine ⟨12914240201420785580868803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609493467613857053912535 12914240201420785580868803)
                  ·
                    refine ⟨19371360302131178371303205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12914240201420785580868803 19371360302131178371303205)
                    ·
                      refine ⟨3632130056649595944619351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19371360302131178371303205 3632130056649595944619351)
                      ·
                        rfl

theorem cell23_7073548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_7073548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073548 prefixEnd_7073548 := by exact prefixLift 7073548
  have htrace : WordTrace (prefixWord ++ tailWord_7073548) baseStart_7073548 baseEnd_7073548 := by
    simpa [prefixWord, tailWord_7073548, baseEnd_7073548] using wordTrace_append hprefix tailTrace_7073548
  have hstable : (prefixWord ++ tailWord_7073548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073548).length < 2 ^ (prefixWord ++ tailWord_7073548).sum := by decide
  have hdescent : baseEnd_7073548 < baseStart_7073548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073549 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7073549 : Nat := 118140960795 + 7073549 * 2 ^ 59
def prefixEnd_7073549 : Nat := 4983230072969 + 3 ^ 40 * 7073549 * 2
def baseEnd_7073549 : Nat := 403570063347805604522983

theorem tailTrace_7073549 : CollatzResearch.WordTrace tailWord_7073549 prefixEnd_7073549 403570063347805604522983 := by
  unfold tailWord_7073549
  simp only [CollatzResearch.WordTrace]
  refine ⟨257993527050747513835263701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171995684700498342556842467 257993527050747513835263701)
  ·
    refine ⟨6046723290251894855513993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 257993527050747513835263701 6046723290251894855513993)
    ·
      refine ⟨4535042467688921141635495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6046723290251894855513993 4535042467688921141635495)
      ·
        refine ⟨6802563701533381712453243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4535042467688921141635495 6802563701533381712453243)
        ·
          refine ⟨10203845552300072568679865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802563701533381712453243 10203845552300072568679865)
          ·
            refine ⟨7652884164225054426509899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10203845552300072568679865 7652884164225054426509899)
            ·
              refine ⟨11479326246337581639764849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7652884164225054426509899 11479326246337581639764849)
              ·
                refine ⟨8609494684753186229823637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11479326246337581639764849 8609494684753186229823637)
                ·
                  refine ⟨403570063347805604522983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8609494684753186229823637 403570063347805604522983)
                  ·
                    rfl

theorem cell23_7073549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7073549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073549 prefixEnd_7073549 := by exact prefixLift 7073549
  have htrace : WordTrace (prefixWord ++ tailWord_7073549) baseStart_7073549 baseEnd_7073549 := by
    simpa [prefixWord, tailWord_7073549, baseEnd_7073549] using wordTrace_append hprefix tailTrace_7073549
  have hstable : (prefixWord ++ tailWord_7073549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073549).length < 2 ^ (prefixWord ++ tailWord_7073549).sum := by decide
  have hdescent : baseEnd_7073549 < baseStart_7073549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073588 : List Nat := [2, 5, 1, 1, 2, 1, 4, 7]
def baseStart_7073588 : Nat := 118140960795 + 7073588 * 2 ^ 59
def prefixEnd_7073588 : Nat := 4983230072969 + 3 ^ 40 * 7073588 * 2
def baseEnd_7073588 : Nat := 134524096143547251411821

theorem tailTrace_7073588 : CollatzResearch.WordTrace tailWord_7073588 prefixEnd_7073588 134524096143547251411821 := by
  unfold tailWord_7073588
  simp only [CollatzResearch.WordTrace]
  refine ⟨128997474748803111747966709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171996632998404148997288945 128997474748803111747966709)
  ·
    refine ⟨12093513257700291726371879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128997474748803111747966709 12093513257700291726371879)
    ·
      refine ⟨18140269886550437589557819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093513257700291726371879 18140269886550437589557819)
      ·
        refine ⟨27210404829825656384336729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140269886550437589557819 27210404829825656384336729)
        ·
          refine ⟨20407803622369242288252547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27210404829825656384336729 20407803622369242288252547)
          ·
            refine ⟨30611705433553863432378821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20407803622369242288252547 30611705433553863432378821)
            ·
              refine ⟨5739694768791349393571029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30611705433553863432378821 5739694768791349393571029)
              ·
                refine ⟨134524096143547251411821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5739694768791349393571029 134524096143547251411821)
                ·
                  rfl

theorem cell23_7073588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 7].length) (baseStart_7073588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073588 prefixEnd_7073588 := by exact prefixLift 7073588
  have htrace : WordTrace (prefixWord ++ tailWord_7073588) baseStart_7073588 baseEnd_7073588 := by
    simpa [prefixWord, tailWord_7073588, baseEnd_7073588] using wordTrace_append hprefix tailTrace_7073588
  have hstable : (prefixWord ++ tailWord_7073588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073588).length < 2 ^ (prefixWord ++ tailWord_7073588).sum := by decide
  have hdescent : baseEnd_7073588 < baseStart_7073588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073599 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 1, 2, 2]
def baseStart_7073599 : Nat := 118140960795 + 7073599 * 2 ^ 59
def prefixEnd_7073599 : Nat := 4983230072969 + 3 ^ 40 * 7073599 * 2
def baseEnd_7073599 : Nat := 3632156244162975245081617

theorem tailTrace_7073599 : CollatzResearch.WordTrace tailWord_7073599 prefixEnd_7073599 3632156244162975245081617 := by
  unfold tailWord_7073599
  simp only [CollatzResearch.WordTrace]
  refine ⟨257995350700566372374583851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171996900467044248249722567 257995350700566372374583851)
  ·
    refine ⟨386993026050849558561875777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257995350700566372374583851 386993026050849558561875777)
    ·
      refine ⟨290244769538137168921406833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386993026050849558561875777 290244769538137168921406833)
      ·
        refine ⟨217683577153602876691055125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290244769538137168921406833 217683577153602876691055125)
        ·
          refine ⟨10203917679075134844893209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 217683577153602876691055125 10203917679075134844893209)
          ·
            refine ⟨7652938259306351133669907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10203917679075134844893209 7652938259306351133669907)
            ·
              refine ⟨11479407388959526700504861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7652938259306351133669907 11479407388959526700504861)
              ·
                refine ⟨4304777770859822512689323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11479407388959526700504861 4304777770859822512689323)
                ·
                  refine ⟨6457166656289733769033985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304777770859822512689323 6457166656289733769033985)
                  ·
                    refine ⟨4842874992217300326775489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457166656289733769033985 4842874992217300326775489)
                    ·
                      refine ⟨3632156244162975245081617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842874992217300326775489 3632156244162975245081617)
                      ·
                        rfl

theorem cell23_7073599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_7073599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073599 prefixEnd_7073599 := by exact prefixLift 7073599
  have htrace : WordTrace (prefixWord ++ tailWord_7073599) baseStart_7073599 baseEnd_7073599 := by
    simpa [prefixWord, tailWord_7073599, baseEnd_7073599] using wordTrace_append hprefix tailTrace_7073599
  have hstable : (prefixWord ++ tailWord_7073599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073599).length < 2 ^ (prefixWord ++ tailWord_7073599).sum := by decide
  have hdescent : baseEnd_7073599 < baseStart_7073599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073632 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3]
def baseStart_7073632 : Nat := 118140960795 + 7073632 * 2 ^ 59
def prefixEnd_7073632 : Nat := 4983230072969 + 3 ^ 40 * 7073632 * 2
def baseEnd_7073632 : Nat := 3632173189024573615968965

theorem tailTrace_7073632 : CollatzResearch.WordTrace tailWord_7073632 prefixEnd_7073632 3632173189024573615968965 := by
  unfold tailWord_7073632
  simp only [CollatzResearch.WordTrace]
  refine ⟨128998277154723409505267575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171997702872964546007023433 128998277154723409505267575)
  ·
    refine ⟨193497415732085114257901363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128998277154723409505267575 193497415732085114257901363)
    ·
      refine ⟨290246123598127671386852045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193497415732085114257901363 290246123598127671386852045)
      ·
        refine ⟨108842296349297876770069517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290246123598127671386852045 108842296349297876770069517)
        ·
          refine ⟨40815861130986703788776069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108842296349297876770069517 40815861130986703788776069)
          ·
            refine ⟨7652973962060006960395513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40815861130986703788776069 7652973962060006960395513)
            ·
              refine ⟨5739730471545005220296635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7652973962060006960395513 5739730471545005220296635)
              ·
                refine ⟨8609595707317507830444953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739730471545005220296635 8609595707317507830444953)
                ·
                  refine ⟨6457196780488130872833715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8609595707317507830444953 6457196780488130872833715)
                  ·
                    refine ⟨9685795170732196309250573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6457196780488130872833715 9685795170732196309250573)
                    ·
                      refine ⟨3632173189024573615968965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9685795170732196309250573 3632173189024573615968965)
                      ·
                        rfl

theorem cell23_7073632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_7073632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073632 prefixEnd_7073632 := by exact prefixLift 7073632
  have htrace : WordTrace (prefixWord ++ tailWord_7073632) baseStart_7073632 baseEnd_7073632 := by
    simpa [prefixWord, tailWord_7073632, baseEnd_7073632] using wordTrace_append hprefix tailTrace_7073632
  have hstable : (prefixWord ++ tailWord_7073632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073632).length < 2 ^ (prefixWord ++ tailWord_7073632).sum := by decide
  have hdescent : baseEnd_7073632 < baseStart_7073632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073642 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7073642 : Nat := 118140960795 + 7073642 * 2 ^ 59
def prefixEnd_7073642 : Nat := 4983230072969 + 3 ^ 40 * 7073642 * 2
def baseEnd_7073642 : Nat := 3632178323831118576843919

theorem tailTrace_7073642 : CollatzResearch.WordTrace tailWord_7073642 prefixEnd_7073642 3632178323831118576843919 := by
  unfold tailWord_7073642
  simp only [CollatzResearch.WordTrace]
  refine ⟨64499229759852647679599795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171997946026273727145599453 64499229759852647679599795)
  ·
    refine ⟨96748844639778971519399693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64499229759852647679599795 96748844639778971519399693)
    ·
      refine ⟨36280816739917114319774885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96748844639778971519399693 36280816739917114319774885)
      ·
        refine ⟨6802653138734458934957791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36280816739917114319774885 6802653138734458934957791)
        ·
          refine ⟨10203979708101688402436687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802653138734458934957791 10203979708101688402436687)
          ·
            refine ⟨15305969562152532603655031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10203979708101688402436687 15305969562152532603655031)
            ·
              refine ⟨22958954343228798905482547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15305969562152532603655031 22958954343228798905482547)
              ·
                refine ⟨34438431514843198358223821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22958954343228798905482547 34438431514843198358223821)
                ·
                  refine ⟨12914411818066199384333933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34438431514843198358223821 12914411818066199384333933)
                  ·
                    refine ⟨4842904431774824769125225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12914411818066199384333933 4842904431774824769125225)
                    ·
                      refine ⟨3632178323831118576843919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842904431774824769125225 3632178323831118576843919)
                      ·
                        rfl

theorem cell23_7073642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7073642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073642 prefixEnd_7073642 := by exact prefixLift 7073642
  have htrace : WordTrace (prefixWord ++ tailWord_7073642) baseStart_7073642 baseEnd_7073642 := by
    simpa [prefixWord, tailWord_7073642, baseEnd_7073642] using wordTrace_append hprefix tailTrace_7073642
  have hstable : (prefixWord ++ tailWord_7073642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073642).length < 2 ^ (prefixWord ++ tailWord_7073642).sum := by decide
  have hdescent : baseEnd_7073642 < baseStart_7073642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073710 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7073710 : Nat := 118140960795 + 7073710 * 2 ^ 59
def prefixEnd_7073710 : Nat := 4983230072969 + 3 ^ 40 * 7073710 * 2
def baseEnd_7073710 : Nat := 3632213240515624310793607

theorem tailTrace_7073710 : CollatzResearch.WordTrace tailWord_7073710 prefixEnd_7073710 3632213240515624310793607 := by
  unfold tailWord_7073710
  simp only [CollatzResearch.WordTrace]
  refine ⟨32249924900395529791484323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 171999599468776158887916389 32249924900395529791484323)
  ·
    refine ⟨48374887350593294687226485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32249924900395529791484323 48374887350593294687226485)
    ·
      refine ⟨4535145689118121376927483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48374887350593294687226485 4535145689118121376927483)
      ·
        refine ⟨6802718533677182065391225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4535145689118121376927483 6802718533677182065391225)
        ·
          refine ⟨5102038900257886549043419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6802718533677182065391225 5102038900257886549043419)
          ·
            refine ⟨7653058350386829823565129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102038900257886549043419 7653058350386829823565129)
            ·
              refine ⟨5739793762790122367673847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653058350386829823565129 5739793762790122367673847)
              ·
                refine ⟨8609690644185183551510771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739793762790122367673847 8609690644185183551510771)
                ·
                  refine ⟨12914535966277775327266157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609690644185183551510771 12914535966277775327266157)
                  ·
                    refine ⟨4842950987354165747724809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12914535966277775327266157 4842950987354165747724809)
                    ·
                      refine ⟨3632213240515624310793607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842950987354165747724809 3632213240515624310793607)
                      ·
                        rfl

theorem cell23_7073710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7073710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073710 prefixEnd_7073710 := by exact prefixLift 7073710
  have htrace : WordTrace (prefixWord ++ tailWord_7073710) baseStart_7073710 baseEnd_7073710 := by
    simpa [prefixWord, tailWord_7073710, baseEnd_7073710] using wordTrace_append hprefix tailTrace_7073710
  have hstable : (prefixWord ++ tailWord_7073710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073710).length < 2 ^ (prefixWord ++ tailWord_7073710).sum := by decide
  have hdescent : baseEnd_7073710 < baseStart_7073710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073711 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_7073711 : Nat := 118140960795 + 7073711 * 2 ^ 59
def prefixEnd_7073711 : Nat := 4983230072969 + 3 ^ 40 * 7073711 * 2
def baseEnd_7073711 : Nat := 3632213753996278806881101

theorem tailTrace_7073711 : CollatzResearch.WordTrace tailWord_7073711 prefixEnd_7073711 3632213753996278806881101 := by
  unfold tailWord_7073711
  simp only [CollatzResearch.WordTrace]
  refine ⟨257999435676160615502660987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171999623784107077001773991 257999435676160615502660987)
  ·
    refine ⟨386999153514240923253991481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257999435676160615502660987 386999153514240923253991481)
    ·
      refine ⟨290249365135680692440493611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 386999153514240923253991481 290249365135680692440493611)
      ·
        refine ⟨435374047703521038660740417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290249365135680692440493611 435374047703521038660740417)
        ·
          refine ⟨326530535777640778995555313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435374047703521038660740417 326530535777640778995555313)
          ·
            refine ⟨244897901833230584246666485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326530535777640778995555313 244897901833230584246666485)
            ·
              refine ⟨22959178296865367273124983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244897901833230584246666485 22959178296865367273124983)
              ·
                refine ⟨34438767445298050909687475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22959178296865367273124983 34438767445298050909687475)
                ·
                  refine ⟨51658151167947076364531213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34438767445298050909687475 51658151167947076364531213)
                  ·
                    refine ⟨19371806687980153636699205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51658151167947076364531213 19371806687980153636699205)
                    ·
                      refine ⟨3632213753996278806881101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19371806687980153636699205 3632213753996278806881101)
                      ·
                        rfl

theorem cell23_7073711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_7073711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073711 prefixEnd_7073711 := by exact prefixLift 7073711
  have htrace : WordTrace (prefixWord ++ tailWord_7073711) baseStart_7073711 baseEnd_7073711 := by
    simpa [prefixWord, tailWord_7073711, baseEnd_7073711] using wordTrace_append hprefix tailTrace_7073711
  have hstable : (prefixWord ++ tailWord_7073711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073711).length < 2 ^ (prefixWord ++ tailWord_7073711).sum := by decide
  have hdescent : baseEnd_7073711 < baseStart_7073711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073728 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2]
def baseStart_7073728 : Nat := 118140960795 + 7073728 * 2 ^ 59
def prefixEnd_7073728 : Nat := 4983230072969 + 3 ^ 40 * 7073728 * 2
def baseEnd_7073728 : Nat := 3632222483167405240368523

theorem tailTrace_7073728 : CollatzResearch.WordTrace tailWord_7073728 prefixEnd_7073728 3632222483167405240368523 := by
  unfold tailWord_7073728
  simp only [CollatzResearch.WordTrace]
  refine ⟨129000027858549513703014919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172000037144732684937353225 129000027858549513703014919)
  ·
    refine ⟨193500041787824270554522379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129000027858549513703014919 193500041787824270554522379)
    ·
      refine ⟨290250062681736405831783569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193500041787824270554522379 290250062681736405831783569)
      ·
        refine ⟨217687547011302304373837677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290250062681736405831783569 217687547011302304373837677)
        ·
          refine ⟨81632830129238364140189129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217687547011302304373837677 81632830129238364140189129)
          ·
            refine ⟨61224622596928773105141847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81632830129238364140189129 61224622596928773105141847)
            ·
              refine ⟨91836933895393159657712771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61224622596928773105141847 91836933895393159657712771)
              ·
                refine ⟨137755400843089739486569157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91836933895393159657712771 137755400843089739486569157)
                ·
                  refine ⟨25829137658079326153731717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137755400843089739486569157 25829137658079326153731717)
                  ·
                    refine ⟨4842963310889873653824697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25829137658079326153731717 4842963310889873653824697)
                    ·
                      refine ⟨3632222483167405240368523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4842963310889873653824697 3632222483167405240368523)
                      ·
                        rfl

theorem cell23_7073728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_7073728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073728 prefixEnd_7073728 := by exact prefixLift 7073728
  have htrace : WordTrace (prefixWord ++ tailWord_7073728) baseStart_7073728 baseEnd_7073728 := by
    simpa [prefixWord, tailWord_7073728, baseEnd_7073728] using wordTrace_append hprefix tailTrace_7073728
  have hstable : (prefixWord ++ tailWord_7073728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073728).length < 2 ^ (prefixWord ++ tailWord_7073728).sum := by decide
  have hdescent : baseEnd_7073728 < baseStart_7073728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073731 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3]
def baseStart_7073731 : Nat := 118140960795 + 7073731 * 2 ^ 59
def prefixEnd_7073731 : Nat := 4983230072969 + 3 ^ 40 * 7073731 * 2
def baseEnd_7073731 : Nat := 3632224023609368728631009

theorem tailTrace_7073731 : CollatzResearch.WordTrace tailWord_7073731 prefixEnd_7073731 3632224023609368728631009 := by
  unfold tailWord_7073731
  simp only [CollatzResearch.WordTrace]
  refine ⟨258000165136088158918389047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172000110090725439278926031 258000165136088158918389047)
  ·
    refine ⟨387000247704132238377583571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258000165136088158918389047 387000247704132238377583571)
    ·
      refine ⟨580500371556198357566375357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387000247704132238377583571 580500371556198357566375357)
      ·
        refine ⟨217687639333574384087390759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580500371556198357566375357 217687639333574384087390759)
        ·
          refine ⟨326531459000361576131086139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217687639333574384087390759 326531459000361576131086139)
          ·
            refine ⟨489797188500542364196629209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326531459000361576131086139 489797188500542364196629209)
            ·
              refine ⟨367347891375406773147471907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489797188500542364196629209 367347891375406773147471907)
              ·
                refine ⟨551021837063110159721207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367347891375406773147471907 551021837063110159721207861)
                ·
                  refine ⟨51658297224666577473863237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 551021837063110159721207861 51658297224666577473863237)
                  ·
                    refine ⟨9685930729624983276349357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51658297224666577473863237 9685930729624983276349357)
                    ·
                      refine ⟨3632224023609368728631009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9685930729624983276349357 3632224023609368728631009)
                      ·
                        rfl

theorem cell23_7073731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_7073731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073731 prefixEnd_7073731 := by exact prefixLift 7073731
  have htrace : WordTrace (prefixWord ++ tailWord_7073731) baseStart_7073731 baseEnd_7073731 := by
    simpa [prefixWord, tailWord_7073731, baseEnd_7073731] using wordTrace_append hprefix tailTrace_7073731
  have hstable : (prefixWord ++ tailWord_7073731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073731).length < 2 ^ (prefixWord ++ tailWord_7073731).sum := by decide
  have hdescent : baseEnd_7073731 < baseStart_7073731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073738 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_7073738 : Nat := 118140960795 + 7073738 * 2 ^ 59
def prefixEnd_7073738 : Nat := 4983230072969 + 3 ^ 40 * 7073738 * 2
def baseEnd_7073738 : Nat := 1210742539324650067081159

theorem tailTrace_7073738 : CollatzResearch.WordTrace tailWord_7073738 prefixEnd_7073738 1210742539324650067081159 := by
  unfold tailWord_7073738
  simp only [CollatzResearch.WordTrace]
  refine ⟨64500105111765699778473467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172000280298041866075929245 64500105111765699778473467)
  ·
    refine ⟨96750157667648549667710201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64500105111765699778473467 96750157667648549667710201)
    ·
      refine ⟨72562618250736412250782651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96750157667648549667710201 72562618250736412250782651)
      ·
        refine ⟨108843927376104618376173977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72562618250736412250782651 108843927376104618376173977)
        ·
          refine ⟨81632945532078463782130483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108843927376104618376173977 81632945532078463782130483)
          ·
            refine ⟨122449418298117695673195725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81632945532078463782130483 122449418298117695673195725)
            ·
              refine ⟨45918531861794135877448397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122449418298117695673195725 45918531861794135877448397)
              ·
                refine ⟨17219449448172800954043149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45918531861794135877448397 17219449448172800954043149)
                ·
                  refine ⟨6457293543064800357766181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17219449448172800954043149 6457293543064800357766181)
                  ·
                    refine ⟨1210742539324650067081159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457293543064800357766181 1210742539324650067081159)
                    ·
                      rfl

theorem cell23_7073738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_7073738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073738 prefixEnd_7073738 := by exact prefixLift 7073738
  have htrace : WordTrace (prefixWord ++ tailWord_7073738) baseStart_7073738 baseEnd_7073738 := by
    simpa [prefixWord, tailWord_7073738, baseEnd_7073738] using wordTrace_append hprefix tailTrace_7073738
  have hstable : (prefixWord ++ tailWord_7073738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073738).length < 2 ^ (prefixWord ++ tailWord_7073738).sum := by decide
  have hdescent : baseEnd_7073738 < baseStart_7073738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073748 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7073748 : Nat := 118140960795 + 7073748 * 2 ^ 59
def prefixEnd_7073748 : Nat := 4983230072969 + 3 ^ 40 * 7073748 * 2
def baseEnd_7073748 : Nat := 3632232752780495162118431

theorem tailTrace_7073748 : CollatzResearch.WordTrace tailWord_7073748 prefixEnd_7073748 3632232752780495162118431 := by
  unfold tailWord_7073748
  simp only [CollatzResearch.WordTrace]
  refine ⟨129000392588513285410878949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172000523451351047214505265 129000392588513285410878949)
  ·
    refine ⟨24187573610346241014539803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129000392588513285410878949 24187573610346241014539803)
    ·
      refine ⟨36281360415519361521809705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24187573610346241014539803 36281360415519361521809705)
      ·
        refine ⟨27211020311639521141357279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36281360415519361521809705 27211020311639521141357279)
        ·
          refine ⟨40816530467459281712035919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211020311639521141357279 40816530467459281712035919)
          ·
            refine ⟨61224795701188922568053879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40816530467459281712035919 61224795701188922568053879)
            ·
              refine ⟨91837193551783383852080819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61224795701188922568053879 91837193551783383852080819)
              ·
                refine ⟨137755790327675075778121229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91837193551783383852080819 137755790327675075778121229)
                ·
                  refine ⟨51658421372878153416795461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137755790327675075778121229 51658421372878153416795461)
                  ·
                    refine ⟨9685954007414653765649149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51658421372878153416795461 9685954007414653765649149)
                    ·
                      refine ⟨3632232752780495162118431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9685954007414653765649149 3632232752780495162118431)
                      ·
                        rfl

theorem cell23_7073748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7073748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073748 prefixEnd_7073748 := by exact prefixLift 7073748
  have htrace : WordTrace (prefixWord ++ tailWord_7073748) baseStart_7073748 baseEnd_7073748 := by
    simpa [prefixWord, tailWord_7073748, baseEnd_7073748] using wordTrace_append hprefix tailTrace_7073748
  have hstable : (prefixWord ++ tailWord_7073748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073748).length < 2 ^ (prefixWord ++ tailWord_7073748).sum := by decide
  have hdescent : baseEnd_7073748 < baseStart_7073748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073782 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_7073782 : Nat := 118140960795 + 7073782 * 2 ^ 59
def prefixEnd_7073782 : Nat := 4983230072969 + 3 ^ 40 * 7073782 * 2
def baseEnd_7073782 : Nat := 3632250211122748029093275

theorem tailTrace_7073782 : CollatzResearch.WordTrace tailWord_7073782 prefixEnd_7073782 3632250211122748029093275 := by
  unfold tailWord_7073782
  simp only [CollatzResearch.WordTrace]
  refine ⟨16125126578681462164280975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172001350172602263085663733 16125126578681462164280975)
  ·
    refine ⟨24187689868022193246421463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16125126578681462164280975 24187689868022193246421463)
    ·
      refine ⟨36281534802033289869632195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24187689868022193246421463 36281534802033289869632195)
      ·
        refine ⟨54422302203049934804448293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36281534802033289869632195 54422302203049934804448293)
        ·
          refine ⟨10204181663071862775834055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54422302203049934804448293 10204181663071862775834055)
          ·
            refine ⟨15306272494607794163751083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204181663071862775834055 15306272494607794163751083)
            ·
              refine ⟨22959408741911691245626625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15306272494607794163751083 22959408741911691245626625)
              ·
                refine ⟨17219556556433768434219969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22959408741911691245626625 17219556556433768434219969)
                ·
                  refine ⟨12914667417325326325664977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17219556556433768434219969 12914667417325326325664977)
                  ·
                    refine ⟨9686000562993994744248733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12914667417325326325664977 9686000562993994744248733)
                    ·
                      refine ⟨3632250211122748029093275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9686000562993994744248733 3632250211122748029093275)
                      ·
                        rfl

theorem cell23_7073782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_7073782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073782 prefixEnd_7073782 := by exact prefixLift 7073782
  have htrace : WordTrace (prefixWord ++ tailWord_7073782) baseStart_7073782 baseEnd_7073782 := by
    simpa [prefixWord, tailWord_7073782, baseEnd_7073782] using wordTrace_append hprefix tailTrace_7073782
  have hstable : (prefixWord ++ tailWord_7073782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073782).length < 2 ^ (prefixWord ++ tailWord_7073782).sum := by decide
  have hdescent : baseEnd_7073782 < baseStart_7073782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073801 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_7073801 : Nat := 118140960795 + 7073801 * 2 ^ 59
def prefixEnd_7073801 : Nat := 4983230072969 + 3 ^ 40 * 7073801 * 2
def baseEnd_7073801 : Nat := 3632259967255183454755687

theorem tailTrace_7073801 : CollatzResearch.WordTrace tailWord_7073801 prefixEnd_7073801 3632259967255183454755687 := by
  unfold tailWord_7073801
  simp only [CollatzResearch.WordTrace]
  refine ⟨258002718245834560873437257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172001812163889707248958171 258002718245834560873437257)
  ·
    refine ⟨193502038684375920655077943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258002718245834560873437257 193502038684375920655077943)
    ·
      refine ⟨290253058026563880982616915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193502038684375920655077943 290253058026563880982616915)
      ·
        refine ⟨435379587039845821473925373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290253058026563880982616915 435379587039845821473925373)
        ·
          refine ⟨163267345139942183052722015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435379587039845821473925373 163267345139942183052722015)
          ·
            refine ⟨244901017709913274579083023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163267345139942183052722015 244901017709913274579083023)
            ·
              refine ⟨367351526564869911868624535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244901017709913274579083023 367351526564869911868624535)
              ·
                refine ⟨551027289847304867802936803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367351526564869911868624535 551027289847304867802936803)
                ·
                  refine ⟨826540934770957301704405205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551027289847304867802936803 826540934770957301704405205)
                  ·
                    refine ⟨19372053158694311758696997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 826540934770957301704405205 19372053158694311758696997)
                    ·
                      refine ⟨3632259967255183454755687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19372053158694311758696997 3632259967255183454755687)
                      ·
                        rfl

theorem cell23_7073801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_7073801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073801 prefixEnd_7073801 := by exact prefixLift 7073801
  have htrace : WordTrace (prefixWord ++ tailWord_7073801) baseStart_7073801 baseEnd_7073801 := by
    simpa [prefixWord, tailWord_7073801, baseEnd_7073801] using wordTrace_append hprefix tailTrace_7073801
  have hstable : (prefixWord ++ tailWord_7073801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073801).length < 2 ^ (prefixWord ++ tailWord_7073801).sum := by decide
  have hdescent : baseEnd_7073801 < baseStart_7073801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073802 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_7073802 : Nat := 118140960795 + 7073802 * 2 ^ 59
def prefixEnd_7073802 : Nat := 4983230072969 + 3 ^ 40 * 7073802 * 2
def baseEnd_7073802 : Nat := 403584497859537550093687

theorem tailTrace_7073802 : CollatzResearch.WordTrace tailWord_7073802 prefixEnd_7073802 403584497859537550093687 := by
  unfold tailWord_7073802
  simp only [CollatzResearch.WordTrace]
  refine ⟨64500688679707734511055915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172001836479220625362815773 64500688679707734511055915)
  ·
    refine ⟨96751033019561601766583873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64500688679707734511055915 96751033019561601766583873)
    ·
      refine ⟨72563274764671201324937905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96751033019561601766583873 72563274764671201324937905)
      ·
        refine ⟨54422456073503400993703429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72563274764671201324937905 54422456073503400993703429)
        ·
          refine ⟨10204210513781887686319393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54422456073503400993703429 10204210513781887686319393)
          ·
            refine ⟨7653157885336415764739545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204210513781887686319393 7653157885336415764739545)
            ·
              refine ⟨5739868414002311823554659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653157885336415764739545 5739868414002311823554659)
              ·
                refine ⟨8609802621003467735331989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5739868414002311823554659 8609802621003467735331989)
                ·
                  refine ⟨403584497859537550093687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8609802621003467735331989 403584497859537550093687)
                  ·
                    rfl

theorem cell23_7073802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_7073802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073802 prefixEnd_7073802 := by exact prefixLift 7073802
  have htrace : WordTrace (prefixWord ++ tailWord_7073802) baseStart_7073802 baseEnd_7073802 := by
    simpa [prefixWord, tailWord_7073802, baseEnd_7073802] using wordTrace_append hprefix tailTrace_7073802
  have hstable : (prefixWord ++ tailWord_7073802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073802).length < 2 ^ (prefixWord ++ tailWord_7073802).sum := by decide
  have hdescent : baseEnd_7073802 < baseStart_7073802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073815 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 3, 5]
def baseStart_7073815 : Nat := 118140960795 + 7073815 * 2 ^ 59
def prefixEnd_7073815 : Nat := 4983230072969 + 3 ^ 40 * 7073815 * 2
def baseEnd_7073815 : Nat := 1210755718661448799993541

theorem tailTrace_7073815 : CollatzResearch.WordTrace tailWord_7073815 prefixEnd_7073815 1210755718661448799993541 := by
  unfold tailWord_7073815
  simp only [CollatzResearch.WordTrace]
  refine ⟨258003228867783841264446899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172002152578522560842964599 258003228867783841264446899)
  ·
    refine ⟨387004843301675761896670349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258003228867783841264446899 387004843301675761896670349)
    ·
      refine ⟨145126816238128410711251381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387004843301675761896670349 145126816238128410711251381)
      ·
        refine ⟨13605639022324538504179817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145126816238128410711251381 13605639022324538504179817)
        ·
          refine ⟨10204229266743403878134863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13605639022324538504179817 10204229266743403878134863)
          ·
            refine ⟨15306343900115105817202295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204229266743403878134863 15306343900115105817202295)
            ·
              refine ⟨22959515850172658725803443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15306343900115105817202295 22959515850172658725803443)
              ·
                refine ⟨34439273775258988088705165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22959515850172658725803443 34439273775258988088705165)
                ·
                  refine ⟨12914727665722120533264437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34439273775258988088705165 12914727665722120533264437)
                  ·
                    refine ⟨1210755718661448799993541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12914727665722120533264437 1210755718661448799993541)
                    ·
                      rfl

theorem cell23_7073815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_7073815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073815 prefixEnd_7073815 := by exact prefixLift 7073815
  have htrace : WordTrace (prefixWord ++ tailWord_7073815) baseStart_7073815 baseEnd_7073815 := by
    simpa [prefixWord, tailWord_7073815, baseEnd_7073815] using wordTrace_append hprefix tailTrace_7073815
  have hstable : (prefixWord ++ tailWord_7073815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073815).length < 2 ^ (prefixWord ++ tailWord_7073815).sum := by decide
  have hdescent : baseEnd_7073815 < baseStart_7073815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073835 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 7, 2, 2]
def baseStart_7073835 : Nat := 118140960795 + 7073835 * 2 ^ 59
def prefixEnd_7073835 : Nat := 4983230072969 + 3 ^ 40 * 7073835 * 2
def baseEnd_7073835 : Nat := 3632277425597436321730531

theorem tailTrace_7073835 : CollatzResearch.WordTrace tailWord_7073835 prefixEnd_7073835 3632277425597436321730531 := by
  unfold tailWord_7073835
  simp only [CollatzResearch.WordTrace]
  refine ⟨258003958327711384680174959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172002638885140923120116639 258003958327711384680174959)
  ·
    refine ⟨387005937491567077020262439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258003958327711384680174959 387005937491567077020262439)
    ·
      refine ⟨580508906237350615530393659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387005937491567077020262439 580508906237350615530393659)
      ·
        refine ⟨870763359356025923295590489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580508906237350615530393659 870763359356025923295590489)
        ·
          refine ⟨653072519517019442471692867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870763359356025923295590489 653072519517019442471692867)
          ·
            refine ⟨979608779275529163707539301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653072519517019442471692867 979608779275529163707539301)
            ·
              refine ⟨183676646114161718195163619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 979608779275529163707539301 183676646114161718195163619)
              ·
                refine ⟨275514969171242577292745429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183676646114161718195163619 275514969171242577292745429)
                ·
                  refine ⟨6457382089950997905298721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 275514969171242577292745429 6457382089950997905298721)
                  ·
                    refine ⟨4843036567463248428974041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457382089950997905298721 4843036567463248428974041)
                    ·
                      refine ⟨3632277425597436321730531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843036567463248428974041 3632277425597436321730531)
                      ·
                        rfl

theorem cell23_7073835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2, 2].length) (baseStart_7073835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073835 prefixEnd_7073835 := by exact prefixLift 7073835
  have htrace : WordTrace (prefixWord ++ tailWord_7073835) baseStart_7073835 baseEnd_7073835 := by
    simpa [prefixWord, tailWord_7073835, baseEnd_7073835] using wordTrace_append hprefix tailTrace_7073835
  have hstable : (prefixWord ++ tailWord_7073835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073835).length < 2 ^ (prefixWord ++ tailWord_7073835).sum := by decide
  have hdescent : baseEnd_7073835 < baseStart_7073835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073841 : List Nat := [1, 2, 2, 3, 1, 14]
def baseStart_7073841 : Nat := 118140960795 + 7073841 * 2 ^ 59
def prefixEnd_7073841 : Nat := 4983230072969 + 3 ^ 40 * 7073841 * 2
def baseEnd_7073841 : Nat := 14947656405273099992821

theorem tailTrace_7073841 : CollatzResearch.WordTrace tailWord_7073841 prefixEnd_7073841 14947656405273099992821 := by
  unfold tailWord_7073841
  simp only [CollatzResearch.WordTrace]
  refine ⟨258004177165689647704893377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172002784777126431803262251 258004177165689647704893377)
  ·
    refine ⟨193503132874267235778670033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258004177165689647704893377 193503132874267235778670033)
    ·
      refine ⟨145127349655700426834002525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193503132874267235778670033 145127349655700426834002525)
      ·
        refine ⟨54422756120887660062750947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145127349655700426834002525 54422756120887660062750947)
        ·
          refine ⟨81634134181331490094126421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54422756120887660062750947 81634134181331490094126421)
          ·
            refine ⟨14947656405273099992821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 81634134181331490094126421 14947656405273099992821)
            ·
              rfl

theorem cell23_7073841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 14].length) (baseStart_7073841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073841 prefixEnd_7073841 := by exact prefixLift 7073841
  have htrace : WordTrace (prefixWord ++ tailWord_7073841) baseStart_7073841 baseEnd_7073841 := by
    simpa [prefixWord, tailWord_7073841, baseEnd_7073841] using wordTrace_append hprefix tailTrace_7073841
  have hstable : (prefixWord ++ tailWord_7073841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073841).length < 2 ^ (prefixWord ++ tailWord_7073841).sum := by decide
  have hdescent : baseEnd_7073841 < baseStart_7073841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073845 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7073845 : Nat := 118140960795 + 7073845 * 2 ^ 59
def prefixEnd_7073845 : Nat := 4983230072969 + 3 ^ 40 * 7073845 * 2
def baseEnd_7073845 : Nat := 1210760853467993760868495

theorem tailTrace_7073845 : CollatzResearch.WordTrace tailWord_7073845 prefixEnd_7073845 1210760853467993760868495 := by
  unfold tailWord_7073845
  simp only [CollatzResearch.WordTrace]
  refine ⟨258004323057675156388038989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172002882038450104258692659 258004323057675156388038989)
  ·
    refine ⟨96751621146628183645514621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258004323057675156388038989 96751621146628183645514621)
    ·
      refine ⟨36281857929985568867067983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96751621146628183645514621 36281857929985568867067983)
      ·
        refine ⟨54422786894978353300601975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36281857929985568867067983 54422786894978353300601975)
        ·
          refine ⟨81634180342467529950902963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54422786894978353300601975 81634180342467529950902963)
          ·
            refine ⟨122451270513701294926354445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81634180342467529950902963 122451270513701294926354445)
            ·
              refine ⟨45919226442637985597382917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122451270513701294926354445 45919226442637985597382917)
              ·
                refine ⟨8609854957994622299509297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45919226442637985597382917 8609854957994622299509297)
                ·
                  refine ⟨6457391218495966724631973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8609854957994622299509297 6457391218495966724631973)
                  ·
                    refine ⟨1210760853467993760868495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457391218495966724631973 1210760853467993760868495)
                    ·
                      rfl

theorem cell23_7073845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7073845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073845 prefixEnd_7073845 := by exact prefixLift 7073845
  have htrace : WordTrace (prefixWord ++ tailWord_7073845) baseStart_7073845 baseEnd_7073845 := by
    simpa [prefixWord, tailWord_7073845, baseEnd_7073845] using wordTrace_append hprefix tailTrace_7073845
  have hstable : (prefixWord ++ tailWord_7073845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073845).length < 2 ^ (prefixWord ++ tailWord_7073845).sum := by decide
  have hdescent : baseEnd_7073845 < baseStart_7073845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073852 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_7073852 : Nat := 118140960795 + 7073852 * 2 ^ 59
def prefixEnd_7073852 : Nat := 4983230072969 + 3 ^ 40 * 7073852 * 2
def baseEnd_7073852 : Nat := 3632286154768562755217953

theorem tailTrace_7073852 : CollatzResearch.WordTrace tailWord_7073852 prefixEnd_7073852 3632286154768562755217953 := by
  unfold tailWord_7073852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129002289184324898291771905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172003052245766531055695873 129002289184324898291771905)
  ·
    refine ⟨96751716888243673718828929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129002289184324898291771905 96751716888243673718828929)
    ·
      refine ⟨72563787666182755289121697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96751716888243673718828929 72563787666182755289121697)
      ·
        refine ⟨54422840749637066466841273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72563787666182755289121697 54422840749637066466841273)
        ·
          refine ⟨40817130562227799850130955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54422840749637066466841273 40817130562227799850130955)
          ·
            refine ⟨61225695843341699775196433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40817130562227799850130955 61225695843341699775196433)
            ·
              refine ⟨45919271882506274831397325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61225695843341699775196433 45919271882506274831397325)
              ·
                refine ⟨17219726955939853061773997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45919271882506274831397325 17219726955939853061773997)
                ·
                  refine ⟨6457397608477444898165249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17219726955939853061773997 6457397608477444898165249)
                  ·
                    refine ⟨4843048206358083673623937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457397608477444898165249 4843048206358083673623937)
                    ·
                      refine ⟨3632286154768562755217953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843048206358083673623937 3632286154768562755217953)
                      ·
                        rfl

theorem cell23_7073852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_7073852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073852 prefixEnd_7073852 := by exact prefixLift 7073852
  have htrace : WordTrace (prefixWord ++ tailWord_7073852) baseStart_7073852 baseEnd_7073852 := by
    simpa [prefixWord, tailWord_7073852, baseEnd_7073852] using wordTrace_append hprefix tailTrace_7073852
  have hstable : (prefixWord ++ tailWord_7073852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073852).length < 2 ^ (prefixWord ++ tailWord_7073852).sum := by decide
  have hdescent : baseEnd_7073852 < baseStart_7073852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073862 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_7073862 : Nat := 118140960795 + 7073862 * 2 ^ 59
def prefixEnd_7073862 : Nat := 4983230072969 + 3 ^ 40 * 7073862 * 2
def baseEnd_7073862 : Nat := 1210763763191702572030969

theorem tailTrace_7073862 : CollatzResearch.WordTrace tailWord_7073862 prefixEnd_7073862 1210763763191702572030969 := by
  unfold tailWord_7073862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062654471831674009106495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172003295399075712194271893 8062654471831674009106495)
  ·
    refine ⟨12093981707747511013659743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8062654471831674009106495 12093981707747511013659743)
    ·
      refine ⟨18140972561621266520489615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093981707747511013659743 18140972561621266520489615)
      ·
        refine ⟨27211458842431899780734423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140972561621266520489615 27211458842431899780734423)
        ·
          refine ⟨40817188263647849671101635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211458842431899780734423 40817188263647849671101635)
          ·
            refine ⟨61225782395471774506652453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40817188263647849671101635 61225782395471774506652453)
            ·
              refine ⟨11479834199150957719997335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61225782395471774506652453 11479834199150957719997335)
              ·
                refine ⟨17219751298726436579996003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11479834199150957719997335 17219751298726436579996003)
                ·
                  refine ⟨25829626948089654869994005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17219751298726436579996003 25829626948089654869994005)
                  ·
                    refine ⟨1210763763191702572030969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25829626948089654869994005 1210763763191702572030969)
                    ·
                      rfl

theorem cell23_7073862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_7073862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073862 prefixEnd_7073862 := by exact prefixLift 7073862
  have htrace : WordTrace (prefixWord ++ tailWord_7073862) baseStart_7073862 baseEnd_7073862 := by
    simpa [prefixWord, tailWord_7073862, baseEnd_7073862] using wordTrace_append hprefix tailTrace_7073862
  have hstable : (prefixWord ++ tailWord_7073862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073862).length < 2 ^ (prefixWord ++ tailWord_7073862).sum := by decide
  have hdescent : baseEnd_7073862 < baseStart_7073862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073869 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7073869 : Nat := 118140960795 + 7073869 * 2 ^ 59
def prefixEnd_7073869 : Nat := 4983230072969 + 3 ^ 40 * 7073869 * 2
def baseEnd_7073869 : Nat := 3632294883939689188705375

theorem tailTrace_7073869 : CollatzResearch.WordTrace tailWord_7073869 prefixEnd_7073869 3632294883939689188705375 := by
  unfold tailWord_7073869
  simp only [CollatzResearch.WordTrace]
  refine ⟨258005198409588208486912661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172003465606392138991275107 258005198409588208486912661)
  ·
    refine ⟨12093993675449447272824031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258005198409588208486912661 12093993675449447272824031)
    ·
      refine ⟨18140990513174170909236047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12093993675449447272824031 18140990513174170909236047)
      ·
        refine ⟨27211485769761256363854071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140990513174170909236047 27211485769761256363854071)
        ·
          refine ⟨40817228654641884545781107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211485769761256363854071 40817228654641884545781107)
          ·
            refine ⟨61225842981962826818671661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40817228654641884545781107 61225842981962826818671661)
            ·
              refine ⟨22959691118236060057001873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61225842981962826818671661 22959691118236060057001873)
              ·
                refine ⟨17219768338677045042751405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22959691118236060057001873 17219768338677045042751405)
                ·
                  refine ⟨6457413127003891891031777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17219768338677045042751405 6457413127003891891031777)
                  ·
                    refine ⟨4843059845252918918273833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6457413127003891891031777 4843059845252918918273833)
                    ·
                      refine ⟨3632294883939689188705375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843059845252918918273833 3632294883939689188705375)
                      ·
                        rfl

theorem cell23_7073869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7073869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073869 prefixEnd_7073869 := by exact prefixLift 7073869
  have htrace : WordTrace (prefixWord ++ tailWord_7073869) baseStart_7073869 baseEnd_7073869 := by
    simpa [prefixWord, tailWord_7073869, baseEnd_7073869] using wordTrace_append hprefix tailTrace_7073869
  have hstable : (prefixWord ++ tailWord_7073869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073869).length < 2 ^ (prefixWord ++ tailWord_7073869).sum := by decide
  have hdescent : baseEnd_7073869 < baseStart_7073869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073886 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7073886 : Nat := 118140960795 + 7073886 * 2 ^ 59
def prefixEnd_7073886 : Nat := 4983230072969 + 3 ^ 40 * 7073886 * 2
def baseEnd_7073886 : Nat := 3632303613110815622192797

theorem tailTrace_7073886 : CollatzResearch.WordTrace tailWord_7073886 prefixEnd_7073886 3632303613110815622192797 := by
  unfold tailWord_7073886
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250727306315827548785189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172003878967017746926854341 32250727306315827548785189)
  ·
    refine ⟨6047011369934217665397223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32250727306315827548785189 6047011369934217665397223)
    ·
      refine ⟨9070517054901326498095835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6047011369934217665397223 9070517054901326498095835)
      ·
        refine ⟨13605775582351989747143753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9070517054901326498095835 13605775582351989747143753)
        ·
          refine ⟨10204331686763992310357815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13605775582351989747143753 10204331686763992310357815)
          ·
            refine ⟨15306497530145988465536723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10204331686763992310357815 15306497530145988465536723)
            ·
              refine ⟨22959746295218982698305085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15306497530145988465536723 22959746295218982698305085)
              ·
                refine ⟨8609904860707118511864407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22959746295218982698305085 8609904860707118511864407)
                ·
                  refine ⟨12914857291060677767796611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8609904860707118511864407 12914857291060677767796611)
                  ·
                    refine ⟨19372285936591016651694917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12914857291060677767796611 19372285936591016651694917)
                    ·
                      refine ⟨3632303613110815622192797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19372285936591016651694917 3632303613110815622192797)
                      ·
                        rfl

theorem cell23_7073886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7073886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073886 prefixEnd_7073886 := by exact prefixLift 7073886
  have htrace : WordTrace (prefixWord ++ tailWord_7073886) baseStart_7073886 baseEnd_7073886 := by
    simpa [prefixWord, tailWord_7073886, baseEnd_7073886] using wordTrace_append hprefix tailTrace_7073886
  have hstable : (prefixWord ++ tailWord_7073886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073886).length < 2 ^ (prefixWord ++ tailWord_7073886).sum := by decide
  have hdescent : baseEnd_7073886 < baseStart_7073886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073902 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_7073902 : Nat := 118140960795 + 7073902 * 2 ^ 59
def prefixEnd_7073902 : Nat := 4983230072969 + 3 ^ 40 * 7073902 * 2
def baseEnd_7073902 : Nat := 3632311828801287559592723

theorem tailTrace_7073902 : CollatzResearch.WordTrace tailWord_7073902 prefixEnd_7073902 3632311828801287559592723 := by
  unfold tailWord_7073902
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250800252308581890357995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172004268012312436748575973 32250800252308581890357995)
  ·
    refine ⟨48376200378462872835536993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32250800252308581890357995 48376200378462872835536993)
    ·
      refine ⟨36282150283847154626652745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48376200378462872835536993 36282150283847154626652745)
      ·
        refine ⟨27211612712885365969989559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36282150283847154626652745 27211612712885365969989559)
        ·
          refine ⟨40817419069328048954984339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211612712885365969989559 40817419069328048954984339)
          ·
            refine ⟨61226128603992073432476509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40817419069328048954984339 61226128603992073432476509)
            ·
              refine ⟨22959798226497027537178691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61226128603992073432476509 22959798226497027537178691)
              ·
                refine ⟨34439697339745541305768037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22959798226497027537178691 34439697339745541305768037)
                ·
                  refine ⟨6457443251202288994831507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34439697339745541305768037 6457443251202288994831507)
                  ·
                    refine ⟨9686164876803433492247261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6457443251202288994831507 9686164876803433492247261)
                    ·
                      refine ⟨3632311828801287559592723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9686164876803433492247261 3632311828801287559592723)
                      ·
                        rfl

theorem cell23_7073902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_7073902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073902 prefixEnd_7073902 := by exact prefixLift 7073902
  have htrace : WordTrace (prefixWord ++ tailWord_7073902) baseStart_7073902 baseEnd_7073902 := by
    simpa [prefixWord, tailWord_7073902, baseEnd_7073902] using wordTrace_append hprefix tailTrace_7073902
  have hstable : (prefixWord ++ tailWord_7073902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073902).length < 2 ^ (prefixWord ++ tailWord_7073902).sum := by decide
  have hdescent : baseEnd_7073902 < baseStart_7073902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073978 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_7073978 : Nat := 118140960795 + 7073978 * 2 ^ 59
def prefixEnd_7073978 : Nat := 4983230072969 + 3 ^ 40 * 7073978 * 2
def baseEnd_7073978 : Nat := 1210783617777009754080791

theorem tailTrace_7073978 : CollatzResearch.WordTrace tailWord_7073978 prefixEnd_7073978 1210783617777009754080791 := by
  unfold tailWord_7073978
  simp only [CollatzResearch.WordTrace]
  refine ⟨64502293491548330025657647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172006115977462213401753725 64502293491548330025657647)
  ·
    refine ⟨96753440237322495038486471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64502293491548330025657647 96753440237322495038486471)
    ·
      refine ⟨145130160355983742557729707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96753440237322495038486471 145130160355983742557729707)
      ·
        refine ⟨217695240533975613836594561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145130160355983742557729707 217695240533975613836594561)
        ·
          refine ⟨163271430400481710377445921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217695240533975613836594561 163271430400481710377445921)
          ·
            refine ⟨122453572800361282783084441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163271430400481710377445921 122453572800361282783084441)
            ·
              refine ⟨91840179600270962087313331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122453572800361282783084441 91840179600270962087313331)
              ·
                refine ⟨137760269400406443130969997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91840179600270962087313331 137760269400406443130969997)
                ·
                  refine ⟨51660101025152416174113749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137760269400406443130969997 51660101025152416174113749)
                  ·
                    refine ⟨1210783617777009754080791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51660101025152416174113749 1210783617777009754080791)
                    ·
                      rfl

theorem cell23_7073978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_7073978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073978 prefixEnd_7073978 := by exact prefixLift 7073978
  have htrace : WordTrace (prefixWord ++ tailWord_7073978) baseStart_7073978 baseEnd_7073978 := by
    simpa [prefixWord, tailWord_7073978, baseEnd_7073978] using wordTrace_append hprefix tailTrace_7073978
  have hstable : (prefixWord ++ tailWord_7073978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073978).length < 2 ^ (prefixWord ++ tailWord_7073978).sum := by decide
  have hdescent : baseEnd_7073978 < baseStart_7073978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7073995 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 2, 5]
def baseStart_7073995 : Nat := 118140960795 + 7073995 * 2 ^ 59
def prefixEnd_7073995 : Nat := 4983230072969 + 3 ^ 40 * 7073995 * 2
def baseEnd_7073995 : Nat := 1210786527500718565243265

theorem tailTrace_7073995 : CollatzResearch.WordTrace tailWord_7073995 prefixEnd_7073995 1210786527500718565243265 := by
  unfold tailWord_7073995
  simp only [CollatzResearch.WordTrace]
  refine ⟨258009794007131732005999439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172006529338087821337332959 258009794007131732005999439)
  ·
    refine ⟨387014691010697598008999159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258009794007131732005999439 387014691010697598008999159)
    ·
      refine ⟨580522036516046397013498739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387014691010697598008999159 580522036516046397013498739)
      ·
        refine ⟨870783054774069595520248109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580522036516046397013498739 870783054774069595520248109)
        ·
          refine ⟨326543645540276098320093041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 870783054774069595520248109 326543645540276098320093041)
          ·
            refine ⟨244907734155207073740069781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326543645540276098320093041 244907734155207073740069781)
            ·
              refine ⟨11480050038525331581565771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244907734155207073740069781 11480050038525331581565771)
              ·
                refine ⟨17220075057787997372348657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11480050038525331581565771 17220075057787997372348657)
                ·
                  refine ⟨12915056293340998029261493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17220075057787997372348657 12915056293340998029261493)
                  ·
                    refine ⟨1210786527500718565243265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12915056293340998029261493 1210786527500718565243265)
                    ·
                      rfl

theorem cell23_7073995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 5].length) (baseStart_7073995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7073995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7073995 prefixEnd_7073995 := by exact prefixLift 7073995
  have htrace : WordTrace (prefixWord ++ tailWord_7073995) baseStart_7073995 baseEnd_7073995 := by
    simpa [prefixWord, tailWord_7073995, baseEnd_7073995] using wordTrace_append hprefix tailTrace_7073995
  have hstable : (prefixWord ++ tailWord_7073995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7073995).length < 2 ^ (prefixWord ++ tailWord_7073995).sum := by decide
  have hdescent : baseEnd_7073995 < baseStart_7073995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7073995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074035 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3]
def baseStart_7074035 : Nat := 118140960795 + 7074035 * 2 ^ 59
def prefixEnd_7074035 : Nat := 4983230072969 + 3 ^ 40 * 7074035 * 2
def baseEnd_7074035 : Nat := 3632380121728335539229611

theorem tailTrace_7074035 : CollatzResearch.WordTrace tailWord_7074035 prefixEnd_7074035 3632380121728335539229611 := by
  unfold tailWord_7074035
  simp only [CollatzResearch.WordTrace]
  refine ⟨258011252926986818837455559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172007501951324545891637039 258011252926986818837455559)
  ·
    refine ⟨387016879390480228256183339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258011252926986818837455559 387016879390480228256183339)
    ·
      refine ⟨580525319085720342384275009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387016879390480228256183339 580525319085720342384275009)
      ·
        refine ⟨435393989314290256788206257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580525319085720342384275009 435393989314290256788206257)
        ·
          refine ⟨326545491985717692591154693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435393989314290256788206257 326545491985717692591154693)
          ·
            refine ⟨61227279747322067360841505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326545491985717692591154693 61227279747322067360841505)
            ·
              refine ⟨45920459810491550520631129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61227279747322067360841505 45920459810491550520631129)
              ·
                refine ⟨34440344857868662890473347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45920459810491550520631129 34440344857868662890473347)
                ·
                  refine ⟨51660517286802994335710021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34440344857868662890473347 51660517286802994335710021)
                  ·
                    refine ⟨9686346991275561437945629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51660517286802994335710021 9686346991275561437945629)
                    ·
                      refine ⟨3632380121728335539229611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9686346991275561437945629 3632380121728335539229611)
                      ·
                        rfl

theorem cell23_7074035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_7074035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074035 prefixEnd_7074035 := by exact prefixLift 7074035
  have htrace : WordTrace (prefixWord ++ tailWord_7074035) baseStart_7074035 baseEnd_7074035 := by
    simpa [prefixWord, tailWord_7074035, baseEnd_7074035] using wordTrace_append hprefix tailTrace_7074035
  have hstable : (prefixWord ++ tailWord_7074035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074035).length < 2 ^ (prefixWord ++ tailWord_7074035).sum := by decide
  have hdescent : baseEnd_7074035 < baseStart_7074035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074042 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_7074042 : Nat := 118140960795 + 7074042 * 2 ^ 59
def prefixEnd_7074042 : Nat := 4983230072969 + 3 ^ 40 * 7074042 * 2
def baseEnd_7074042 : Nat := 1210794572030972337280693

theorem tailTrace_7074042 : CollatzResearch.WordTrace tailWord_7074042 prefixEnd_7074042 1210794572030972337280693 := by
  unfold tailWord_7074042
  simp only [CollatzResearch.WordTrace]
  refine ⟨64502877059490364758240095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172007672158640972688640253 64502877059490364758240095)
  ·
    refine ⟨96754315589235547137360143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64502877059490364758240095 96754315589235547137360143)
    ·
      refine ⟨145131473383853320706040215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96754315589235547137360143 145131473383853320706040215)
      ·
        refine ⟨217697210075779981059060323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145131473383853320706040215 217697210075779981059060323)
        ·
          refine ⟨326545815113669971588590485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217697210075779981059060323 326545815113669971588590485)
          ·
            refine ⟨15306835083453279918215179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326545815113669971588590485 15306835083453279918215179)
            ·
              refine ⟨22960252625179919877322769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15306835083453279918215179 22960252625179919877322769)
              ·
                refine ⟨17220189468884939907992077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22960252625179919877322769 17220189468884939907992077)
                ·
                  refine ⟨6457571050831852465497029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17220189468884939907992077 6457571050831852465497029)
                  ·
                    refine ⟨1210794572030972337280693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457571050831852465497029 1210794572030972337280693)
                    ·
                      rfl

theorem cell23_7074042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_7074042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074042 prefixEnd_7074042 := by exact prefixLift 7074042
  have htrace : WordTrace (prefixWord ++ tailWord_7074042) baseStart_7074042 baseEnd_7074042 := by
    simpa [prefixWord, tailWord_7074042, baseEnd_7074042] using wordTrace_append hprefix tailTrace_7074042
  have hstable : (prefixWord ++ tailWord_7074042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074042).length < 2 ^ (prefixWord ++ tailWord_7074042).sum := by decide
  have hdescent : baseEnd_7074042 < baseStart_7074042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074059 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 1, 4]
def baseStart_7074059 : Nat := 118140960795 + 7074059 * 2 ^ 59
def prefixEnd_7074059 : Nat := 4983230072969 + 3 ^ 40 * 7074059 * 2
def baseEnd_7074059 : Nat := 1210797481754681148443167

theorem tailTrace_7074059 : CollatzResearch.WordTrace tailWord_7074059 prefixEnd_7074059 1210797481754681148443167 := by
  unfold tailWord_7074059
  simp only [CollatzResearch.WordTrace]
  refine ⟨258012128278899870936329231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172008085519266580624219487 258012128278899870936329231)
  ·
    refine ⟨387018192418349806404493847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258012128278899870936329231 387018192418349806404493847)
    ·
      refine ⟨580527288627524709606740771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387018192418349806404493847 580527288627524709606740771)
      ·
        refine ⟨870790932941287064410111157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580527288627524709606740771 870790932941287064410111157)
        ·
          refine ⟨81636649963245662288447921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 870790932941287064410111157 81636649963245662288447921)
          ·
            refine ⟨61227487472434246716335941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81636649963245662288447921 61227487472434246716335941)
            ·
              refine ⟨11480153901081421259312989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61227487472434246716335941 11480153901081421259312989)
              ·
                refine ⟨4305057712905532972242371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11480153901081421259312989 4305057712905532972242371)
                ·
                  refine ⟨6457586569358299458363557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305057712905532972242371 6457586569358299458363557)
                  ·
                    refine ⟨1210797481754681148443167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457586569358299458363557 1210797481754681148443167)
                    ·
                      rfl

theorem cell23_7074059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 4].length) (baseStart_7074059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074059 prefixEnd_7074059 := by exact prefixLift 7074059
  have htrace : WordTrace (prefixWord ++ tailWord_7074059) baseStart_7074059 baseEnd_7074059 := by
    simpa [prefixWord, tailWord_7074059, baseEnd_7074059] using wordTrace_append hprefix tailTrace_7074059
  have hstable : (prefixWord ++ tailWord_7074059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074059).length < 2 ^ (prefixWord ++ tailWord_7074059).sum := by decide
  have hdescent : baseEnd_7074059 < baseStart_7074059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074092 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_7074092 : Nat := 118140960795 + 7074092 * 2 ^ 59
def prefixEnd_7074092 : Nat := 4983230072969 + 3 ^ 40 * 7074092 * 2
def baseEnd_7074092 : Nat := 3632409390125641816216849

theorem tailTrace_7074092 : CollatzResearch.WordTrace tailWord_7074092 prefixEnd_7074092 3632409390125641816216849 := by
  unfold tailWord_7074092
  simp only [CollatzResearch.WordTrace]
  refine ⟨129006665943890158786140265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172008887925186878381520353 129006665943890158786140265)
  ·
    refine ⟨96754999457917619089605199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129006665943890158786140265 96754999457917619089605199)
    ·
      refine ⟨145132499186876428634407799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96754999457917619089605199 145132499186876428634407799)
      ·
        refine ⟨217698748780314642951611699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145132499186876428634407799 217698748780314642951611699)
        ·
          refine ⟨326548123170471964427417549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217698748780314642951611699 326548123170471964427417549)
          ·
            refine ⟨122455546188926986660281581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326548123170471964427417549 122455546188926986660281581)
            ·
              refine ⟨45920829820847619997605593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122455546188926986660281581 45920829820847619997605593)
              ·
                refine ⟨34440622365635714998204195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45920829820847619997605593 34440622365635714998204195)
                ·
                  refine ⟨51660933548453572497306293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34440622365635714998204195 51660933548453572497306293)
                  ·
                    refine ⟨4843212520167522421622465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51660933548453572497306293 4843212520167522421622465)
                    ·
                      refine ⟨3632409390125641816216849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4843212520167522421622465 3632409390125641816216849)
                      ·
                        rfl

theorem cell23_7074092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_7074092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074092 prefixEnd_7074092 := by exact prefixLift 7074092
  have htrace : WordTrace (prefixWord ++ tailWord_7074092) baseStart_7074092 baseEnd_7074092 := by
    simpa [prefixWord, tailWord_7074092, baseEnd_7074092] using wordTrace_append hprefix tailTrace_7074092
  have hstable : (prefixWord ++ tailWord_7074092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074092).length < 2 ^ (prefixWord ++ tailWord_7074092).sum := by decide
  have hdescent : baseEnd_7074092 < baseStart_7074092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7074115 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 1, 6]
def baseStart_7074115 : Nat := 118140960795 + 7074115 * 2 ^ 59
def prefixEnd_7074115 : Nat := 4983230072969 + 3 ^ 40 * 7074115 * 2
def baseEnd_7074115 : Nat := 1210807066726898408743081

theorem tailTrace_7074115 : CollatzResearch.WordTrace tailWord_7074115 prefixEnd_7074115 1210807066726898408743081 := by
  unfold tailWord_7074115
  simp only [CollatzResearch.WordTrace]
  refine ⟨258014170766696992500367799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172009447177797995000245199 258014170766696992500367799)
  ·
    refine ⟨387021256150045488750551699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258014170766696992500367799 387021256150045488750551699)
    ·
      refine ⟨580531884225068233125827549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387021256150045488750551699 580531884225068233125827549)
      ·
        refine ⟨217699456584400587422185331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580531884225068233125827549 217699456584400587422185331)
        ·
          refine ⟨326549184876600881133277997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217699456584400587422185331 326549184876600881133277997)
          ·
            refine ⟨122455944328725330424979249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326549184876600881133277997 122455944328725330424979249)
            ·
              refine ⟨91841958246543997818734437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122455944328725330424979249 91841958246543997818734437)
              ·
                refine ⟨17220367171226999591012707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91841958246543997818734437 17220367171226999591012707)
                ·
                  refine ⟨25830550756840499386519061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17220367171226999591012707 25830550756840499386519061)
                  ·
                    refine ⟨1210807066726898408743081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25830550756840499386519061 1210807066726898408743081)
                    ·
                      rfl

theorem cell23_7074115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 6].length) (baseStart_7074115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7074115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7074115 prefixEnd_7074115 := by exact prefixLift 7074115
  have htrace : WordTrace (prefixWord ++ tailWord_7074115) baseStart_7074115 baseEnd_7074115 := by
    simpa [prefixWord, tailWord_7074115, baseEnd_7074115] using wordTrace_append hprefix tailTrace_7074115
  have hstable : (prefixWord ++ tailWord_7074115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7074115).length < 2 ^ (prefixWord ++ tailWord_7074115).sum := by decide
  have hdescent : baseEnd_7074115 < baseStart_7074115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7074115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
