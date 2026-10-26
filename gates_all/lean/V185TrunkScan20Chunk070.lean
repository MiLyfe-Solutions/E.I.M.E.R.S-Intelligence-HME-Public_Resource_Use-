import V185TrunkScan20Chunk069

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_425158 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_425158 : Nat := 118140960795 + 425158 * 2 ^ 59
def prefixEnd_425158 : Nat := 4983230072969 + 3 ^ 40 * 425158 * 2
def baseEnd_425158 : Nat := 194053696092758045395325

theorem tailTrace_425158 : CollatzResearch.WordTrace tailWord_425158 prefixEnd_425158 194053696092758045395325 := by
  unfold tailWord_425158
  simp only [CollatzResearch.WordTrace]
  refine ⟨484587068554145376582379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10337857462488434700424085 484587068554145376582379)
  ·
    refine ⟨726880602831218064873569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484587068554145376582379 726880602831218064873569)
    ·
      refine ⟨545160452123413548655177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 726880602831218064873569 545160452123413548655177)
      ·
        refine ⟨408870339092560161491383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545160452123413548655177 408870339092560161491383)
        ·
          refine ⟨613305508638840242237075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408870339092560161491383 613305508638840242237075)
          ·
            refine ⟨919958262958260363355613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613305508638840242237075 919958262958260363355613)
            ·
              refine ⟨344984348609347636258355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919958262958260363355613 344984348609347636258355)
              ·
                refine ⟨517476522914021454387533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344984348609347636258355 517476522914021454387533)
                ·
                  refine ⟨194053696092758045395325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517476522914021454387533 194053696092758045395325)
                  ·
                    rfl

theorem cell20_425158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_425158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425158 prefixEnd_425158 := by exact prefixLift 425158
  have htrace : WordTrace (prefixWord ++ tailWord_425158) baseStart_425158 baseEnd_425158 := by
    simpa [prefixWord, tailWord_425158, baseEnd_425158] using wordTrace_append hprefix tailTrace_425158
  have hstable : (prefixWord ++ tailWord_425158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425158).length < 2 ^ (prefixWord ++ tailWord_425158).sum := by decide
  have hdescent : baseEnd_425158 < baseStart_425158 := by decide
  rcases family_descends (prefixWord ++ tailWord_425158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425173 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_425173 : Nat := 118140960795 + 425173 * 2 ^ 59
def prefixEnd_425173 : Nat := 4983230072969 + 3 ^ 40 * 425173 * 2
def baseEnd_425173 : Nat := 194060542501484659895263

theorem tailTrace_425173 : CollatzResearch.WordTrace tailWord_425173 prefixEnd_425173 194060542501484659895263 := by
  unfold tailWord_425173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15507333288678309612432173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10338222192452206408288115 15507333288678309612432173)
  ·
    refine ⟨5815249983254366104662065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15507333288678309612432173 5815249983254366104662065)
    ·
      refine ⟨4361437487440774578496549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5815249983254366104662065 4361437487440774578496549)
      ·
        refine ⟨817769528895145233468103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4361437487440774578496549 817769528895145233468103)
        ·
          refine ⟨1226654293342717850202155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817769528895145233468103 1226654293342717850202155)
          ·
            refine ⟨1839981440014076775303233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226654293342717850202155 1839981440014076775303233)
            ·
              refine ⟨1379986080010557581477425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839981440014076775303233 1379986080010557581477425)
              ·
                refine ⟨1034989560007918186108069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379986080010557581477425 1034989560007918186108069)
                ·
                  refine ⟨194060542501484659895263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034989560007918186108069 194060542501484659895263)
                  ·
                    rfl

theorem cell20_425173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_425173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425173 prefixEnd_425173 := by exact prefixLift 425173
  have htrace : WordTrace (prefixWord ++ tailWord_425173) baseStart_425173 baseEnd_425173 := by
    simpa [prefixWord, tailWord_425173, baseEnd_425173] using wordTrace_append hprefix tailTrace_425173
  have hstable : (prefixWord ++ tailWord_425173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425173).length < 2 ^ (prefixWord ++ tailWord_425173).sum := by decide
  have hdescent : baseEnd_425173 < baseStart_425173 := by decide
  rcases family_descends (prefixWord ++ tailWord_425173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425176 : List Nat := [2, 1, 2, 2, 6, 1, 2, 4]
def baseStart_425176 : Nat := 118140960795 + 425176 * 2 ^ 59
def prefixEnd_425176 : Nat := 4983230072969 + 3 ^ 40 * 425176 * 2
def baseEnd_425176 : Nat := 64687303927743327598417

theorem tailTrace_425176 : CollatzResearch.WordTrace tailWord_425176 prefixEnd_425176 64687303927743327598417 := by
  unfold tailWord_425176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753721353833720562395691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10338295138444960749860921 7753721353833720562395691)
  ·
    refine ⟨11630582030750580843593537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7753721353833720562395691 11630582030750580843593537)
    ·
      refine ⟨8722936523062935632695153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11630582030750580843593537 8722936523062935632695153)
      ·
        refine ⟨6542202392297201724521365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8722936523062935632695153 6542202392297201724521365)
        ·
          refine ⟨306665737138931330836939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6542202392297201724521365 306665737138931330836939)
          ·
            refine ⟨459998605708396996255409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306665737138931330836939 459998605708396996255409)
            ·
              refine ⟨344998954281297747191557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459998605708396996255409 344998954281297747191557)
              ·
                refine ⟨64687303927743327598417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344998954281297747191557 64687303927743327598417)
                ·
                  rfl

theorem cell20_425176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_425176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425176 prefixEnd_425176 := by exact prefixLift 425176
  have htrace : WordTrace (prefixWord ++ tailWord_425176) baseStart_425176 baseEnd_425176 := by
    simpa [prefixWord, tailWord_425176, baseEnd_425176] using wordTrace_append hprefix tailTrace_425176
  have hstable : (prefixWord ++ tailWord_425176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425176).length < 2 ^ (prefixWord ++ tailWord_425176).sum := by decide
  have hdescent : baseEnd_425176 < baseStart_425176 := by decide
  rcases family_descends (prefixWord ++ tailWord_425176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425225 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_425225 : Nat := 118140960795 + 425225 * 2 ^ 59
def prefixEnd_425225 : Nat := 4983230072969 + 3 ^ 40 * 425225 * 2
def baseEnd_425225 : Nat := 194084276718403590161717

theorem tailTrace_425225 : CollatzResearch.WordTrace tailWord_425225 prefixEnd_425225 194084276718403590161717 := by
  unfold tailWord_425225
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509229884489922493325129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10339486589659948328883419 15509229884489922493325129)
  ·
    refine ⟨11631922413367441869993847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15509229884489922493325129 11631922413367441869993847)
    ·
      refine ⟨17447883620051162804990771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11631922413367441869993847 17447883620051162804990771)
      ·
        refine ⟨26171825430076744207486157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17447883620051162804990771 26171825430076744207486157)
        ·
          refine ⟨9814434536278779077807309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26171825430076744207486157 9814434536278779077807309)
          ·
            refine ⟨3680412951104542154177741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9814434536278779077807309 3680412951104542154177741)
            ·
              refine ⟨1380154856664203307816653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3680412951104542154177741 1380154856664203307816653)
              ·
                refine ⟨517558071249076240431245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380154856664203307816653 517558071249076240431245)
                ·
                  refine ⟨194084276718403590161717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517558071249076240431245 194084276718403590161717)
                  ·
                    rfl

theorem cell20_425225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_425225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425225 prefixEnd_425225 := by exact prefixLift 425225
  have htrace : WordTrace (prefixWord ++ tailWord_425225) baseStart_425225 baseEnd_425225 := by
    simpa [prefixWord, tailWord_425225, baseEnd_425225] using wordTrace_append hprefix tailTrace_425225
  have hstable : (prefixWord ++ tailWord_425225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425225).length < 2 ^ (prefixWord ++ tailWord_425225).sum := by decide
  have hdescent : baseEnd_425225 < baseStart_425225 := by decide
  rcases family_descends (prefixWord ++ tailWord_425225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425239 : List Nat := [1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_425239 : Nat := 118140960795 + 425239 * 2 ^ 59
def prefixEnd_425239 : Nat := 4983230072969 + 3 ^ 40 * 425239 * 2
def baseEnd_425239 : Nat := 64696888899960587898331

theorem tailTrace_425239 : CollatzResearch.WordTrace tailWord_425239 prefixEnd_425239 64696888899960587898331 := by
  unfold tailWord_425239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509740506439202884334771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10339827004292801922889847 15509740506439202884334771)
  ·
    refine ⟨23264610759658804326502157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509740506439202884334771 23264610759658804326502157)
    ·
      refine ⟨8724229034872051622438309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23264610759658804326502157 8724229034872051622438309)
      ·
        refine ⟨1635792944038509679207183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8724229034872051622438309 1635792944038509679207183)
        ·
          refine ⟨2453689416057764518810775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635792944038509679207183 2453689416057764518810775)
          ·
            refine ⟨3680534124086646778216163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453689416057764518810775 3680534124086646778216163)
            ·
              refine ⟨5520801186129970167324245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680534124086646778216163 5520801186129970167324245)
              ·
                refine ⟨64696888899960587898331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5520801186129970167324245 64696888899960587898331)
                ·
                  rfl

theorem cell20_425239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_425239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425239 prefixEnd_425239 := by exact prefixLift 425239
  have htrace : WordTrace (prefixWord ++ tailWord_425239) baseStart_425239 baseEnd_425239 := by
    simpa [prefixWord, tailWord_425239, baseEnd_425239] using wordTrace_append hprefix tailTrace_425239
  have hstable : (prefixWord ++ tailWord_425239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425239).length < 2 ^ (prefixWord ++ tailWord_425239).sum := by decide
  have hdescent : baseEnd_425239 < baseStart_425239 := by decide
  rcases family_descends (prefixWord ++ tailWord_425239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425249 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 2]
def baseStart_425249 : Nat := 118140960795 + 425249 * 2 ^ 59
def prefixEnd_425249 : Nat := 4983230072969 + 3 ^ 40 * 425249 * 2
def baseEnd_425249 : Nat := 194095230972366173361619

theorem tailTrace_425249 : CollatzResearch.WordTrace tailWord_425249 prefixEnd_425249 194095230972366173361619 := by
  unfold tailWord_425249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510105236402974592198801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10340070157601983061465867 15510105236402974592198801)
  ·
    refine ⟨11632578927302230944149101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15510105236402974592198801 11632578927302230944149101)
    ·
      refine ⟨4362217097738336604055913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11632578927302230944149101 4362217097738336604055913)
      ·
        refine ⟨3271662823303752453041935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362217097738336604055913 3271662823303752453041935)
        ·
          refine ⟨4907494234955628679562903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271662823303752453041935 4907494234955628679562903)
          ·
            refine ⟨7361241352433443019344355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907494234955628679562903 7361241352433443019344355)
            ·
              refine ⟨11041862028650164529016533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361241352433443019344355 11041862028650164529016533)
              ·
                refine ⟨258793641296488231148825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11041862028650164529016533 258793641296488231148825)
                ·
                  refine ⟨194095230972366173361619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258793641296488231148825 194095230972366173361619)
                  ·
                    rfl

theorem cell20_425249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_425249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425249 prefixEnd_425249 := by exact prefixLift 425249
  have htrace : WordTrace (prefixWord ++ tailWord_425249) baseStart_425249 baseEnd_425249 := by
    simpa [prefixWord, tailWord_425249, baseEnd_425249] using wordTrace_append hprefix tailTrace_425249
  have hstable : (prefixWord ++ tailWord_425249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425249).length < 2 ^ (prefixWord ++ tailWord_425249).sum := by decide
  have hdescent : baseEnd_425249 < baseStart_425249 := by decide
  rcases family_descends (prefixWord ++ tailWord_425249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425266 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_425266 : Nat := 118140960795 + 425266 * 2 ^ 59
def prefixEnd_425266 : Nat := 4983230072969 + 3 ^ 40 * 425266 * 2
def baseEnd_425266 : Nat := 194102990235589669794883

theorem tailTrace_425266 : CollatzResearch.WordTrace tailWord_425266 prefixEnd_425266 194102990235589669794883 := by
  unfold tailWord_425266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877681319335346623891913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10340483518227590997045101 3877681319335346623891913)
  ·
    refine ⟨2908260989501509967918935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3877681319335346623891913 2908260989501509967918935)
    ·
      refine ⟨4362391484252264951878403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908260989501509967918935 4362391484252264951878403)
      ·
        refine ⟨6543587226378397427817605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362391484252264951878403 6543587226378397427817605)
        ·
          refine ⟨1226922604945949517715801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6543587226378397427817605 1226922604945949517715801)
          ·
            refine ⟨920191953709462138286851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226922604945949517715801 920191953709462138286851)
            ·
              refine ⟨1380287930564193207430277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920191953709462138286851 1380287930564193207430277)
              ·
                refine ⟨258803986980786226393177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1380287930564193207430277 258803986980786226393177)
                ·
                  refine ⟨194102990235589669794883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258803986980786226393177 194102990235589669794883)
                  ·
                    rfl

theorem cell20_425266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_425266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425266 prefixEnd_425266 := by exact prefixLift 425266
  have htrace : WordTrace (prefixWord ++ tailWord_425266) baseStart_425266 baseEnd_425266 := by
    simpa [prefixWord, tailWord_425266, baseEnd_425266] using wordTrace_append hprefix tailTrace_425266
  have hstable : (prefixWord ++ tailWord_425266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425266).length < 2 ^ (prefixWord ++ tailWord_425266).sum := by decide
  have hdescent : baseEnd_425266 < baseStart_425266 := by decide
  rcases family_descends (prefixWord ++ tailWord_425266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425273 : List Nat := [1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_425273 : Nat := 118140960795 + 425273 * 2 ^ 59
def prefixEnd_425273 : Nat := 4983230072969 + 3 ^ 40 * 425273 * 2
def baseEnd_425273 : Nat := 64702061742109585520507

theorem tailTrace_425273 : CollatzResearch.WordTrace tailWord_425273 prefixEnd_425273 64702061742109585520507 := by
  unfold tailWord_425273
  simp only [CollatzResearch.WordTrace]
  refine ⟨15510980588316026691072473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10340653725544017794048315 15510980588316026691072473)
  ·
    refine ⟨11633235441237020018304355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15510980588316026691072473 11633235441237020018304355)
    ·
      refine ⟨17449853161855530027456533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11633235441237020018304355 17449853161855530027456533)
      ·
        refine ⟨817961866961977970037025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17449853161855530027456533 817961866961977970037025)
        ·
          refine ⟨613471400221483477527769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817961866961977970037025 613471400221483477527769)
          ·
            refine ⟨460103550166112608145827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613471400221483477527769 460103550166112608145827)
            ·
              refine ⟨690155325249168912218741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460103550166112608145827 690155325249168912218741)
              ·
                refine ⟨64702061742109585520507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690155325249168912218741 64702061742109585520507)
                ·
                  rfl

theorem cell20_425273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_425273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425273 prefixEnd_425273 := by exact prefixLift 425273
  have htrace : WordTrace (prefixWord ++ tailWord_425273) baseStart_425273 baseEnd_425273 := by
    simpa [prefixWord, tailWord_425273, baseEnd_425273] using wordTrace_append hprefix tailTrace_425273
  have hstable : (prefixWord ++ tailWord_425273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425273).length < 2 ^ (prefixWord ++ tailWord_425273).sum := by decide
  have hdescent : baseEnd_425273 < baseStart_425273 := by decide
  rcases family_descends (prefixWord ++ tailWord_425273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425294 : List Nat := [4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_425294 : Nat := 118140960795 + 425294 * 2 ^ 59
def prefixEnd_425294 : Nat := 4983230072969 + 3 ^ 40 * 425294 * 2
def baseEnd_425294 : Nat := 64705256732848672287145

theorem tailTrace_425294 : CollatzResearch.WordTrace tailWord_425294 prefixEnd_425294 64705256732848672287145 := by
  unfold tailWord_425294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938968315154993409698367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10341164347493298185057957 1938968315154993409698367)
  ·
    refine ⟨2908452472732490114547551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938968315154993409698367 2908452472732490114547551)
    ·
      refine ⟨4362678709098735171821327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908452472732490114547551 4362678709098735171821327)
      ·
        refine ⟨6544018063648102757731991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362678709098735171821327 6544018063648102757731991)
        ·
          refine ⟨9816027095472154136597987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544018063648102757731991 9816027095472154136597987)
          ·
            refine ⟨14724040643208231204896981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816027095472154136597987 14724040643208231204896981)
            ·
              refine ⟨345094702575192918864773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14724040643208231204896981 345094702575192918864773)
              ·
                refine ⟨64705256732848672287145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345094702575192918864773 64705256732848672287145)
                ·
                  rfl

theorem cell20_425294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_425294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425294 prefixEnd_425294 := by exact prefixLift 425294
  have htrace : WordTrace (prefixWord ++ tailWord_425294) baseStart_425294 baseEnd_425294 := by
    simpa [prefixWord, tailWord_425294, baseEnd_425294] using wordTrace_append hprefix tailTrace_425294
  have hstable : (prefixWord ++ tailWord_425294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425294).length < 2 ^ (prefixWord ++ tailWord_425294).sum := by decide
  have hdescent : baseEnd_425294 < baseStart_425294 := by decide
  rcases family_descends (prefixWord ++ tailWord_425294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425315 : List Nat := [1, 1, 1, 5, 2, 3, 7]
def baseStart_425315 : Nat := 118140960795 + 425315 * 2 ^ 59
def prefixEnd_425315 : Nat := 4983230072969 + 3 ^ 40 * 425315 * 2
def baseEnd_425315 : Nat := 21569483907862586351261

theorem tailTrace_425315 : CollatzResearch.WordTrace tailWord_425315 prefixEnd_425315 21569483907862586351261 := by
  unfold tailWord_425315
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512512454163867864101399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10341674969442578576067599 15512512454163867864101399)
  ·
    refine ⟨23268768681245801796152099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15512512454163867864101399 23268768681245801796152099)
    ·
      refine ⟨34903153021868702694228149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23268768681245801796152099 34903153021868702694228149)
      ·
        refine ⟨3272170595800190877583889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34903153021868702694228149 3272170595800190877583889)
        ·
          refine ⟨2454127946850143158187917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272170595800190877583889 2454127946850143158187917)
          ·
            refine ⟨920297980068803684320469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454127946850143158187917 920297980068803684320469)
            ·
              refine ⟨21569483907862586351261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 920297980068803684320469 21569483907862586351261)
              ·
                rfl

theorem cell20_425315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_425315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425315 prefixEnd_425315 := by exact prefixLift 425315
  have htrace : WordTrace (prefixWord ++ tailWord_425315) baseStart_425315 baseEnd_425315 := by
    simpa [prefixWord, tailWord_425315, baseEnd_425315] using wordTrace_append hprefix tailTrace_425315
  have hstable : (prefixWord ++ tailWord_425315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425315).length < 2 ^ (prefixWord ++ tailWord_425315).sum := by decide
  have hdescent : baseEnd_425315 < baseStart_425315 := by decide
  rcases family_descends (prefixWord ++ tailWord_425315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425325 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_425325 : Nat := 118140960795 + 425325 * 2 ^ 59
def prefixEnd_425325 : Nat := 4983230072969 + 3 ^ 40 * 425325 * 2
def baseEnd_425325 : Nat := 194129919443247686827975

theorem tailTrace_425325 : CollatzResearch.WordTrace tailWord_425325 prefixEnd_425325 194129919443247686827975 := by
  unfold tailWord_425325
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512877184127639571965429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10341918122751759714643619 15512877184127639571965429)
  ·
    refine ⟨1454332236011966209871759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15512877184127639571965429 1454332236011966209871759)
    ·
      refine ⟨2181498354017949314807639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454332236011966209871759 2181498354017949314807639)
      ·
        refine ⟨3272247531026923972211459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181498354017949314807639 3272247531026923972211459)
        ·
          refine ⟨4908371296540385958317189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272247531026923972211459 4908371296540385958317189)
          ·
            refine ⟨920319618101322367184473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4908371296540385958317189 920319618101322367184473)
            ·
              refine ⟨690239713575991775388355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920319618101322367184473 690239713575991775388355)
              ·
                refine ⟨1035359570363987663082533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690239713575991775388355 1035359570363987663082533)
                ·
                  refine ⟨194129919443247686827975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035359570363987663082533 194129919443247686827975)
                  ·
                    rfl

theorem cell20_425325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_425325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425325 prefixEnd_425325 := by exact prefixLift 425325
  have htrace : WordTrace (prefixWord ++ tailWord_425325) baseStart_425325 baseEnd_425325 := by
    simpa [prefixWord, tailWord_425325, baseEnd_425325] using wordTrace_append hprefix tailTrace_425325
  have hstable : (prefixWord ++ tailWord_425325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425325).length < 2 ^ (prefixWord ++ tailWord_425325).sum := by decide
  have hdescent : baseEnd_425325 < baseStart_425325 := by decide
  rcases family_descends (prefixWord ++ tailWord_425325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425439 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 2]
def baseStart_425439 : Nat := 118140960795 + 425439 * 2 ^ 59
def prefixEnd_425439 : Nat := 4983230072969 + 3 ^ 40 * 425439 * 2
def baseEnd_425439 : Nat := 194181952149569957027509

theorem tailTrace_425439 : CollatzResearch.WordTrace tailWord_425439 prefixEnd_425439 194181952149569957027509 := by
  unfold tailWord_425439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517035105714637041615371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10344690070476424694410247 15517035105714637041615371)
  ·
    refine ⟨23275552658571955562423057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517035105714637041615371 23275552658571955562423057)
    ·
      refine ⟨17456664493928966671817293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23275552658571955562423057 17456664493928966671817293)
      ·
        refine ⟨6546249185223362501931485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17456664493928966671817293 6546249185223362501931485)
        ·
          refine ⟨2454843444458760938224307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6546249185223362501931485 2454843444458760938224307)
          ·
            refine ⟨3682265166688141407336461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454843444458760938224307 3682265166688141407336461)
            ·
              refine ⟨1380849437508053027751173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3682265166688141407336461 1380849437508053027751173)
              ·
                refine ⟨258909269532759942703345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1380849437508053027751173 258909269532759942703345)
                ·
                  refine ⟨194181952149569957027509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258909269532759942703345 194181952149569957027509)
                  ·
                    rfl

theorem cell20_425439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2].length) (baseStart_425439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425439 prefixEnd_425439 := by exact prefixLift 425439
  have htrace : WordTrace (prefixWord ++ tailWord_425439) baseStart_425439 baseEnd_425439 := by
    simpa [prefixWord, tailWord_425439, baseEnd_425439] using wordTrace_append hprefix tailTrace_425439
  have hstable : (prefixWord ++ tailWord_425439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425439).length < 2 ^ (prefixWord ++ tailWord_425439).sum := by decide
  have hdescent : baseEnd_425439 < baseStart_425439 := by decide
  rcases family_descends (prefixWord ++ tailWord_425439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425481 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_425481 : Nat := 118140960795 + 425481 * 2 ^ 59
def prefixEnd_425481 : Nat := 4983230072969 + 3 ^ 40 * 425481 * 2
def baseEnd_425481 : Nat := 194201122094004477627337

theorem tailTrace_425481 : CollatzResearch.WordTrace tailWord_425481 prefixEnd_425481 194201122094004477627337 := by
  unfold tailWord_425481
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518566971562478214644297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10345711314374985476429531 15518566971562478214644297)
  ·
    refine ⟨11638925228671858660983223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15518566971562478214644297 11638925228671858660983223)
    ·
      refine ⟨17458387843007787991474835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11638925228671858660983223 17458387843007787991474835)
      ·
        refine ⟨26187581764511681987212253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17458387843007787991474835 26187581764511681987212253)
        ·
          refine ⟨9820343161691880745204595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26187581764511681987212253 9820343161691880745204595)
          ·
            refine ⟨14730514742537821117806893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820343161691880745204595 14730514742537821117806893)
            ·
              refine ⟨5523943028451682919177585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14730514742537821117806893 5523943028451682919177585)
              ·
                refine ⟨4142957271338762189383189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523943028451682919177585 4142957271338762189383189)
                ·
                  refine ⟨194201122094004477627337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4142957271338762189383189 194201122094004477627337)
                  ·
                    rfl

theorem cell20_425481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_425481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425481 prefixEnd_425481 := by exact prefixLift 425481
  have htrace : WordTrace (prefixWord ++ tailWord_425481) baseStart_425481 baseEnd_425481 := by
    simpa [prefixWord, tailWord_425481, baseEnd_425481] using wordTrace_append hprefix tailTrace_425481
  have hstable : (prefixWord ++ tailWord_425481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425481).length < 2 ^ (prefixWord ++ tailWord_425481).sum := by decide
  have hdescent : baseEnd_425481 < baseStart_425481 := by decide
  rcases family_descends (prefixWord ++ tailWord_425481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425491 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_425491 : Nat := 118140960795 + 425491 * 2 ^ 59
def prefixEnd_425491 : Nat := 4983230072969 + 3 ^ 40 * 425491 * 2
def baseEnd_425491 : Nat := 194205686366488887293963

theorem tailTrace_425491 : CollatzResearch.WordTrace tailWord_425491 prefixEnd_425491 194205686366488887293963 := by
  unfold tailWord_425491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518931701526249922508327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10345954467684166615005551 15518931701526249922508327)
  ·
    refine ⟨23278397552289374883762491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15518931701526249922508327 23278397552289374883762491)
    ·
      refine ⟨34917596328434062325643737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23278397552289374883762491 34917596328434062325643737)
      ·
        refine ⟨26188197246325546744232803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34917596328434062325643737 26188197246325546744232803)
        ·
          refine ⟨39282295869488320116349205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26188197246325546744232803 39282295869488320116349205)
          ·
            refine ⟨1841357618882265005453869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39282295869488320116349205 1841357618882265005453869)
            ·
              refine ⟨690509107080849377045201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1841357618882265005453869 690509107080849377045201)
              ·
                refine ⟨517881830310637032783901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690509107080849377045201 517881830310637032783901)
                ·
                  refine ⟨194205686366488887293963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517881830310637032783901 194205686366488887293963)
                  ·
                    rfl

theorem cell20_425491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_425491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425491 prefixEnd_425491 := by exact prefixLift 425491
  have htrace : WordTrace (prefixWord ++ tailWord_425491) baseStart_425491 baseEnd_425491 := by
    simpa [prefixWord, tailWord_425491, baseEnd_425491] using wordTrace_append hprefix tailTrace_425491
  have hstable : (prefixWord ++ tailWord_425491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425491).length < 2 ^ (prefixWord ++ tailWord_425491).sum := by decide
  have hdescent : baseEnd_425491 < baseStart_425491 := by decide
  rcases family_descends (prefixWord ++ tailWord_425491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425549 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 4]
def baseStart_425549 : Nat := 118140960795 + 425549 * 2 ^ 59
def prefixEnd_425549 : Nat := 4983230072969 + 3 ^ 40 * 425549 * 2
def baseEnd_425549 : Nat := 194232159146898463360393

theorem tailTrace_425549 : CollatzResearch.WordTrace tailWord_425549 prefixEnd_425549 194232159146898463360393 := by
  unfold tailWord_425549
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521047135316125828119701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10347364756877417218746467 15521047135316125828119701)
  ·
    refine ⟨727549084467943398193111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15521047135316125828119701 727549084467943398193111)
    ·
      refine ⟨1091323626701915097289667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727549084467943398193111 1091323626701915097289667)
      ·
        refine ⟨1636985440052872645934501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091323626701915097289667 1636985440052872645934501)
        ·
          refine ⟨306934770009913621112719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1636985440052872645934501 306934770009913621112719)
          ·
            refine ⟨460402155014870431669079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306934770009913621112719 460402155014870431669079)
            ·
              refine ⟨690603232522305647503619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460402155014870431669079 690603232522305647503619)
              ·
                refine ⟨1035904848783458471255429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690603232522305647503619 1035904848783458471255429)
                ·
                  refine ⟨194232159146898463360393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035904848783458471255429 194232159146898463360393)
                  ·
                    rfl

theorem cell20_425549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_425549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425549 prefixEnd_425549 := by exact prefixLift 425549
  have htrace : WordTrace (prefixWord ++ tailWord_425549) baseStart_425549 baseEnd_425549 := by
    simpa [prefixWord, tailWord_425549, baseEnd_425549] using wordTrace_append hprefix tailTrace_425549
  have hstable : (prefixWord ++ tailWord_425549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425549).length < 2 ^ (prefixWord ++ tailWord_425549).sum := by decide
  have hdescent : baseEnd_425549 < baseStart_425549 := by decide
  rcases family_descends (prefixWord ++ tailWord_425549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425604 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_425604 : Nat := 118140960795 + 425604 * 2 ^ 59
def prefixEnd_425604 : Nat := 4983230072969 + 3 ^ 40 * 425604 * 2
def baseEnd_425604 : Nat := 194257262645562716526835

theorem tailTrace_425604 : CollatzResearch.WordTrace tailWord_425604 prefixEnd_425604 194257262645562716526835 := by
  unfold tailWord_425604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761526575058435110685933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10348702100077913480914577 7761526575058435110685933)
  ·
    refine ⟨2910572465646913166507225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7761526575058435110685933 2910572465646913166507225)
    ·
      refine ⟨2182929349235184874880419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2910572465646913166507225 2182929349235184874880419)
      ·
        refine ⟨3274394023852777312320629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182929349235184874880419 3274394023852777312320629)
        ·
          refine ⟨306974439736197873030059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3274394023852777312320629 306974439736197873030059)
          ·
            refine ⟨460461659604296809545089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306974439736197873030059 460461659604296809545089)
            ·
              refine ⟨345346244703222607158817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460461659604296809545089 345346244703222607158817)
              ·
                refine ⟨259009683527416955369113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345346244703222607158817 259009683527416955369113)
                ·
                  refine ⟨194257262645562716526835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259009683527416955369113 194257262645562716526835)
                  ·
                    rfl

theorem cell20_425604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_425604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425604 prefixEnd_425604 := by exact prefixLift 425604
  have htrace : WordTrace (prefixWord ++ tailWord_425604) baseStart_425604 baseEnd_425604 := by
    simpa [prefixWord, tailWord_425604, baseEnd_425604] using wordTrace_append hprefix tailTrace_425604
  have hstable : (prefixWord ++ tailWord_425604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425604).length < 2 ^ (prefixWord ++ tailWord_425604).sum := by decide
  have hdescent : baseEnd_425604 < baseStart_425604 := by decide
  rcases family_descends (prefixWord ++ tailWord_425604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425605 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_425605 : Nat := 118140960795 + 425605 * 2 ^ 59
def prefixEnd_425605 : Nat := 4983230072969 + 3 ^ 40 * 425605 * 2
def baseEnd_425605 : Nat := 194257719072811157493497

theorem tailTrace_425605 : CollatzResearch.WordTrace tailWord_425605 prefixEnd_425605 194257719072811157493497 := by
  unfold tailWord_425605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523089623113247392158269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348726415408831594772179 15523089623113247392158269)
  ·
    refine ⟨5821158608667467772059351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15523089623113247392158269 5821158608667467772059351)
    ·
      refine ⟨8731737913001201658089027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821158608667467772059351 8731737913001201658089027)
      ·
        refine ⟨13097606869501802487133541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8731737913001201658089027 13097606869501802487133541)
        ·
          refine ⟨2455801288031587966337539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13097606869501802487133541 2455801288031587966337539)
          ·
            refine ⟨3683701932047381949506309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455801288031587966337539 3683701932047381949506309)
            ·
              refine ⟨690694112258884115532433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3683701932047381949506309 690694112258884115532433)
              ·
                refine ⟨518020584194163086649325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690694112258884115532433 518020584194163086649325)
                ·
                  refine ⟨194257719072811157493497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518020584194163086649325 194257719072811157493497)
                  ·
                    rfl

theorem cell20_425605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_425605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425605 prefixEnd_425605 := by exact prefixLift 425605
  have htrace : WordTrace (prefixWord ++ tailWord_425605) baseStart_425605 baseEnd_425605 := by
    simpa [prefixWord, tailWord_425605, baseEnd_425605] using wordTrace_append hprefix tailTrace_425605
  have hstable : (prefixWord ++ tailWord_425605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425605).length < 2 ^ (prefixWord ++ tailWord_425605).sum := by decide
  have hdescent : baseEnd_425605 < baseStart_425605 := by decide
  rcases family_descends (prefixWord ++ tailWord_425605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425636 : List Nat := [2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_425636 : Nat := 118140960795 + 425636 * 2 ^ 59
def prefixEnd_425636 : Nat := 4983230072969 + 3 ^ 40 * 425636 * 2
def baseEnd_425636 : Nat := 64757289439170942486679

theorem tailTrace_425636 : CollatzResearch.WordTrace tailWord_425636 prefixEnd_425636 64757289439170942486679 := by
  unfold tailWord_425636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762110143000469843268381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10349480190667293124357841 7762110143000469843268381)
  ·
    refine ⟨2910791303625176191225643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7762110143000469843268381 2910791303625176191225643)
    ·
      refine ⟨4366186955437764286838465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910791303625176191225643 4366186955437764286838465)
      ·
        refine ⟨3274640216578323215128849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4366186955437764286838465 3274640216578323215128849)
        ·
          refine ⟨2455980162433742411346637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3274640216578323215128849 2455980162433742411346637)
          ·
            refine ⟨920992560912653404254989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2455980162433742411346637 920992560912653404254989)
            ·
              refine ⟨345372210342245026595621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 920992560912653404254989 345372210342245026595621)
              ·
                refine ⟨64757289439170942486679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345372210342245026595621 64757289439170942486679)
                ·
                  rfl

theorem cell20_425636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_425636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425636 prefixEnd_425636 := by exact prefixLift 425636
  have htrace : WordTrace (prefixWord ++ tailWord_425636) baseStart_425636 baseEnd_425636 := by
    simpa [prefixWord, tailWord_425636, baseEnd_425636] using wordTrace_append hprefix tailTrace_425636
  have hstable : (prefixWord ++ tailWord_425636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425636).length < 2 ^ (prefixWord ++ tailWord_425636).sum := by decide
  have hdescent : baseEnd_425636 < baseStart_425636 := by decide
  rcases family_descends (prefixWord ++ tailWord_425636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425660 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_425660 : Nat := 118140960795 + 425660 * 2 ^ 59
def prefixEnd_425660 : Nat := 4983230072969 + 3 ^ 40 * 425660 * 2
def baseEnd_425660 : Nat := 194282822571475410659939

theorem tailTrace_425660 : CollatzResearch.WordTrace tailWord_425660 prefixEnd_425660 194282822571475410659939 := by
  unfold tailWord_425660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762547818956995892705217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10350063758609327856940289 7762547818956995892705217)
  ·
    refine ⟨5821910864217746919528913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7762547818956995892705217 5821910864217746919528913)
    ·
      refine ⟨4366433148163310189646685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5821910864217746919528913 4366433148163310189646685)
      ·
        refine ⟨1637412430561241321117507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4366433148163310189646685 1637412430561241321117507)
        ·
          refine ⟨2456118645841861981676261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637412430561241321117507 2456118645841861981676261)
          ·
            refine ⟨460522246095349121564299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2456118645841861981676261 460522246095349121564299)
            ·
              refine ⟨690783369143023682346449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460522246095349121564299 690783369143023682346449)
              ·
                refine ⟨518087526857267761759837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690783369143023682346449 518087526857267761759837)
                ·
                  refine ⟨194282822571475410659939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518087526857267761759837 194282822571475410659939)
                  ·
                    rfl

theorem cell20_425660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_425660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425660 prefixEnd_425660 := by exact prefixLift 425660
  have htrace : WordTrace (prefixWord ++ tailWord_425660) baseStart_425660 baseEnd_425660 := by
    simpa [prefixWord, tailWord_425660, baseEnd_425660] using wordTrace_append hprefix tailTrace_425660
  have hstable : (prefixWord ++ tailWord_425660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425660).length < 2 ^ (prefixWord ++ tailWord_425660).sum := by decide
  have hdescent : baseEnd_425660 < baseStart_425660 := by decide
  rcases family_descends (prefixWord ++ tailWord_425660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425664 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_425664 : Nat := 118140960795 + 425664 * 2 ^ 59
def prefixEnd_425664 : Nat := 4983230072969 + 3 ^ 40 * 425664 * 2
def baseEnd_425664 : Nat := 194284648280469174526589

theorem tailTrace_425664 : CollatzResearch.WordTrace tailWord_425664 prefixEnd_425664 194284648280469174526589 := by
  unfold tailWord_425664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762620764949750234278023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10350161019933000312370697 7762620764949750234278023)
  ·
    refine ⟨11643931147424625351417035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762620764949750234278023 11643931147424625351417035)
    ·
      refine ⟨17465896721136938027125553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11643931147424625351417035 17465896721136938027125553)
      ·
        refine ⟨13099422540852703520344165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17465896721136938027125553 13099422540852703520344165)
        ·
          refine ⟨2456141726409881910064531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13099422540852703520344165 2456141726409881910064531)
          ·
            refine ⟨3684212589614822865096797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456141726409881910064531 3684212589614822865096797)
            ·
              refine ⟨1381579721105558574411299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3684212589614822865096797 1381579721105558574411299)
              ·
                refine ⟨2072369581658337861616949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381579721105558574411299 2072369581658337861616949)
                ·
                  refine ⟨194284648280469174526589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072369581658337861616949 194284648280469174526589)
                  ·
                    rfl

theorem cell20_425664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_425664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425664 prefixEnd_425664 := by exact prefixLift 425664
  have htrace : WordTrace (prefixWord ++ tailWord_425664) baseStart_425664 baseEnd_425664 := by
    simpa [prefixWord, tailWord_425664, baseEnd_425664] using wordTrace_append hprefix tailTrace_425664
  have hstable : (prefixWord ++ tailWord_425664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425664).length < 2 ^ (prefixWord ++ tailWord_425664).sum := by decide
  have hdescent : baseEnd_425664 < baseStart_425664 := by decide
  rcases family_descends (prefixWord ++ tailWord_425664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425798 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_425798 : Nat := 118140960795 + 425798 * 2 ^ 59
def prefixEnd_425798 : Nat := 4983230072969 + 3 ^ 40 * 425798 * 2
def baseEnd_425798 : Nat := 194345809531760264059375

theorem tailTrace_425798 : CollatzResearch.WordTrace tailWord_425798 prefixEnd_425798 194345809531760264059375 := by
  unfold tailWord_425798
  simp only [CollatzResearch.WordTrace]
  refine ⟨485316528481688792310439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10353419274276027569289365 485316528481688792310439)
  ·
    refine ⟨727974792722533188465659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 485316528481688792310439 727974792722533188465659)
    ·
      refine ⟨1091962189083799782698489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727974792722533188465659 1091962189083799782698489)
      ·
        refine ⟨818971641812849837023867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091962189083799782698489 818971641812849837023867)
        ·
          refine ⟨1228457462719274755535801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818971641812849837023867 1228457462719274755535801)
          ·
            refine ⟨921343097039456066651851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1228457462719274755535801 921343097039456066651851)
            ·
              refine ⟨1382014645559184099977777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921343097039456066651851 1382014645559184099977777)
              ·
                refine ⟨1036510984169388074983333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382014645559184099977777 1036510984169388074983333)
                ·
                  refine ⟨194345809531760264059375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036510984169388074983333 194345809531760264059375)
                  ·
                    rfl

theorem cell20_425798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_425798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425798 prefixEnd_425798 := by exact prefixLift 425798
  have htrace : WordTrace (prefixWord ++ tailWord_425798) baseStart_425798 baseEnd_425798 := by
    simpa [prefixWord, tailWord_425798, baseEnd_425798] using wordTrace_append hprefix tailTrace_425798
  have hstable : (prefixWord ++ tailWord_425798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425798).length < 2 ^ (prefixWord ++ tailWord_425798).sum := by decide
  have hdescent : baseEnd_425798 < baseStart_425798 := by decide
  rcases family_descends (prefixWord ++ tailWord_425798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425805 : List Nat := [1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_425805 : Nat := 118140960795 + 425805 * 2 ^ 59
def prefixEnd_425805 : Nat := 4983230072969 + 3 ^ 40 * 425805 * 2
def baseEnd_425805 : Nat := 64783001507499783608671

theorem tailTrace_425805 : CollatzResearch.WordTrace tailWord_425805 prefixEnd_425805 64783001507499783608671 := by
  unfold tailWord_425805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530384222388681549438869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10353589481592454366292579 15530384222388681549438869)
  ·
    refine ⟨727986760424469447629947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15530384222388681549438869 727986760424469447629947)
    ·
      refine ⟨1091980140636704171444921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727986760424469447629947 1091980140636704171444921)
      ·
        refine ⟨818985105477528128583691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091980140636704171444921 818985105477528128583691)
        ·
          refine ⟨1228477658216292192875537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818985105477528128583691 1228477658216292192875537)
          ·
            refine ⟨921358243662219144656653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1228477658216292192875537 921358243662219144656653)
            ·
              refine ⟨345509341373332179246245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 921358243662219144656653 345509341373332179246245)
              ·
                refine ⟨64783001507499783608671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345509341373332179246245 64783001507499783608671)
                ·
                  rfl

theorem cell20_425805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_425805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425805 prefixEnd_425805 := by exact prefixLift 425805
  have htrace : WordTrace (prefixWord ++ tailWord_425805) baseStart_425805 baseEnd_425805 := by
    simpa [prefixWord, tailWord_425805, baseEnd_425805] using wordTrace_append hprefix tailTrace_425805
  have hstable : (prefixWord ++ tailWord_425805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425805).length < 2 ^ (prefixWord ++ tailWord_425805).sum := by decide
  have hdescent : baseEnd_425805 < baseStart_425805 := by decide
  rcases family_descends (prefixWord ++ tailWord_425805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425861 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_425861 : Nat := 118140960795 + 425861 * 2 ^ 59
def prefixEnd_425861 : Nat := 4983230072969 + 3 ^ 40 * 425861 * 2
def baseEnd_425861 : Nat := 194374564448412044959117

theorem tailTrace_425861 : CollatzResearch.WordTrace tailWord_425861 prefixEnd_425861 194374564448412044959117 := by
  unfold tailWord_425861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532426710185803113477437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10354951140123868742318291 15532426710185803113477437)
  ·
    refine ⟨5824660016319676167554039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15532426710185803113477437 5824660016319676167554039)
    ·
      refine ⟨8736990024479514251331059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5824660016319676167554039 8736990024479514251331059)
      ·
        refine ⟨13105485036719271376996589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8736990024479514251331059 13105485036719271376996589)
        ·
          refine ⟨4914556888769726766373721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13105485036719271376996589 4914556888769726766373721)
          ·
            refine ⟨3685917666577295074780291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4914556888769726766373721 3685917666577295074780291)
            ·
              refine ⟨5528876499865942612170437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685917666577295074780291 5528876499865942612170437)
              ·
                refine ⟨1036664343724864239781957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5528876499865942612170437 1036664343724864239781957)
                ·
                  refine ⟨194374564448412044959117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036664343724864239781957 194374564448412044959117)
                  ·
                    rfl

theorem cell20_425861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_425861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425861 prefixEnd_425861 := by exact prefixLift 425861
  have htrace : WordTrace (prefixWord ++ tailWord_425861) baseStart_425861 baseEnd_425861 := by
    simpa [prefixWord, tailWord_425861, baseEnd_425861] using wordTrace_append hprefix tailTrace_425861
  have hstable : (prefixWord ++ tailWord_425861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425861).length < 2 ^ (prefixWord ++ tailWord_425861).sum := by decide
  have hdescent : baseEnd_425861 < baseStart_425861 := by decide
  rcases family_descends (prefixWord ++ tailWord_425861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425870 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_425870 : Nat := 118140960795 + 425870 * 2 ^ 59
def prefixEnd_425870 : Nat := 4983230072969 + 3 ^ 40 * 425870 * 2
def baseEnd_425870 : Nat := 194378672293648013659081

theorem tailTrace_425870 : CollatzResearch.WordTrace tailWord_425870 prefixEnd_425870 194378672293648013659081 := by
  unfold tailWord_425870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941594370894149706319383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10355169978102131767036709 1941594370894149706319383)
  ·
    refine ⟨2912391556341224559479075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941594370894149706319383 2912391556341224559479075)
    ·
      refine ⟨4368587334511836839218613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912391556341224559479075 4368587334511836839218613)
      ·
        refine ⟨409555062610484703676745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4368587334511836839218613 409555062610484703676745)
        ·
          refine ⟨307166296957863527757559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409555062610484703676745 307166296957863527757559)
          ·
            refine ⟨460749445436795291636339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307166296957863527757559 460749445436795291636339)
            ·
              refine ⟨691124168155192937454509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460749445436795291636339 691124168155192937454509)
              ·
                refine ⟨259171563058197351545441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691124168155192937454509 259171563058197351545441)
                ·
                  refine ⟨194378672293648013659081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259171563058197351545441 194378672293648013659081)
                  ·
                    rfl

theorem cell20_425870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_425870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425870 prefixEnd_425870 := by exact prefixLift 425870
  have htrace : WordTrace (prefixWord ++ tailWord_425870) baseStart_425870 baseEnd_425870 := by
    simpa [prefixWord, tailWord_425870, baseEnd_425870] using wordTrace_append hprefix tailTrace_425870
  have hstable : (prefixWord ++ tailWord_425870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425870).length < 2 ^ (prefixWord ++ tailWord_425870).sum := by decide
  have hdescent : baseEnd_425870 < baseStart_425870 := by decide
  rcases family_descends (prefixWord ++ tailWord_425870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425874 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_425874 : Nat := 118140960795 + 425874 * 2 ^ 59
def prefixEnd_425874 : Nat := 4983230072969 + 3 ^ 40 * 425874 * 2
def baseEnd_425874 : Nat := 194380498002641777525731

theorem tailTrace_425874 : CollatzResearch.WordTrace tailWord_425874 prefixEnd_425874 194380498002641777525731 := by
  unfold tailWord_425874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3883225214784676583425169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10355267239425804222467117 3883225214784676583425169)
  ·
    refine ⟨2912418911088507437568877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3883225214784676583425169 2912418911088507437568877)
    ·
      refine ⟨1092157091658190289088329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2912418911088507437568877 1092157091658190289088329)
      ·
        refine ⟨819117818743642716816247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1092157091658190289088329 819117818743642716816247)
        ·
          refine ⟨1228676728115464075224371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819117818743642716816247 1228676728115464075224371)
          ·
            refine ⟨1843015092173196112836557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228676728115464075224371 1843015092173196112836557)
            ·
              refine ⟨691130659564948542313709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1843015092173196112836557 691130659564948542313709)
              ·
                refine ⟨259173997336855703367641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691130659564948542313709 259173997336855703367641)
                ·
                  refine ⟨194380498002641777525731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259173997336855703367641 194380498002641777525731)
                  ·
                    rfl

theorem cell20_425874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_425874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425874 prefixEnd_425874 := by exact prefixLift 425874
  have htrace : WordTrace (prefixWord ++ tailWord_425874) baseStart_425874 baseEnd_425874 := by
    simpa [prefixWord, tailWord_425874, baseEnd_425874] using wordTrace_append hprefix tailTrace_425874
  have hstable : (prefixWord ++ tailWord_425874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425874).length < 2 ^ (prefixWord ++ tailWord_425874).sum := by decide
  have hdescent : baseEnd_425874 < baseStart_425874 := by decide
  rcases family_descends (prefixWord ++ tailWord_425874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425885 : List Nat := [1, 4, 2, 1, 2, 4, 6]
def baseStart_425885 : Nat := 118140960795 + 425885 * 2 ^ 59
def prefixEnd_425885 : Nat := 4983230072969 + 3 ^ 40 * 425885 * 2
def baseEnd_425885 : Nat := 21598390966930514239891

theorem tailTrace_425885 : CollatzResearch.WordTrace tailWord_425885 prefixEnd_425885 21598390966930514239891 := by
  unfold tailWord_425885
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533302062098855212351109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10355534708065903474900739 15533302062098855212351109)
  ·
    refine ⟨2912494136643535352315833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15533302062098855212351109 2912494136643535352315833)
    ·
      refine ⟨2184370602482651514236875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2912494136643535352315833 2184370602482651514236875)
      ·
        refine ⟨3276555903723977271355313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184370602482651514236875 3276555903723977271355313)
        ·
          refine ⟨2457416927792982953516485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3276555903723977271355313 2457416927792982953516485)
          ·
            refine ⟨460765673961184303784341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2457416927792982953516485 460765673961184303784341)
            ·
              refine ⟨21598390966930514239891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 460765673961184303784341 21598390966930514239891)
              ·
                rfl

theorem cell20_425885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_425885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425885 prefixEnd_425885 := by exact prefixLift 425885
  have htrace : WordTrace (prefixWord ++ tailWord_425885) baseStart_425885 baseEnd_425885 := by
    simpa [prefixWord, tailWord_425885, baseEnd_425885] using wordTrace_append hprefix tailTrace_425885
  have hstable : (prefixWord ++ tailWord_425885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425885).length < 2 ^ (prefixWord ++ tailWord_425885).sum := by decide
  have hdescent : baseEnd_425885 < baseStart_425885 := by decide
  rcases family_descends (prefixWord ++ tailWord_425885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425892 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_425892 : Nat := 118140960795 + 425892 * 2 ^ 59
def prefixEnd_425892 : Nat := 4983230072969 + 3 ^ 40 * 425892 * 2
def baseEnd_425892 : Nat := 194388713693113714925657

theorem tailTrace_425892 : CollatzResearch.WordTrace tailWord_425892 prefixEnd_425892 194388713693113714925657 := by
  unfold tailWord_425892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766778686536747703927965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10355704915382330271903953 7766778686536747703927965)
  ·
    refine ⟨2912542007451280388972987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7766778686536747703927965 2912542007451280388972987)
    ·
      refine ⟨4368813011176920583459481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912542007451280388972987 4368813011176920583459481)
      ·
        refine ⟨3276609758382690437594611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368813011176920583459481 3276609758382690437594611)
        ·
          refine ⟨4914914637574035656391917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276609758382690437594611 4914914637574035656391917)
          ·
            refine ⟨1843092989090263371146969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4914914637574035656391917 1843092989090263371146969)
            ·
              refine ⟨1382319741817697528360227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843092989090263371146969 1382319741817697528360227)
              ·
                refine ⟨2073479612726546292540341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382319741817697528360227 2073479612726546292540341)
                ·
                  refine ⟨194388713693113714925657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2073479612726546292540341 194388713693113714925657)
                  ·
                    rfl

theorem cell20_425892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_425892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425892 prefixEnd_425892 := by exact prefixLift 425892
  have htrace : WordTrace (prefixWord ++ tailWord_425892) baseStart_425892 baseEnd_425892 := by
    simpa [prefixWord, tailWord_425892, baseEnd_425892] using wordTrace_append hprefix tailTrace_425892
  have hstable : (prefixWord ++ tailWord_425892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425892).length < 2 ^ (prefixWord ++ tailWord_425892).sum := by decide
  have hdescent : baseEnd_425892 < baseStart_425892 := by decide
  rcases family_descends (prefixWord ++ tailWord_425892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425895 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_425895 : Nat := 118140960795 + 425895 * 2 ^ 59
def prefixEnd_425895 : Nat := 4983230072969 + 3 ^ 40 * 425895 * 2
def baseEnd_425895 : Nat := 194390082974859037825645

theorem tailTrace_425895 : CollatzResearch.WordTrace tailWord_425895 prefixEnd_425895 194390082974859037825645 := by
  unfold tailWord_425895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533666792062626920215139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10355777861375084613476759 15533666792062626920215139)
  ·
    refine ⟨23300500188093940380322709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15533666792062626920215139 23300500188093940380322709)
    ·
      refine ⟨1092210946316903455327627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23300500188093940380322709 1092210946316903455327627)
      ·
        refine ⟨1638316419475355182991441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092210946316903455327627 1638316419475355182991441)
        ·
          refine ⟨1228737314606516387243581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638316419475355182991441 1228737314606516387243581)
          ·
            refine ⟨460776492977443645216343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1228737314606516387243581 460776492977443645216343)
            ·
              refine ⟨691164739466165467824515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460776492977443645216343 691164739466165467824515)
              ·
                refine ⟨1036747109199248201736773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691164739466165467824515 1036747109199248201736773)
                ·
                  refine ⟨194390082974859037825645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036747109199248201736773 194390082974859037825645)
                  ·
                    rfl

theorem cell20_425895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_425895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425895 prefixEnd_425895 := by exact prefixLift 425895
  have htrace : WordTrace (prefixWord ++ tailWord_425895) baseStart_425895 baseEnd_425895 := by
    simpa [prefixWord, tailWord_425895, baseEnd_425895] using wordTrace_append hprefix tailTrace_425895
  have hstable : (prefixWord ++ tailWord_425895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425895).length < 2 ^ (prefixWord ++ tailWord_425895).sum := by decide
  have hdescent : baseEnd_425895 < baseStart_425895 := by decide
  rcases family_descends (prefixWord ++ tailWord_425895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425909 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_425909 : Nat := 118140960795 + 425909 * 2 ^ 59
def prefixEnd_425909 : Nat := 4983230072969 + 3 ^ 40 * 425909 * 2
def baseEnd_425909 : Nat := 194396472956337211358921

theorem tailTrace_425909 : CollatzResearch.WordTrace tailWord_425909 prefixEnd_425909 194396472956337211358921 := by
  unfold tailWord_425909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15534177414011907311224781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10356118276007938207483187 15534177414011907311224781)
  ·
    refine ⟨5825316530254465241709293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15534177414011907311224781 5825316530254465241709293)
    ·
      refine ⟨2184493698845424465640985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5825316530254465241709293 2184493698845424465640985)
      ·
        refine ⟨1638370274134068349230739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2184493698845424465640985 1638370274134068349230739)
        ·
          refine ⟨2457555411201102523846109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638370274134068349230739 2457555411201102523846109)
          ·
            refine ⟨921583279200413446442291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2457555411201102523846109 921583279200413446442291)
            ·
              refine ⟨1382374918800620169663437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921583279200413446442291 1382374918800620169663437)
              ·
                refine ⟨518390594550232563623789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1382374918800620169663437 518390594550232563623789)
                ·
                  refine ⟨194396472956337211358921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518390594550232563623789 194396472956337211358921)
                  ·
                    rfl

theorem cell20_425909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_425909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425909 prefixEnd_425909 := by exact prefixLift 425909
  have htrace : WordTrace (prefixWord ++ tailWord_425909) baseStart_425909 baseEnd_425909 := by
    simpa [prefixWord, tailWord_425909, baseEnd_425909] using wordTrace_append hprefix tailTrace_425909
  have hstable : (prefixWord ++ tailWord_425909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425909).length < 2 ^ (prefixWord ++ tailWord_425909).sum := by decide
  have hdescent : baseEnd_425909 < baseStart_425909 := by decide
  rcases family_descends (prefixWord ++ tailWord_425909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425968 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_425968 : Nat := 118140960795 + 425968 * 2 ^ 59
def prefixEnd_425968 : Nat := 4983230072969 + 3 ^ 40 * 425968 * 2
def baseEnd_425968 : Nat := 194423402163995228392013

theorem tailTrace_425968 : CollatzResearch.WordTrace tailWord_425968 prefixEnd_425968 194423402163995228392013 := by
  unfold tailWord_425968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768164660399080193811279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10357552880532106925081705 7768164660399080193811279)
  ·
    refine ⟨11652246990598620290716919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7768164660399080193811279 11652246990598620290716919)
    ·
      refine ⟨17478370485897930436075379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11652246990598620290716919 17478370485897930436075379)
      ·
        refine ⟨26217555728846895654113069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478370485897930436075379 26217555728846895654113069)
        ·
          refine ⟨9831583398317585870292401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26217555728846895654113069 9831583398317585870292401)
          ·
            refine ⟨7373687548738189402719301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9831583398317585870292401 7373687548738189402719301)
            ·
              refine ⟨1382566415388410513009869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7373687548738189402719301 1382566415388410513009869)
              ·
                refine ⟨518462405770653942378701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1382566415388410513009869 518462405770653942378701)
                ·
                  refine ⟨194423402163995228392013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518462405770653942378701 194423402163995228392013)
                  ·
                    rfl

theorem cell20_425968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_425968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_425968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_425968 prefixEnd_425968 := by exact prefixLift 425968
  have htrace : WordTrace (prefixWord ++ tailWord_425968) baseStart_425968 baseEnd_425968 := by
    simpa [prefixWord, tailWord_425968, baseEnd_425968] using wordTrace_append hprefix tailTrace_425968
  have hstable : (prefixWord ++ tailWord_425968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425968).length < 2 ^ (prefixWord ++ tailWord_425968).sum := by decide
  have hdescent : baseEnd_425968 < baseStart_425968 := by decide
  rcases family_descends (prefixWord ++ tailWord_425968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426030 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_426030 : Nat := 118140960795 + 426030 * 2 ^ 59
def prefixEnd_426030 : Nat := 4983230072969 + 3 ^ 40 * 426030 * 2
def baseEnd_426030 : Nat := 194451700653398568325093

theorem tailTrace_426030 : CollatzResearch.WordTrace tailWord_426030 prefixEnd_426030 194451700653398568325093 := by
  unfold tailWord_426030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942323830821693122047443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10359060431049029984253029 1942323830821693122047443)
  ·
    refine ⟨2913485746232539683071165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942323830821693122047443 2913485746232539683071165)
    ·
      refine ⟨1092557154837202381151687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2913485746232539683071165 1092557154837202381151687)
      ·
        refine ⟨1638835732255803571727531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092557154837202381151687 1638835732255803571727531)
        ·
          refine ⟨2458253598383705357591297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638835732255803571727531 2458253598383705357591297)
          ·
            refine ⟨1843690198787779018193473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458253598383705357591297 1843690198787779018193473)
            ·
              refine ⟨1382767649090834263645105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843690198787779018193473 1382767649090834263645105)
              ·
                refine ⟨1037075736818125697733829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382767649090834263645105 1037075736818125697733829)
                ·
                  refine ⟨194451700653398568325093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037075736818125697733829 194451700653398568325093)
                  ·
                    rfl

theorem cell20_426030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_426030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426030 prefixEnd_426030 := by exact prefixLift 426030
  have htrace : WordTrace (prefixWord ++ tailWord_426030) baseStart_426030 baseEnd_426030 := by
    simpa [prefixWord, tailWord_426030, baseEnd_426030] using wordTrace_append hprefix tailTrace_426030
  have hstable : (prefixWord ++ tailWord_426030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426030).length < 2 ^ (prefixWord ++ tailWord_426030).sum := by decide
  have hdescent : baseEnd_426030 < baseStart_426030 := by decide
  rcases family_descends (prefixWord ++ tailWord_426030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426037 : List Nat := [1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_426037 : Nat := 118140960795 + 426037 * 2 ^ 59
def prefixEnd_426037 : Nat := 4983230072969 + 3 ^ 40 * 426037 * 2
def baseEnd_426037 : Nat := 64818298548045885030577

theorem tailTrace_426037 : CollatzResearch.WordTrace tailWord_426037 prefixEnd_426037 64818298548045885030577 := by
  unfold tailWord_426037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538845957548185171884365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10359230638365456781256243 15538845957548185171884365)
  ·
    refine ⟨5827067234080569439456637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15538845957548185171884365 5827067234080569439456637)
    ·
      refine ⟨2185150212780213539796239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5827067234080569439456637 2185150212780213539796239)
      ·
        refine ⟨3277725319170320309694359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185150212780213539796239 3277725319170320309694359)
        ·
          refine ⟨4916587978755480464541539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277725319170320309694359 4916587978755480464541539)
          ·
            refine ⟨7374881968133220696812309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916587978755480464541539 7374881968133220696812309)
            ·
              refine ⟨345697592256244720163077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7374881968133220696812309 345697592256244720163077)
              ·
                refine ⟨64818298548045885030577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345697592256244720163077 64818298548045885030577)
                ·
                  rfl

theorem cell20_426037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_426037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426037 prefixEnd_426037 := by exact prefixLift 426037
  have htrace : WordTrace (prefixWord ++ tailWord_426037) baseStart_426037 baseEnd_426037 := by
    simpa [prefixWord, tailWord_426037, baseEnd_426037] using wordTrace_append hprefix tailTrace_426037
  have hstable : (prefixWord ++ tailWord_426037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426037).length < 2 ^ (prefixWord ++ tailWord_426037).sum := by decide
  have hdescent : baseEnd_426037 < baseStart_426037 := by decide
  rcases family_descends (prefixWord ++ tailWord_426037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426061 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_426061 : Nat := 118140960795 + 426061 * 2 ^ 59
def prefixEnd_426061 : Nat := 4983230072969 + 3 ^ 40 * 426061 * 2
def baseEnd_426061 : Nat := 194465849898100238291633

theorem tailTrace_426061 : CollatzResearch.WordTrace tailWord_426061 prefixEnd_426061 194465849898100238291633 := by
  unfold tailWord_426061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15539721309461237270758037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10359814206307491513838691 15539721309461237270758037)
  ·
    refine ⟨728424436380995497066783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15539721309461237270758037 728424436380995497066783)
    ·
      refine ⟨1092636654571493245600175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728424436380995497066783 1092636654571493245600175)
      ·
        refine ⟨1638954981857239868400263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092636654571493245600175 1638954981857239868400263)
        ·
          refine ⟨2458432472785859802600395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638954981857239868400263 2458432472785859802600395)
          ·
            refine ⟨3687648709178789703900593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458432472785859802600395 3687648709178789703900593)
            ·
              refine ⟨2765736531884092277925445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687648709178789703900593 2765736531884092277925445)
              ·
                refine ⟨518575599728267302111021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2765736531884092277925445 518575599728267302111021)
                ·
                  refine ⟨194465849898100238291633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518575599728267302111021 194465849898100238291633)
                  ·
                    rfl

theorem cell20_426061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_426061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426061 prefixEnd_426061 := by exact prefixLift 426061
  have htrace : WordTrace (prefixWord ++ tailWord_426061) baseStart_426061 baseEnd_426061 := by
    simpa [prefixWord, tailWord_426061, baseEnd_426061] using wordTrace_append hprefix tailTrace_426061
  have hstable : (prefixWord ++ tailWord_426061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426061).length < 2 ^ (prefixWord ++ tailWord_426061).sum := by decide
  have hdescent : baseEnd_426061 < baseStart_426061 := by decide
  rcases family_descends (prefixWord ++ tailWord_426061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426096 : List Nat := [2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_426096 : Nat := 118140960795 + 426096 * 2 ^ 59
def prefixEnd_426096 : Nat := 4983230072969 + 3 ^ 40 * 426096 * 2
def baseEnd_426096 : Nat := 64827274950598557374941

theorem tailTrace_426096 : CollatzResearch.WordTrace tailWord_426096 prefixEnd_426096 64827274950598557374941 := by
  unfold tailWord_426096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770498932167219124141071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10360665242889625498854761 7770498932167219124141071)
  ·
    refine ⟨11655748398250828686211607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7770498932167219124141071 11655748398250828686211607)
    ·
      refine ⟨17483622597376243029317411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655748398250828686211607 17483622597376243029317411)
      ·
        refine ⟨26225433896064364543976117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17483622597376243029317411 26225433896064364543976117)
        ·
          refine ⟨2458634427756034175997761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26225433896064364543976117 2458634427756034175997761)
          ·
            refine ⟨1843975820817025631998321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458634427756034175997761 1843975820817025631998321)
            ·
              refine ⟨1382981865612769223998741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843975820817025631998321 1382981865612769223998741)
              ·
                refine ⟨64827274950598557374941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1382981865612769223998741 64827274950598557374941)
                ·
                  rfl

theorem cell20_426096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_426096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426096 prefixEnd_426096 := by exact prefixLift 426096
  have htrace : WordTrace (prefixWord ++ tailWord_426096) baseStart_426096 baseEnd_426096 := by
    simpa [prefixWord, tailWord_426096, baseEnd_426096] using wordTrace_append hprefix tailTrace_426096
  have hstable : (prefixWord ++ tailWord_426096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426096).length < 2 ^ (prefixWord ++ tailWord_426096).sum := by decide
  have hdescent : baseEnd_426096 < baseStart_426096 := by decide
  rcases family_descends (prefixWord ++ tailWord_426096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426113 : List Nat := [1, 2, 4, 2, 4, 7]
def baseStart_426113 : Nat := 118140960795 + 426113 * 2 ^ 59
def prefixEnd_426113 : Nat := 4983230072969 + 3 ^ 40 * 426113 * 2
def baseEnd_426113 : Nat := 7203317930185895131781

theorem tailTrace_426113 : CollatzResearch.WordTrace tailWord_426113 prefixEnd_426113 7203317930185895131781 := by
  unfold tailWord_426113
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541617905272850151650993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10361078603515233434433995 15541617905272850151650993)
  ·
    refine ⟨11656213428954637613738245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15541617905272850151650993 11656213428954637613738245)
    ·
      refine ⟨2185540017928994552575921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11656213428954637613738245 2185540017928994552575921)
      ·
        refine ⟨1639155013446745914431941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2185540017928994552575921 1639155013446745914431941)
        ·
          refine ⟨307341565021264858955989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1639155013446745914431941 307341565021264858955989)
          ·
            refine ⟨7203317930185895131781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 307341565021264858955989 7203317930185895131781)
            ·
              rfl

theorem cell20_426113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 7].length) (baseStart_426113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426113 prefixEnd_426113 := by exact prefixLift 426113
  have htrace : WordTrace (prefixWord ++ tailWord_426113) baseStart_426113 baseEnd_426113 := by
    simpa [prefixWord, tailWord_426113, baseEnd_426113] using wordTrace_append hprefix tailTrace_426113
  have hstable : (prefixWord ++ tailWord_426113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426113).length < 2 ^ (prefixWord ++ tailWord_426113).sum := by decide
  have hdescent : baseEnd_426113 < baseStart_426113 := by decide
  rcases family_descends (prefixWord ++ tailWord_426113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426178 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_426178 : Nat := 118140960795 + 426178 * 2 ^ 59
def prefixEnd_426178 : Nat := 4983230072969 + 3 ^ 40 * 426178 * 2
def baseEnd_426178 : Nat := 194519251886167831391155

theorem tailTrace_426178 : CollatzResearch.WordTrace tailWord_426178 prefixEnd_426178 194519251886167831391155 := by
  unfold tailWord_426178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885997162509341563191797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10362659100024910835178125 3885997162509341563191797)
  ·
    refine ⟨364312233985250771549231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3885997162509341563191797 364312233985250771549231)
    ·
      refine ⟨546468350977876157323847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364312233985250771549231 546468350977876157323847)
      ·
        refine ⟨819702526466814235985771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546468350977876157323847 819702526466814235985771)
        ·
          refine ⟨1229553789700221353978657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819702526466814235985771 1229553789700221353978657)
          ·
            refine ⟨922165342275166015483993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229553789700221353978657 922165342275166015483993)
            ·
              refine ⟨691624006706374511612995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922165342275166015483993 691624006706374511612995)
              ·
                refine ⟨1037436010059561767419493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691624006706374511612995 1037436010059561767419493)
                ·
                  refine ⟨194519251886167831391155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037436010059561767419493 194519251886167831391155)
                  ·
                    rfl

theorem cell20_426178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_426178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426178 prefixEnd_426178 := by exact prefixLift 426178
  have htrace : WordTrace (prefixWord ++ tailWord_426178) baseStart_426178 baseEnd_426178 := by
    simpa [prefixWord, tailWord_426178, baseEnd_426178] using wordTrace_append hprefix tailTrace_426178
  have hstable : (prefixWord ++ tailWord_426178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426178).length < 2 ^ (prefixWord ++ tailWord_426178).sum := by decide
  have hdescent : baseEnd_426178 < baseStart_426178 := by decide
  rcases family_descends (prefixWord ++ tailWord_426178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426224 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_426224 : Nat := 118140960795 + 426224 * 2 ^ 59
def prefixEnd_426224 : Nat := 4983230072969 + 3 ^ 40 * 426224 * 2
def baseEnd_426224 : Nat := 194540247539596115857633

theorem tailTrace_426224 : CollatzResearch.WordTrace tailWord_426224 prefixEnd_426224 194540247539596115857633 := by
  unfold tailWord_426224
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772833203935358054470863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10363777605247144072627817 7772833203935358054470863)
  ·
    refine ⟨11659249805903037081706295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7772833203935358054470863 11659249805903037081706295)
    ·
      refine ⟨17488874708854555622559443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659249805903037081706295 17488874708854555622559443)
      ·
        refine ⟨26233312063281833433839165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17488874708854555622559443 26233312063281833433839165)
        ·
          refine ⟨9837492023730687537689687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26233312063281833433839165 9837492023730687537689687)
          ·
            refine ⟨14756238035596031306534531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837492023730687537689687 14756238035596031306534531)
            ·
              refine ⟨22134357053394046959801797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14756238035596031306534531 22134357053394046959801797)
              ·
                refine ⟨4150191947511383804962837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22134357053394046959801797 4150191947511383804962837)
                ·
                  refine ⟨194540247539596115857633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4150191947511383804962837 194540247539596115857633)
                  ·
                    rfl

theorem cell20_426224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_426224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426224 prefixEnd_426224 := by exact prefixLift 426224
  have htrace : WordTrace (prefixWord ++ tailWord_426224) baseStart_426224 baseEnd_426224 := by
    simpa [prefixWord, tailWord_426224, baseEnd_426224] using wordTrace_append hprefix tailTrace_426224
  have hstable : (prefixWord ++ tailWord_426224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426224).length < 2 ^ (prefixWord ++ tailWord_426224).sum := by decide
  have hdescent : baseEnd_426224 < baseStart_426224 := by decide
  rcases family_descends (prefixWord ++ tailWord_426224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426247 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 3]
def baseStart_426247 : Nat := 118140960795 + 426247 * 2 ^ 59
def prefixEnd_426247 : Nat := 4983230072969 + 3 ^ 40 * 426247 * 2
def baseEnd_426247 : Nat := 194550745366310258090873

theorem tailTrace_426247 : CollatzResearch.WordTrace tailWord_426247 prefixEnd_426247 194550745366310258090873 := by
  unfold tailWord_426247
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546505286787391037028995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10364336857858260691352663 15546505286787391037028995)
  ·
    refine ⟨23319757930181086555543493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15546505286787391037028995 23319757930181086555543493)
    ·
      refine ⟨4372454611908953729164405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23319757930181086555543493 4372454611908953729164405)
      ·
        refine ⟨409917619866464412109163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4372454611908953729164405 409917619866464412109163)
        ·
          refine ⟨614876429799696618163745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409917619866464412109163 614876429799696618163745)
          ·
            refine ⟨461157322349772463622809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614876429799696618163745 461157322349772463622809)
            ·
              refine ⟨345867991762329347717107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461157322349772463622809 345867991762329347717107)
              ·
                refine ⟨518801987643494021575661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345867991762329347717107 518801987643494021575661)
                ·
                  refine ⟨194550745366310258090873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518801987643494021575661 194550745366310258090873)
                  ·
                    rfl

theorem cell20_426247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_426247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426247 prefixEnd_426247 := by exact prefixLift 426247
  have htrace : WordTrace (prefixWord ++ tailWord_426247) baseStart_426247 baseEnd_426247 := by
    simpa [prefixWord, tailWord_426247, baseEnd_426247] using wordTrace_append hprefix tailTrace_426247
  have hstable : (prefixWord ++ tailWord_426247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426247).length < 2 ^ (prefixWord ++ tailWord_426247).sum := by decide
  have hdescent : baseEnd_426247 < baseStart_426247 := by decide
  rcases family_descends (prefixWord ++ tailWord_426247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426248 : List Nat := [2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_426248 : Nat := 118140960795 + 426248 * 2 ^ 59
def prefixEnd_426248 : Nat := 4983230072969 + 3 ^ 40 * 426248 * 2
def baseEnd_426248 : Nat := 64850400597852899685845

theorem tailTrace_426248 : CollatzResearch.WordTrace tailWord_426248 prefixEnd_426248 64850400597852899685845 := by
  unfold tailWord_426248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773270879891884103907699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10364361173189178805210265 7773270879891884103907699)
  ·
    refine ⟨11659906319837826155861549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7773270879891884103907699 11659906319837826155861549)
    ·
      refine ⟨4372464869939184808448081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11659906319837826155861549 4372464869939184808448081)
      ·
        refine ⟨3279348652454388606336061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372464869939184808448081 3279348652454388606336061)
        ·
          refine ⟨1229755744670395727376023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3279348652454388606336061 1229755744670395727376023)
          ·
            refine ⟨1844633617005593591064035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229755744670395727376023 1844633617005593591064035)
            ·
              refine ⟨2766950425508390386596053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844633617005593591064035 2766950425508390386596053)
              ·
                refine ⟨64850400597852899685845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2766950425508390386596053 64850400597852899685845)
                ·
                  rfl

theorem cell20_426248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_426248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426248 prefixEnd_426248 := by exact prefixLift 426248
  have htrace : WordTrace (prefixWord ++ tailWord_426248) baseStart_426248 baseEnd_426248 := by
    simpa [prefixWord, tailWord_426248, baseEnd_426248] using wordTrace_append hprefix tailTrace_426248
  have hstable : (prefixWord ++ tailWord_426248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426248).length < 2 ^ (prefixWord ++ tailWord_426248).sum := by decide
  have hdescent : baseEnd_426248 < baseStart_426248 := by decide
  rcases family_descends (prefixWord ++ tailWord_426248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426289 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_426289 : Nat := 118140960795 + 426289 * 2 ^ 59
def prefixEnd_426289 : Nat := 4983230072969 + 3 ^ 40 * 426289 * 2
def baseEnd_426289 : Nat := 194569915310744778690701

theorem tailTrace_426289 : CollatzResearch.WordTrace tailWord_426289 prefixEnd_426289 194569915310744778690701 := by
  unfold tailWord_426289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548037152635232210057921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10365358101756821473371947 15548037152635232210057921)
  ·
    refine ⟨11661027864476424157543441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15548037152635232210057921 11661027864476424157543441)
    ·
      refine ⟨8745770898357318118157581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11661027864476424157543441 8745770898357318118157581)
      ·
        refine ⟨3279664086883994294309093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8745770898357318118157581 3279664086883994294309093)
        ·
          refine ⟨614937016290748930182955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3279664086883994294309093 614937016290748930182955)
          ·
            refine ⟨922405524436123395274433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614937016290748930182955 922405524436123395274433)
            ·
              refine ⟨691804143327092546455825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922405524436123395274433 691804143327092546455825)
              ·
                refine ⟨518853107495319409841869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691804143327092546455825 518853107495319409841869)
                ·
                  refine ⟨194569915310744778690701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518853107495319409841869 194569915310744778690701)
                  ·
                    rfl

theorem cell20_426289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_426289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426289 prefixEnd_426289 := by exact prefixLift 426289
  have htrace : WordTrace (prefixWord ++ tailWord_426289) baseStart_426289 baseEnd_426289 := by
    simpa [prefixWord, tailWord_426289, baseEnd_426289] using wordTrace_append hprefix tailTrace_426289
  have hstable : (prefixWord ++ tailWord_426289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426289).length < 2 ^ (prefixWord ++ tailWord_426289).sum := by decide
  have hdescent : baseEnd_426289 < baseStart_426289 := by decide
  rcases family_descends (prefixWord ++ tailWord_426289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426292 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_426292 : Nat := 118140960795 + 426292 * 2 ^ 59
def prefixEnd_426292 : Nat := 4983230072969 + 3 ^ 40 * 426292 * 2
def baseEnd_426292 : Nat := 194571284592490101590689

theorem tailTrace_426292 : CollatzResearch.WordTrace tailWord_426292 prefixEnd_426292 194571284592490101590689 := by
  unfold tailWord_426292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774073285812181861208565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10365431047749575814944753 7774073285812181861208565)
  ·
    refine ⟨728819370544892049488303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7774073285812181861208565 728819370544892049488303)
    ·
      refine ⟨1093229055817338074232455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728819370544892049488303 1093229055817338074232455)
      ·
        refine ⟨1639843583726007111348683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093229055817338074232455 1639843583726007111348683)
        ·
          refine ⟨2459765375589010667023025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639843583726007111348683 2459765375589010667023025)
          ·
            refine ⟨1844824031691758000267269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459765375589010667023025 1844824031691758000267269)
            ·
              refine ⟨345904505942204625050113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1844824031691758000267269 345904505942204625050113)
              ·
                refine ⟨259428379456653468787585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345904505942204625050113 259428379456653468787585)
                ·
                  refine ⟨194571284592490101590689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259428379456653468787585 194571284592490101590689)
                  ·
                    rfl

theorem cell20_426292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_426292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426292 prefixEnd_426292 := by exact prefixLift 426292
  have htrace : WordTrace (prefixWord ++ tailWord_426292) baseStart_426292 baseEnd_426292 := by
    simpa [prefixWord, tailWord_426292, baseEnd_426292] using wordTrace_append hprefix tailTrace_426292
  have hstable : (prefixWord ++ tailWord_426292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426292).length < 2 ^ (prefixWord ++ tailWord_426292).sum := by decide
  have hdescent : baseEnd_426292 < baseStart_426292 := by decide
  rcases family_descends (prefixWord ++ tailWord_426292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426345 : List Nat := [1, 2, 1, 1, 1, 3, 11]
def baseStart_426345 : Nat := 118140960795 + 426345 * 2 ^ 59
def prefixEnd_426345 : Nat := 4983230072969 + 3 ^ 40 * 426345 * 2
def baseEnd_426345 : Nat := 21621719470739719202645

theorem tailTrace_426345 : CollatzResearch.WordTrace tailWord_426345 prefixEnd_426345 21621719470739719202645 := by
  unfold tailWord_426345
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550079640432353774096489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10366719760288235849397659 15550079640432353774096489)
  ·
    refine ⟨11662559730324265330572367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15550079640432353774096489 11662559730324265330572367)
    ·
      refine ⟨17493839595486397995858551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11662559730324265330572367 17493839595486397995858551)
      ·
        refine ⟨26240759393229596993787827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17493839595486397995858551 26240759393229596993787827)
        ·
          refine ⟨39361139089844395490681741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26240759393229596993787827 39361139089844395490681741)
          ·
            refine ⟨14760427158691648309005653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39361139089844395490681741 14760427158691648309005653)
            ·
              refine ⟨21621719470739719202645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14760427158691648309005653 21621719470739719202645)
              ·
                rfl

theorem cell20_426345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_426345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426345 prefixEnd_426345 := by exact prefixLift 426345
  have htrace : WordTrace (prefixWord ++ tailWord_426345) baseStart_426345 baseEnd_426345 := by
    simpa [prefixWord, tailWord_426345, baseEnd_426345] using wordTrace_append hprefix tailTrace_426345
  have hstable : (prefixWord ++ tailWord_426345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426345).length < 2 ^ (prefixWord ++ tailWord_426345).sum := by decide
  have hdescent : baseEnd_426345 < baseStart_426345 := by decide
  rcases family_descends (prefixWord ++ tailWord_426345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426348 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_426348 : Nat := 118140960795 + 426348 * 2 ^ 59
def prefixEnd_426348 : Nat := 4983230072969 + 3 ^ 40 * 426348 * 2
def baseEnd_426348 : Nat := 194596844518402795723793

theorem tailTrace_426348 : CollatzResearch.WordTrace tailWord_426348 prefixEnd_426348 194596844518402795723793 := by
  unfold tailWord_426348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775094529710742643227849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10366792706280990190970465 7775094529710742643227849)
  ·
    refine ⟨5831320897283056982420887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7775094529710742643227849 5831320897283056982420887)
    ·
      refine ⟨8746981345924585473631331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5831320897283056982420887 8746981345924585473631331)
      ·
        refine ⟨13120472018886878210446997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8746981345924585473631331 13120472018886878210446997)
        ·
          refine ⟨615022125885322416114703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13120472018886878210446997 615022125885322416114703)
          ·
            refine ⟨922533188827983624172055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615022125885322416114703 922533188827983624172055)
            ·
              refine ⟨1383799783241975436258083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922533188827983624172055 1383799783241975436258083)
              ·
                refine ⟨2075699674862963154387125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383799783241975436258083 2075699674862963154387125)
                ·
                  refine ⟨194596844518402795723793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2075699674862963154387125 194596844518402795723793)
                  ·
                    rfl

theorem cell20_426348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_426348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426348 prefixEnd_426348 := by exact prefixLift 426348
  have htrace : WordTrace (prefixWord ++ tailWord_426348) baseStart_426348 baseEnd_426348 := by
    simpa [prefixWord, tailWord_426348, baseEnd_426348] using wordTrace_append hprefix tailTrace_426348
  have hstable : (prefixWord ++ tailWord_426348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426348).length < 2 ^ (prefixWord ++ tailWord_426348).sum := by decide
  have hdescent : baseEnd_426348 < baseStart_426348 := by decide
  rcases family_descends (prefixWord ++ tailWord_426348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426365 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 3]
def baseStart_426365 : Nat := 118140960795 + 426365 * 2 ^ 59
def prefixEnd_426365 : Nat := 4983230072969 + 3 ^ 40 * 426365 * 2
def baseEnd_426365 : Nat := 194604603781626292157057

theorem tailTrace_426365 : CollatzResearch.WordTrace tailWord_426365 prefixEnd_426365 194604603781626292157057 := by
  unfold tailWord_426365
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550809100359897189824549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10367206066906598126549699 15550809100359897189824549)
  ·
    refine ⟨2915776706317480723092103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15550809100359897189824549 2915776706317480723092103)
    ·
      refine ⟨4373665059476221084638155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915776706317480723092103 4373665059476221084638155)
      ·
        refine ⟨6560497589214331626957233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373665059476221084638155 6560497589214331626957233)
        ·
          refine ⟨4920373191910748720217925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6560497589214331626957233 4920373191910748720217925)
          ·
            refine ⟨922569973483265385040861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4920373191910748720217925 922569973483265385040861)
            ·
              refine ⟨345963740056224519390323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922569973483265385040861 345963740056224519390323)
              ·
                refine ⟨518945610084336779085485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345963740056224519390323 518945610084336779085485)
                ·
                  refine ⟨194604603781626292157057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518945610084336779085485 194604603781626292157057)
                  ·
                    rfl

theorem cell20_426365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_426365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426365 prefixEnd_426365 := by exact prefixLift 426365
  have htrace : WordTrace (prefixWord ++ tailWord_426365) baseStart_426365 baseEnd_426365 := by
    simpa [prefixWord, tailWord_426365, baseEnd_426365] using wordTrace_append hprefix tailTrace_426365
  have hstable : (prefixWord ++ tailWord_426365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426365).length < 2 ^ (prefixWord ++ tailWord_426365).sum := by decide
  have hdescent : baseEnd_426365 < baseStart_426365 := by decide
  rcases family_descends (prefixWord ++ tailWord_426365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426379 : List Nat := [1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_426379 : Nat := 118140960795 + 426379 * 2 ^ 59
def prefixEnd_426379 : Nat := 4983230072969 + 3 ^ 40 * 426379 * 2
def baseEnd_426379 : Nat := 64870331254368155230111

theorem tailTrace_426379 : CollatzResearch.WordTrace tailWord_426379 prefixEnd_426379 64870331254368155230111 := by
  unfold tailWord_426379
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551319722309177580834191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10367546481539451720556127 15551319722309177580834191)
  ·
    refine ⟨23326979583463766371251287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15551319722309177580834191 23326979583463766371251287)
    ·
      refine ⟨34990469375195649556876931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23326979583463766371251287 34990469375195649556876931)
      ·
        refine ⟨52485704062793474335315397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34990469375195649556876931 52485704062793474335315397)
        ·
          refine ⟨9841069511773776437871637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52485704062793474335315397 9841069511773776437871637)
          ·
            refine ⟨461300133364395770525233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9841069511773776437871637 461300133364395770525233)
            ·
              refine ⟨345975100023296827893925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461300133364395770525233 345975100023296827893925)
              ·
                refine ⟨64870331254368155230111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345975100023296827893925 64870331254368155230111)
                ·
                  rfl

theorem cell20_426379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_426379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426379 prefixEnd_426379 := by exact prefixLift 426379
  have htrace : WordTrace (prefixWord ++ tailWord_426379) baseStart_426379 baseEnd_426379 := by
    simpa [prefixWord, tailWord_426379, baseEnd_426379] using wordTrace_append hprefix tailTrace_426379
  have hstable : (prefixWord ++ tailWord_426379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426379).length < 2 ^ (prefixWord ++ tailWord_426379).sum := by decide
  have hdescent : baseEnd_426379 < baseStart_426379 := by decide
  rcases family_descends (prefixWord ++ tailWord_426379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426400 : List Nat := [2, 1, 1, 4, 1, 5, 6]
def baseStart_426400 : Nat := 118140960795 + 426400 * 2 ^ 59
def prefixEnd_426400 : Nat := 4983230072969 + 3 ^ 40 * 426400 * 2
def baseEnd_426400 : Nat := 21624508748369080665583

theorem tailTrace_426400 : CollatzResearch.WordTrace tailWord_426400 prefixEnd_426400 21624508748369080665583 := by
  unfold tailWord_426400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776042827616549083674327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10368057103488732111565769 7776042827616549083674327)
  ·
    refine ⟨11664064241424823625511491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776042827616549083674327 11664064241424823625511491)
    ·
      refine ⟨17496096362137235438267237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664064241424823625511491 17496096362137235438267237)
      ·
        refine ⟨3280518067900731644675107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17496096362137235438267237 3280518067900731644675107)
        ·
          refine ⟨4920777101851097467012661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280518067900731644675107 4920777101851097467012661)
          ·
            refine ⟨461322853298540387532437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4920777101851097467012661 461322853298540387532437)
            ·
              refine ⟨21624508748369080665583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 461322853298540387532437 21624508748369080665583)
              ·
                rfl

theorem cell20_426400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_426400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426400 prefixEnd_426400 := by exact prefixLift 426400
  have htrace : WordTrace (prefixWord ++ tailWord_426400) baseStart_426400 baseEnd_426400 := by
    simpa [prefixWord, tailWord_426400, baseEnd_426400] using wordTrace_append hprefix tailTrace_426400
  have hstable : (prefixWord ++ tailWord_426400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426400).length < 2 ^ (prefixWord ++ tailWord_426400).sum := by decide
  have hdescent : baseEnd_426400 < baseStart_426400 := by decide
  rcases family_descends (prefixWord ++ tailWord_426400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426483 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_426483 : Nat := 118140960795 + 426483 * 2 ^ 59
def prefixEnd_426483 : Nat := 4983230072969 + 3 ^ 40 * 426483 * 2
def baseEnd_426483 : Nat := 194658462196942326223241

theorem tailTrace_426483 : CollatzResearch.WordTrace tailWord_426483 prefixEnd_426483 194658462196942326223241 := by
  unfold tailWord_426483
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555112913932403342620103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10370075275954935561746735 15555112913932403342620103)
  ·
    refine ⟨23332669370898605013930155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555112913932403342620103 23332669370898605013930155)
    ·
      refine ⟨34999004056347907520895233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23332669370898605013930155 34999004056347907520895233)
      ·
        refine ⟨26249253042260930640671425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34999004056347907520895233 26249253042260930640671425)
        ·
          refine ⟨19686939781695697980503569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26249253042260930640671425 19686939781695697980503569)
          ·
            refine ⟨14765204836271773485377677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19686939781695697980503569 14765204836271773485377677)
            ·
              refine ⟨5536951813601915057016629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14765204836271773485377677 5536951813601915057016629)
              ·
                refine ⟨519089232525179536595309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5536951813601915057016629 519089232525179536595309)
                ·
                  refine ⟨194658462196942326223241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519089232525179536595309 194658462196942326223241)
                  ·
                    rfl

theorem cell20_426483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_426483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426483 prefixEnd_426483 := by exact prefixLift 426483
  have htrace : WordTrace (prefixWord ++ tailWord_426483) baseStart_426483 baseEnd_426483 := by
    simpa [prefixWord, tailWord_426483, baseEnd_426483] using wordTrace_append hprefix tailTrace_426483
  have hstable : (prefixWord ++ tailWord_426483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426483).length < 2 ^ (prefixWord ++ tailWord_426483).sum := by decide
  have hdescent : baseEnd_426483 < baseStart_426483 := by decide
  rcases family_descends (prefixWord ++ tailWord_426483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426503 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 2]
def baseStart_426503 : Nat := 118140960795 + 426503 * 2 ^ 59
def prefixEnd_426503 : Nat := 4983230072969 + 3 ^ 40 * 426503 * 2
def baseEnd_426503 : Nat := 194667590741911145556493

theorem tailTrace_426503 : CollatzResearch.WordTrace tailWord_426503 prefixEnd_426503 194667590741911145556493 := by
  unfold tailWord_426503
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555842373859946758348163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10370561582573297838898775 15555842373859946758348163)
  ·
    refine ⟨23333763560789920137522245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555842373859946758348163 23333763560789920137522245)
    ·
      refine ⟨4375080667648110025785421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23333763560789920137522245 4375080667648110025785421)
      ·
        refine ⟨1640655250368041259669533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4375080667648110025785421 1640655250368041259669533)
        ·
          refine ⟨615245718888015472376075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1640655250368041259669533 615245718888015472376075)
          ·
            refine ⟨922868578332023208564113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615245718888015472376075 922868578332023208564113)
            ·
              refine ⟨692151433749017406423085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922868578332023208564113 692151433749017406423085)
              ·
                refine ⟨259556787655881527408657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692151433749017406423085 259556787655881527408657)
                ·
                  refine ⟨194667590741911145556493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259556787655881527408657 194667590741911145556493)
                  ·
                    rfl

theorem cell20_426503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2].length) (baseStart_426503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426503 prefixEnd_426503 := by exact prefixLift 426503
  have htrace : WordTrace (prefixWord ++ tailWord_426503) baseStart_426503 baseEnd_426503 := by
    simpa [prefixWord, tailWord_426503, baseEnd_426503] using wordTrace_append hprefix tailTrace_426503
  have hstable : (prefixWord ++ tailWord_426503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426503).length < 2 ^ (prefixWord ++ tailWord_426503).sum := by decide
  have hdescent : baseEnd_426503 < baseStart_426503 := by decide
  rcases family_descends (prefixWord ++ tailWord_426503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426524 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_426524 : Nat := 118140960795 + 426524 * 2 ^ 59
def prefixEnd_426524 : Nat := 4983230072969 + 3 ^ 40 * 426524 * 2
def baseEnd_426524 : Nat := 194677175714128405856407

theorem tailTrace_426524 : CollatzResearch.WordTrace tailWord_426524 prefixEnd_426524 194677175714128405856407 := by
  unfold tailWord_426524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778304153391933672431313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10371072204522578229908417 7778304153391933672431313)
  ·
    refine ⟨5833728115043950254323485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7778304153391933672431313 5833728115043950254323485)
    ·
      refine ⟨2187648043141481345371307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5833728115043950254323485 2187648043141481345371307)
      ·
        refine ⟨3281472064712222018056961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187648043141481345371307 3281472064712222018056961)
        ·
          refine ⟨2461104048534166513542721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281472064712222018056961 2461104048534166513542721)
          ·
            refine ⟨1845828036400624885157041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2461104048534166513542721 1845828036400624885157041)
            ·
              refine ⟨1384371027300468663867781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845828036400624885157041 1384371027300468663867781)
              ·
                refine ⟨259569567618837874475209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1384371027300468663867781 259569567618837874475209)
                ·
                  refine ⟨194677175714128405856407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259569567618837874475209 194677175714128405856407)
                  ·
                    rfl

theorem cell20_426524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_426524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426524 prefixEnd_426524 := by exact prefixLift 426524
  have htrace : WordTrace (prefixWord ++ tailWord_426524) baseStart_426524 baseEnd_426524 := by
    simpa [prefixWord, tailWord_426524, baseEnd_426524] using wordTrace_append hprefix tailTrace_426524
  have hstable : (prefixWord ++ tailWord_426524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426524).length < 2 ^ (prefixWord ++ tailWord_426524).sum := by decide
  have hdescent : baseEnd_426524 < baseStart_426524 := by decide
  rcases family_descends (prefixWord ++ tailWord_426524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426548 : List Nat := [2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_426548 : Nat := 118140960795 + 426548 * 2 ^ 59
def prefixEnd_426548 : Nat := 4983230072969 + 3 ^ 40 * 426548 * 2
def baseEnd_426548 : Nat := 64896043322696996352103

theorem tailTrace_426548 : CollatzResearch.WordTrace tailWord_426548 prefixEnd_426548 64896043322696996352103 := by
  unfold tailWord_426548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778741829348459721868149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10371655772464612962490865 7778741829348459721868149)
  ·
    refine ⟨729257046501418098925139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7778741829348459721868149 729257046501418098925139)
    ·
      refine ⟨1093885569752127148387709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729257046501418098925139 1093885569752127148387709)
      ·
        refine ⟨410207088657047680645391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1093885569752127148387709 410207088657047680645391)
        ·
          refine ⟨615310632985571520968087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410207088657047680645391 615310632985571520968087)
          ·
            refine ⟨922965949478357281452131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615310632985571520968087 922965949478357281452131)
            ·
              refine ⟨1384448924217535922178197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922965949478357281452131 1384448924217535922178197)
              ·
                refine ⟨64896043322696996352103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1384448924217535922178197 64896043322696996352103)
                ·
                  rfl

theorem cell20_426548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_426548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426548 prefixEnd_426548 := by exact prefixLift 426548
  have htrace : WordTrace (prefixWord ++ tailWord_426548) baseStart_426548 baseEnd_426548 := by
    simpa [prefixWord, tailWord_426548, baseEnd_426548] using wordTrace_append hprefix tailTrace_426548
  have hstable : (prefixWord ++ tailWord_426548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426548).length < 2 ^ (prefixWord ++ tailWord_426548).sum := by decide
  have hdescent : baseEnd_426548 < baseStart_426548 := by decide
  rcases family_descends (prefixWord ++ tailWord_426548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426593 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 3]
def baseStart_426593 : Nat := 118140960795 + 426593 * 2 ^ 59
def prefixEnd_426593 : Nat := 4983230072969 + 3 ^ 40 * 426593 * 2
def baseEnd_426593 : Nat := 194708669194270832556125

theorem tailTrace_426593 : CollatzResearch.WordTrace tailWord_426593 prefixEnd_426593 194708669194270832556125 := by
  unfold tailWord_426593
  simp only [CollatzResearch.WordTrace]
  refine ⟨15559124943533892129124433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10372749962355928086082955 15559124943533892129124433)
  ·
    refine ⟨11669343707650419096843325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15559124943533892129124433 11669343707650419096843325)
    ·
      refine ⟨4376003890368907161316247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11669343707650419096843325 4376003890368907161316247)
      ·
        refine ⟨6564005835553360741974371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376003890368907161316247 6564005835553360741974371)
        ·
          refine ⟨9846008753330041112961557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564005835553360741974371 9846008753330041112961557)
          ·
            refine ⟨461531660312345677170073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9846008753330041112961557 461531660312345677170073)
            ·
              refine ⟨346148745234259257877555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461531660312345677170073 346148745234259257877555)
              ·
                refine ⟨519223117851388886816333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346148745234259257877555 519223117851388886816333)
                ·
                  refine ⟨194708669194270832556125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519223117851388886816333 194708669194270832556125)
                  ·
                    rfl

theorem cell20_426593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_426593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426593 prefixEnd_426593 := by exact prefixLift 426593
  have htrace : WordTrace (prefixWord ++ tailWord_426593) baseStart_426593 baseEnd_426593 := by
    simpa [prefixWord, tailWord_426593, baseEnd_426593] using wordTrace_append hprefix tailTrace_426593
  have hstable : (prefixWord ++ tailWord_426593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426593).length < 2 ^ (prefixWord ++ tailWord_426593).sum := by decide
  have hdescent : baseEnd_426593 < baseStart_426593 := by decide
  rcases family_descends (prefixWord ++ tailWord_426593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426604 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_426604 : Nat := 118140960795 + 426604 * 2 ^ 59
def prefixEnd_426604 : Nat := 4983230072969 + 3 ^ 40 * 426604 * 2
def baseEnd_426604 : Nat := 194713689894003683189413

theorem tailTrace_426604 : CollatzResearch.WordTrace tailWord_426604 prefixEnd_426604 194713689894003683189413 := by
  unfold tailWord_426604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779763073247020503887433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10373017430996027338516577 7779763073247020503887433)
  ·
    refine ⟨5834822304935265377915575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7779763073247020503887433 5834822304935265377915575)
    ·
      refine ⟨8752233457402898066873363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834822304935265377915575 8752233457402898066873363)
      ·
        refine ⟨13128350186104347100310045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8752233457402898066873363 13128350186104347100310045)
        ·
          refine ⟨4923131319789130162616267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13128350186104347100310045 4923131319789130162616267)
          ·
            refine ⟨7384696979683695243924401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923131319789130162616267 7384696979683695243924401)
            ·
              refine ⟨5538522734762771432943301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7384696979683695243924401 5538522734762771432943301)
              ·
                refine ⟨1038473012768019643676869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5538522734762771432943301 1038473012768019643676869)
                ·
                  refine ⟨194713689894003683189413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1038473012768019643676869 194713689894003683189413)
                  ·
                    rfl

theorem cell20_426604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_426604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426604 prefixEnd_426604 := by exact prefixLift 426604
  have htrace : WordTrace (prefixWord ++ tailWord_426604) baseStart_426604 baseEnd_426604 := by
    simpa [prefixWord, tailWord_426604, baseEnd_426604] using wordTrace_append hprefix tailTrace_426604
  have hstable : (prefixWord ++ tailWord_426604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426604).length < 2 ^ (prefixWord ++ tailWord_426604).sum := by decide
  have hdescent : baseEnd_426604 < baseStart_426604 := by decide
  rcases family_descends (prefixWord ++ tailWord_426604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426634 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_426634 : Nat := 118140960795 + 426634 * 2 ^ 59
def prefixEnd_426634 : Nat := 4983230072969 + 3 ^ 40 * 426634 * 2
def baseEnd_426634 : Nat := 194727382711456912189291

theorem tailTrace_426634 : CollatzResearch.WordTrace tailWord_426634 prefixEnd_426634 194727382711456912189291 := by
  unfold tailWord_426634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890155084096339032841739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10373746890923570754244637 3890155084096339032841739)
  ·
    refine ⟨5835232626144508549262609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3890155084096339032841739 5835232626144508549262609)
    ·
      refine ⟨4376424469608381411946957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5835232626144508549262609 4376424469608381411946957)
      ·
        refine ⟨1641159176103143029480109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4376424469608381411946957 1641159176103143029480109)
        ·
          refine ⟨615434691038678636055041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1641159176103143029480109 615434691038678636055041)
          ·
            refine ⟨461576018279008977041281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615434691038678636055041 461576018279008977041281)
            ·
              refine ⟨346182013709256732780961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461576018279008977041281 346182013709256732780961)
              ·
                refine ⟨259636510281942549585721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346182013709256732780961 259636510281942549585721)
                ·
                  refine ⟨194727382711456912189291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259636510281942549585721 194727382711456912189291)
                  ·
                    rfl

theorem cell20_426634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_426634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426634 prefixEnd_426634 := by exact prefixLift 426634
  have htrace : WordTrace (prefixWord ++ tailWord_426634) baseStart_426634 baseEnd_426634 := by
    simpa [prefixWord, tailWord_426634, baseEnd_426634] using wordTrace_append hprefix tailTrace_426634
  have hstable : (prefixWord ++ tailWord_426634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426634).length < 2 ^ (prefixWord ++ tailWord_426634).sum := by decide
  have hdescent : baseEnd_426634 < baseStart_426634 := by decide
  rcases family_descends (prefixWord ++ tailWord_426634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426638 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_426638 : Nat := 118140960795 + 426638 * 2 ^ 59
def prefixEnd_426638 : Nat := 4983230072969 + 3 ^ 40 * 426638 * 2
def baseEnd_426638 : Nat := 194729208420450676055941

theorem tailTrace_426638 : CollatzResearch.WordTrace tailWord_426638 prefixEnd_426638 194729208420450676055941 := by
  unfold tailWord_426638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945095778546358101814071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10373844152247243209675045 1945095778546358101814071)
  ·
    refine ⟨2917643667819537152721107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945095778546358101814071 2917643667819537152721107)
    ·
      refine ⟨4376465501729305729081661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2917643667819537152721107 4376465501729305729081661)
      ·
        refine ⟨1641174563148489648405623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4376465501729305729081661 1641174563148489648405623)
        ·
          refine ⟨2461761844722734472608435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641174563148489648405623 2461761844722734472608435)
          ·
            refine ⟨3692642767084101708912653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461761844722734472608435 3692642767084101708912653)
            ·
              refine ⟨1384741037656538140842245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3692642767084101708912653 1384741037656538140842245)
              ·
                refine ⟨259638944560600901407921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1384741037656538140842245 259638944560600901407921)
                ·
                  refine ⟨194729208420450676055941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259638944560600901407921 194729208420450676055941)
                  ·
                    rfl

theorem cell20_426638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_426638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426638 prefixEnd_426638 := by exact prefixLift 426638
  have htrace : WordTrace (prefixWord ++ tailWord_426638) baseStart_426638 baseEnd_426638 := by
    simpa [prefixWord, tailWord_426638, baseEnd_426638] using wordTrace_append hprefix tailTrace_426638
  have hstable : (prefixWord ++ tailWord_426638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426638).length < 2 ^ (prefixWord ++ tailWord_426638).sum := by decide
  have hdescent : baseEnd_426638 < baseStart_426638 := by decide
  rcases family_descends (prefixWord ++ tailWord_426638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426652 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_426652 : Nat := 118140960795 + 426652 * 2 ^ 59
def prefixEnd_426652 : Nat := 4983230072969 + 3 ^ 40 * 426652 * 2
def baseEnd_426652 : Nat := 194735598401928849589217

theorem tailTrace_426652 : CollatzResearch.WordTrace tailWord_426652 prefixEnd_426652 194735598401928849589217 := by
  unfold tailWord_426652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7780638425160072602761105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10374184566880096803681473 7780638425160072602761105)
  ·
    refine ⟨5835478818870054452070829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7780638425160072602761105 5835478818870054452070829)
    ·
      refine ⟨2188304557076270419526561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5835478818870054452070829 2188304557076270419526561)
      ·
        refine ⟨1641228417807202814644921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2188304557076270419526561 1641228417807202814644921)
        ·
          refine ⟨1230921313355402110983691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641228417807202814644921 1230921313355402110983691)
          ·
            refine ⟨1846381970033103166475537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230921313355402110983691 1846381970033103166475537)
            ·
              refine ⟨1384786477524827374856653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846381970033103166475537 1384786477524827374856653)
              ·
                refine ⟨519294929071810265571245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384786477524827374856653 519294929071810265571245)
                ·
                  refine ⟨194735598401928849589217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519294929071810265571245 194735598401928849589217)
                  ·
                    rfl

theorem cell20_426652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_426652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426652 prefixEnd_426652 := by exact prefixLift 426652
  have htrace : WordTrace (prefixWord ++ tailWord_426652) baseStart_426652 baseEnd_426652 := by
    simpa [prefixWord, tailWord_426652, baseEnd_426652] using wordTrace_append hprefix tailTrace_426652
  have hstable : (prefixWord ++ tailWord_426652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426652).length < 2 ^ (prefixWord ++ tailWord_426652).sum := by decide
  have hdescent : baseEnd_426652 < baseStart_426652 := by decide
  rcases family_descends (prefixWord ++ tailWord_426652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426687 : List Nat := [1, 1, 2, 2, 2, 5, 7]
def baseStart_426687 : Nat := 118140960795 + 426687 * 2 ^ 59
def prefixEnd_426687 : Nat := 4983230072969 + 3 ^ 40 * 426687 * 2
def baseEnd_426687 : Nat := 21639063706180475935823

theorem tailTrace_426687 : CollatzResearch.WordTrace tailWord_426687 prefixEnd_426687 21639063706180475935823 := by
  unfold tailWord_426687
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562553405193346183046315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10375035603462230788697543 15562553405193346183046315)
  ·
    refine ⟨23343830107790019274569473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15562553405193346183046315 23343830107790019274569473)
    ·
      refine ⟨17507872580842514455927105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23343830107790019274569473 17507872580842514455927105)
      ·
        refine ⟨13130904435631885841945329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17507872580842514455927105 13130904435631885841945329)
        ·
          refine ⟨9848178326723914381458997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13130904435631885841945329 9848178326723914381458997)
          ·
            refine ⟨923266718130366973261781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9848178326723914381458997 923266718130366973261781)
            ·
              refine ⟨21639063706180475935823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 923266718130366973261781 21639063706180475935823)
              ·
                rfl

theorem cell20_426687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_426687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426687 prefixEnd_426687 := by exact prefixLift 426687
  have htrace : WordTrace (prefixWord ++ tailWord_426687) baseStart_426687 baseEnd_426687 := by
    simpa [prefixWord, tailWord_426687, baseEnd_426687] using wordTrace_append hprefix tailTrace_426687
  have hstable : (prefixWord ++ tailWord_426687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426687).length < 2 ^ (prefixWord ++ tailWord_426687).sum := by decide
  have hdescent : baseEnd_426687 < baseStart_426687 := by decide
  rcases family_descends (prefixWord ++ tailWord_426687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426721 : List Nat := [1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_426721 : Nat := 118140960795 + 426721 * 2 ^ 59
def prefixEnd_426721 : Nat := 4983230072969 + 3 ^ 40 * 426721 * 2
def baseEnd_426721 : Nat := 64922363960690425429645

theorem tailTrace_426721 : CollatzResearch.WordTrace tailWord_426721 prefixEnd_426721 64922363960690425429645 := by
  unfold tailWord_426721
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563793487070169989784017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10375862324713446659856011 15563793487070169989784017)
  ·
    refine ⟨11672845115302627492338013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15563793487070169989784017 11672845115302627492338013)
    ·
      refine ⟨4377316918238485309626755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11672845115302627492338013 4377316918238485309626755)
      ·
        refine ⟨6565975377357727964440133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377316918238485309626755 6565975377357727964440133)
        ·
          refine ⟨1231120383254573993332525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6565975377357727964440133 1231120383254573993332525)
          ·
            refine ⟨461670143720465247499697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1231120383254573993332525 461670143720465247499697)
            ·
              refine ⟨346252607790348935624773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461670143720465247499697 346252607790348935624773)
              ·
                refine ⟨64922363960690425429645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346252607790348935624773 64922363960690425429645)
                ·
                  rfl

theorem cell20_426721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_426721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426721 prefixEnd_426721 := by exact prefixLift 426721
  have htrace : WordTrace (prefixWord ++ tailWord_426721) baseStart_426721 baseEnd_426721 := by
    simpa [prefixWord, tailWord_426721, baseEnd_426721] using wordTrace_append hprefix tailTrace_426721
  have hstable : (prefixWord ++ tailWord_426721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426721).length < 2 ^ (prefixWord ++ tailWord_426721).sum := by decide
  have hdescent : baseEnd_426721 < baseStart_426721 := by decide
  rcases family_descends (prefixWord ++ tailWord_426721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426749 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_426749 : Nat := 118140960795 + 426749 * 2 ^ 59
def prefixEnd_426749 : Nat := 4983230072969 + 3 ^ 40 * 426749 * 2
def baseEnd_426749 : Nat := 194779871845027623355487

theorem tailTrace_426749 : CollatzResearch.WordTrace tailWord_426749 prefixEnd_426749 194779871845027623355487 := by
  unfold tailWord_426749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15564814730968730771803301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10376543153979153847868867 15564814730968730771803301)
  ·
    refine ⟨2918402762056637019713119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15564814730968730771803301 2918402762056637019713119)
    ·
      refine ⟨4377604143084955529569679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918402762056637019713119 4377604143084955529569679)
      ·
        refine ⟨6566406214627433294354519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377604143084955529569679 6566406214627433294354519)
        ·
          refine ⟨9849609321941149941531779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566406214627433294354519 9849609321941149941531779)
          ·
            refine ⟨14774413982911724912297669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849609321941149941531779 14774413982911724912297669)
            ·
              refine ⟨2770202621795948421055813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14774413982911724912297669 2770202621795948421055813)
              ·
                refine ⟨519412991586740328947965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2770202621795948421055813 519412991586740328947965)
                ·
                  refine ⟨194779871845027623355487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519412991586740328947965 194779871845027623355487)
                  ·
                    rfl

theorem cell20_426749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_426749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426749 prefixEnd_426749 := by exact prefixLift 426749
  have htrace : WordTrace (prefixWord ++ tailWord_426749) baseStart_426749 baseEnd_426749 := by
    simpa [prefixWord, tailWord_426749, baseEnd_426749] using wordTrace_append hprefix tailTrace_426749
  have hstable : (prefixWord ++ tailWord_426749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426749).length < 2 ^ (prefixWord ++ tailWord_426749).sum := by decide
  have hdescent : baseEnd_426749 < baseStart_426749 := by decide
  rcases family_descends (prefixWord ++ tailWord_426749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426797 : List Nat := [1, 5, 3, 2, 1, 8]
def baseStart_426797 : Nat := 118140960795 + 426797 * 2 ^ 59
def prefixEnd_426797 : Nat := 4983230072969 + 3 ^ 40 * 426797 * 2
def baseEnd_426797 : Nat := 7214880753813066287233

theorem tailTrace_426797 : CollatzResearch.WordTrace tailWord_426797 prefixEnd_426797 7214880753813066287233 := by
  unfold tailWord_426797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566565434794834969550645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10377710289863223313033763 15566565434794834969550645)
  ·
    refine ⟨1459365509512015778395373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15566565434794834969550645 1459365509512015778395373)
    ·
      refine ⟨547262066067005916898265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1459365509512015778395373 547262066067005916898265)
      ·
        refine ⟨410446549550254437673699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547262066067005916898265 410446549550254437673699)
        ·
          refine ⟨615669824325381656510549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410446549550254437673699 615669824325381656510549)
          ·
            refine ⟨7214880753813066287233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 615669824325381656510549 7214880753813066287233)
            ·
              rfl

theorem cell20_426797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 8].length) (baseStart_426797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426797 prefixEnd_426797 := by exact prefixLift 426797
  have htrace : WordTrace (prefixWord ++ tailWord_426797) baseStart_426797 baseEnd_426797 := by
    simpa [prefixWord, tailWord_426797, baseEnd_426797] using wordTrace_append hprefix tailTrace_426797
  have hstable : (prefixWord ++ tailWord_426797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426797).length < 2 ^ (prefixWord ++ tailWord_426797).sum := by decide
  have hdescent : baseEnd_426797 < baseStart_426797 := by decide
  rcases family_descends (prefixWord ++ tailWord_426797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426814 : List Nat := [4, 2, 1, 2, 4, 1, 1, 5]
def baseStart_426814 : Nat := 118140960795 + 426814 * 2 ^ 59
def prefixEnd_426814 : Nat := 4983230072969 + 3 ^ 40 * 426814 * 2
def baseEnd_426814 : Nat := 64936513205392095396185

theorem tailTrace_426814 : CollatzResearch.WordTrace tailWord_426814 prefixEnd_426814 64936513205392095396185 := by
  unfold tailWord_426814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945898184466655859114937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10378123650488831248612997 1945898184466655859114937)
  ·
    refine ⟨1459423638349991894336203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1945898184466655859114937 1459423638349991894336203)
    ·
      refine ⟨2189135457524987841504305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459423638349991894336203 2189135457524987841504305)
      ·
        refine ⟨1641851593143740881128229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189135457524987841504305 1641851593143740881128229)
        ·
          refine ⟨307847173714451415211543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1641851593143740881128229 307847173714451415211543)
          ·
            refine ⟨461770760571677122817315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307847173714451415211543 461770760571677122817315)
            ·
              refine ⟨692656140857515684225973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461770760571677122817315 692656140857515684225973)
              ·
                refine ⟨64936513205392095396185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692656140857515684225973 64936513205392095396185)
                ·
                  rfl

theorem cell20_426814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_426814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426814 prefixEnd_426814 := by exact prefixLift 426814
  have htrace : WordTrace (prefixWord ++ tailWord_426814) baseStart_426814 baseEnd_426814 := by
    simpa [prefixWord, tailWord_426814, baseEnd_426814] using wordTrace_append hprefix tailTrace_426814
  have hstable : (prefixWord ++ tailWord_426814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426814).length < 2 ^ (prefixWord ++ tailWord_426814).sum := by decide
  have hdescent : baseEnd_426814 < baseStart_426814 := by decide
  rcases family_descends (prefixWord ++ tailWord_426814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426825 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_426825 : Nat := 118140960795 + 426825 * 2 ^ 59
def prefixEnd_426825 : Nat := 4983230072969 + 3 ^ 40 * 426825 * 2
def baseEnd_426825 : Nat := 194814560315909136821843

theorem tailTrace_426825 : CollatzResearch.WordTrace tailWord_426825 prefixEnd_426825 194814560315909136821843 := by
  unfold tailWord_426825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15567586678693395751569929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10378391119128930501046619 15567586678693395751569929)
  ·
    refine ⟨11675690009020046813677447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15567586678693395751569929 11675690009020046813677447)
    ·
      refine ⟨17513535013530070220516171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675690009020046813677447 17513535013530070220516171)
      ·
        refine ⟨26270302520295105330774257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17513535013530070220516171 26270302520295105330774257)
        ·
          refine ⟨19702726890221328998080693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26270302520295105330774257 19702726890221328998080693)
          ·
            refine ⟨1847130645958249593570065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19702726890221328998080693 1847130645958249593570065)
            ·
              refine ⟨1385347984468687195177549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847130645958249593570065 1385347984468687195177549)
              ·
                refine ⟨519505494175757698191581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385347984468687195177549 519505494175757698191581)
                ·
                  refine ⟨194814560315909136821843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519505494175757698191581 194814560315909136821843)
                  ·
                    rfl

theorem cell20_426825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_426825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426825 prefixEnd_426825 := by exact prefixLift 426825
  have htrace : WordTrace (prefixWord ++ tailWord_426825) baseStart_426825 baseEnd_426825 := by
    simpa [prefixWord, tailWord_426825, baseEnd_426825] using wordTrace_append hprefix tailTrace_426825
  have hstable : (prefixWord ++ tailWord_426825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426825).length < 2 ^ (prefixWord ++ tailWord_426825).sum := by decide
  have hdescent : baseEnd_426825 < baseStart_426825 := by decide
  rcases family_descends (prefixWord ++ tailWord_426825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426967 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_426967 : Nat := 118140960795 + 426967 * 2 ^ 59
def prefixEnd_426967 : Nat := 4983230072969 + 3 ^ 40 * 426967 * 2
def baseEnd_426967 : Nat := 194879372985187754087929

theorem tailTrace_426967 : CollatzResearch.WordTrace tailWord_426967 prefixEnd_426967 194879372985187754087929 := by
  unfold tailWord_426967
  simp only [CollatzResearch.WordTrace]
  refine ⟨15572765844178954003239155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10381843896119302668826103 15572765844178954003239155)
  ·
    refine ⟨23359148766268431004858733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15572765844178954003239155 23359148766268431004858733)
    ·
      refine ⟨8759680787350661626822025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23359148766268431004858733 8759680787350661626822025)
      ·
        refine ⟨6569760590512996220116519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8759680787350661626822025 6569760590512996220116519)
        ·
          refine ⟨9854640885769494330174779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569760590512996220116519 9854640885769494330174779)
          ·
            refine ⟨14781961328654241495262169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854640885769494330174779 14781961328654241495262169)
            ·
              refine ⟨11086470996490681121446627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14781961328654241495262169 11086470996490681121446627)
              ·
                refine ⟨16629706494736021682169941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11086470996490681121446627 16629706494736021682169941)
                ·
                  refine ⟨194879372985187754087929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16629706494736021682169941 194879372985187754087929)
                  ·
                    rfl

theorem cell20_426967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_426967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426967 prefixEnd_426967 := by exact prefixLift 426967
  have htrace : WordTrace (prefixWord ++ tailWord_426967) baseStart_426967 baseEnd_426967 := by
    simpa [prefixWord, tailWord_426967, baseEnd_426967] using wordTrace_append hprefix tailTrace_426967
  have hstable : (prefixWord ++ tailWord_426967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426967).length < 2 ^ (prefixWord ++ tailWord_426967).sum := by decide
  have hdescent : baseEnd_426967 < baseStart_426967 := by decide
  rcases family_descends (prefixWord ++ tailWord_426967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426991 : List Nat := [1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_426991 : Nat := 118140960795 + 426991 * 2 ^ 59
def prefixEnd_426991 : Nat := 4983230072969 + 3 ^ 40 * 426991 * 2
def baseEnd_426991 : Nat := 64963442413050112429277

theorem tailTrace_426991 : CollatzResearch.WordTrace tailWord_426991 prefixEnd_426991 64963442413050112429277 := by
  unfold tailWord_426991
  simp only [CollatzResearch.WordTrace]
  refine ⟨15573641196092006102112827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10382427464061337401408551 15573641196092006102112827)
  ·
    refine ⟨23360461794138009153169241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15573641196092006102112827 23360461794138009153169241)
    ·
      refine ⟨17520346345603506864876931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23360461794138009153169241 17520346345603506864876931)
      ·
        refine ⟨26280519518405260297315397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17520346345603506864876931 26280519518405260297315397)
        ·
          refine ⟨4927597409700986305746637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26280519518405260297315397 4927597409700986305746637)
          ·
            refine ⟨1847849028637869864654989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4927597409700986305746637 1847849028637869864654989)
            ·
              refine ⟨692943385739201199245621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847849028637869864654989 692943385739201199245621)
              ·
                refine ⟨64963442413050112429277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692943385739201199245621 64963442413050112429277)
                ·
                  rfl

theorem cell20_426991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_426991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_426991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_426991 prefixEnd_426991 := by exact prefixLift 426991
  have htrace : WordTrace (prefixWord ++ tailWord_426991) baseStart_426991 baseEnd_426991 := by
    simpa [prefixWord, tailWord_426991, baseEnd_426991] using wordTrace_append hprefix tailTrace_426991
  have hstable : (prefixWord ++ tailWord_426991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426991).length < 2 ^ (prefixWord ++ tailWord_426991).sum := by decide
  have hdescent : baseEnd_426991 < baseStart_426991 := by decide
  rcases family_descends (prefixWord ++ tailWord_426991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427018 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_427018 : Nat := 118140960795 + 427018 * 2 ^ 59
def prefixEnd_427018 : Nat := 4983230072969 + 3 ^ 40 * 427018 * 2
def baseEnd_427018 : Nat := 194902650774858243387721

theorem tailTrace_427018 : CollatzResearch.WordTrace tailWord_427018 prefixEnd_427018 194902650774858243387721 := by
  unfold tailWord_427018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893656491748547428336427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10383083977996126475563805 3893656491748547428336427)
  ·
    refine ⟨5840484737622821142504641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893656491748547428336427 5840484737622821142504641)
    ·
      refine ⟨4380363553217115856878481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5840484737622821142504641 4380363553217115856878481)
      ·
        refine ⟨3285272664912836892658861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4380363553217115856878481 3285272664912836892658861)
        ·
          refine ⟨1231977249342313834747073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3285272664912836892658861 1231977249342313834747073)
          ·
            refine ⟨923982937006735376060305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231977249342313834747073 923982937006735376060305)
            ·
              refine ⟨692987202755051532045229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923982937006735376060305 692987202755051532045229)
              ·
                refine ⟨259870201033144324516961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692987202755051532045229 259870201033144324516961)
                ·
                  refine ⟨194902650774858243387721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259870201033144324516961 194902650774858243387721)
                  ·
                    rfl

theorem cell20_427018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_427018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427018 prefixEnd_427018 := by exact prefixLift 427018
  have htrace : WordTrace (prefixWord ++ tailWord_427018) baseStart_427018 baseEnd_427018 := by
    simpa [prefixWord, tailWord_427018, baseEnd_427018] using wordTrace_append hprefix tailTrace_427018
  have hstable : (prefixWord ++ tailWord_427018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427018).length < 2 ^ (prefixWord ++ tailWord_427018).sum := by decide
  have hdescent : baseEnd_427018 < baseStart_427018 := by decide
  rcases family_descends (prefixWord ++ tailWord_427018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427029 : List Nat := [1, 3, 2, 1, 4, 2, 7]
def baseStart_427029 : Nat := 118140960795 + 427029 * 2 ^ 59
def prefixEnd_427029 : Nat := 4983230072969 + 3 ^ 40 * 427029 * 2
def baseEnd_427029 : Nat := 21656407941621232669001

theorem tailTrace_427029 : CollatzResearch.WordTrace tailWord_427029 prefixEnd_427029 21656407941621232669001 := by
  unfold tailWord_427029
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575027169954338591996141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10383351446636225727997427 15575027169954338591996141)
  ·
    refine ⟨5840635188732876971998553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15575027169954338591996141 5840635188732876971998553)
    ·
      refine ⟨4380476391549657728998915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5840635188732876971998553 4380476391549657728998915)
      ·
        refine ⟨6570714587324486593498373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380476391549657728998915 6570714587324486593498373)
        ·
          refine ⟨1232008985123341236280945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6570714587324486593498373 1232008985123341236280945)
          ·
            refine ⟨924006738842505927210709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232008985123341236280945 924006738842505927210709)
            ·
              refine ⟨21656407941621232669001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 924006738842505927210709 21656407941621232669001)
              ·
                rfl

theorem cell20_427029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_427029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427029 prefixEnd_427029 := by exact prefixLift 427029
  have htrace : WordTrace (prefixWord ++ tailWord_427029) baseStart_427029 baseEnd_427029 := by
    simpa [prefixWord, tailWord_427029, baseEnd_427029] using wordTrace_append hprefix tailTrace_427029
  have hstable : (prefixWord ++ tailWord_427029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427029).length < 2 ^ (prefixWord ++ tailWord_427029).sum := by decide
  have hdescent : baseEnd_427029 < baseStart_427029 := by decide
  rcases family_descends (prefixWord ++ tailWord_427029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427032 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_427032 : Nat := 118140960795 + 427032 * 2 ^ 59
def prefixEnd_427032 : Nat := 4983230072969 + 3 ^ 40 * 427032 * 2
def baseEnd_427032 : Nat := 194909040756336416920997

theorem tailTrace_427032 : CollatzResearch.WordTrace tailWord_427032 prefixEnd_427032 194909040756336416920997 := by
  unfold tailWord_427032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787568294471735052177675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10383424392628980069570233 7787568294471735052177675)
  ·
    refine ⟨11681352441707602578266513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7787568294471735052177675 11681352441707602578266513)
    ·
      refine ⟨8761014331280701933699885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11681352441707602578266513 8761014331280701933699885)
      ·
        refine ⟨3285380374230263225137457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8761014331280701933699885 3285380374230263225137457)
        ·
          refine ⟨2464035280672697418853093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3285380374230263225137457 2464035280672697418853093)
          ·
            refine ⟨462006615126130766034955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2464035280672697418853093 462006615126130766034955)
            ·
              refine ⟨693009922689196149052433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462006615126130766034955 693009922689196149052433)
              ·
                refine ⟨519757442016897111789325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693009922689196149052433 519757442016897111789325)
                ·
                  refine ⟨194909040756336416920997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519757442016897111789325 194909040756336416920997)
                  ·
                    rfl

theorem cell20_427032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_427032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427032 prefixEnd_427032 := by exact prefixLift 427032
  have htrace : WordTrace (prefixWord ++ tailWord_427032) baseStart_427032 baseEnd_427032 := by
    simpa [prefixWord, tailWord_427032, baseEnd_427032] using wordTrace_append hprefix tailTrace_427032
  have hstable : (prefixWord ++ tailWord_427032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427032).length < 2 ^ (prefixWord ++ tailWord_427032).sum := by decide
  have hdescent : baseEnd_427032 < baseStart_427032 := by decide
  rcases family_descends (prefixWord ++ tailWord_427032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427039 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 2]
def baseStart_427039 : Nat := 118140960795 + 427039 * 2 ^ 59
def prefixEnd_427039 : Nat := 4983230072969 + 3 ^ 40 * 427039 * 2
def baseEnd_427039 : Nat := 194912235747075503687635

theorem tailTrace_427039 : CollatzResearch.WordTrace tailWord_427039 prefixEnd_427039 194912235747075503687635 := by
  unfold tailWord_427039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575391899918110299860171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10383594599945406866573447 15575391899918110299860171)
  ·
    refine ⟨23363087849877165449790257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15575391899918110299860171 23363087849877165449790257)
    ·
      refine ⟨17522315887407874087342693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23363087849877165449790257 17522315887407874087342693)
      ·
        refine ⟨3285434228888976391376755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17522315887407874087342693 3285434228888976391376755)
        ·
          refine ⟨4928151343333464587065133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285434228888976391376755 4928151343333464587065133)
          ·
            refine ⟨1848056753750049220149425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4928151343333464587065133 1848056753750049220149425)
            ·
              refine ⟨1386042565312536915112069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848056753750049220149425 1386042565312536915112069)
              ·
                refine ⟨259882980996100671583513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1386042565312536915112069 259882980996100671583513)
                ·
                  refine ⟨194912235747075503687635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259882980996100671583513 194912235747075503687635)
                  ·
                    rfl

theorem cell20_427039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2].length) (baseStart_427039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427039 prefixEnd_427039 := by exact prefixLift 427039
  have htrace : WordTrace (prefixWord ++ tailWord_427039) baseStart_427039 baseEnd_427039 := by
    simpa [prefixWord, tailWord_427039, baseEnd_427039] using wordTrace_append hprefix tailTrace_427039
  have hstable : (prefixWord ++ tailWord_427039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427039).length < 2 ^ (prefixWord ++ tailWord_427039).sum := by decide
  have hdescent : baseEnd_427039 < baseStart_427039 := by decide
  rcases family_descends (prefixWord ++ tailWord_427039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427073 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 2]
def baseStart_427073 : Nat := 118140960795 + 427073 * 2 ^ 59
def prefixEnd_427073 : Nat := 4983230072969 + 3 ^ 40 * 427073 * 2
def baseEnd_427073 : Nat := 194927754273522496554163

theorem tailTrace_427073 : CollatzResearch.WordTrace tailWord_427073 prefixEnd_427073 194927754273522496554163 := by
  unfold tailWord_427073
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576631981794934106597873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10384421321196622737731915 15576631981794934106597873)
  ·
    refine ⟨11682473986346200579948405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15576631981794934106597873 11682473986346200579948405)
    ·
      refine ⟨1095231936219956304370163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11682473986346200579948405 1095231936219956304370163)
      ·
        refine ⟨1642847904329934456555245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095231936219956304370163 1642847904329934456555245)
        ·
          refine ⟨616067964123725421208217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1642847904329934456555245 616067964123725421208217)
          ·
            refine ⟨462050973092794065906163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616067964123725421208217 462050973092794065906163)
            ·
              refine ⟨693076459639191098859245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462050973092794065906163 693076459639191098859245)
              ·
                refine ⟨259903672364696662072217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693076459639191098859245 259903672364696662072217)
                ·
                  refine ⟨194927754273522496554163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259903672364696662072217 194927754273522496554163)
                  ·
                    rfl

theorem cell20_427073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_427073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427073 prefixEnd_427073 := by exact prefixLift 427073
  have htrace : WordTrace (prefixWord ++ tailWord_427073) baseStart_427073 baseEnd_427073 := by
    simpa [prefixWord, tailWord_427073, baseEnd_427073] using wordTrace_append hprefix tailTrace_427073
  have hstable : (prefixWord ++ tailWord_427073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427073).length < 2 ^ (prefixWord ++ tailWord_427073).sum := by decide
  have hdescent : baseEnd_427073 < baseStart_427073 := by decide
  rcases family_descends (prefixWord ++ tailWord_427073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427077 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 2]
def baseStart_427077 : Nat := 118140960795 + 427077 * 2 ^ 59
def prefixEnd_427077 : Nat := 4983230072969 + 3 ^ 40 * 427077 * 2
def baseEnd_427077 : Nat := 194929579982516260420813

theorem tailTrace_427077 : CollatzResearch.WordTrace tailWord_427077 prefixEnd_427077 194929579982516260420813 := by
  unfold tailWord_427077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576777873780442789743485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10384518582520295193162323 15576777873780442789743485)
  ·
    refine ⟨5841291702667666046153807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15576777873780442789743485 5841291702667666046153807)
    ·
      refine ⟨8761937554001499069230711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841291702667666046153807 8761937554001499069230711)
      ·
        refine ⟨13142906331002248603846067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761937554001499069230711 13142906331002248603846067)
        ·
          refine ⟨19714359496503372905769101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13142906331002248603846067 19714359496503372905769101)
          ·
            refine ⟨7392884811188764839663413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19714359496503372905769101 7392884811188764839663413)
            ·
              refine ⟨693082951048946703718445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7392884811188764839663413 693082951048946703718445)
              ·
                refine ⟨259906106643355013894417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693082951048946703718445 259906106643355013894417)
                ·
                  refine ⟨194929579982516260420813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259906106643355013894417 194929579982516260420813)
                  ·
                    rfl

theorem cell20_427077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_427077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427077 prefixEnd_427077 := by exact prefixLift 427077
  have htrace : WordTrace (prefixWord ++ tailWord_427077) baseStart_427077 baseEnd_427077 := by
    simpa [prefixWord, tailWord_427077, baseEnd_427077] using wordTrace_append hprefix tailTrace_427077
  have hstable : (prefixWord ++ tailWord_427077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427077).length < 2 ^ (prefixWord ++ tailWord_427077).sum := by decide
  have hdescent : baseEnd_427077 < baseStart_427077 := by decide
  rcases family_descends (prefixWord ++ tailWord_427077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427101 : List Nat := [1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_427101 : Nat := 118140960795 + 427101 * 2 ^ 59
def prefixEnd_427101 : Nat := 4983230072969 + 3 ^ 40 * 427101 * 2
def baseEnd_427101 : Nat := 64980178078826281206905

theorem tailTrace_427101 : CollatzResearch.WordTrace tailWord_427101 prefixEnd_427101 64980178078826281206905 := by
  unfold tailWord_427101
  simp only [CollatzResearch.WordTrace]
  refine ⟨15577653225693494888617157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10385102150462329925744771 15577653225693494888617157)
  ·
    refine ⟨2920809979817530291615717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15577653225693494888617157 2920809979817530291615717)
    ·
      refine ⟨547651871215786929677947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2920809979817530291615717 547651871215786929677947)
      ·
        refine ⟨821477806823680394516921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547651871215786929677947 821477806823680394516921)
        ·
          refine ⟨616108355117760295887691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821477806823680394516921 616108355117760295887691)
          ·
            refine ⟨924162532676640443831537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616108355117760295887691 924162532676640443831537)
            ·
              refine ⟨693121899507480332873653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924162532676640443831537 693121899507480332873653)
              ·
                refine ⟨64980178078826281206905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 693121899507480332873653 64980178078826281206905)
                ·
                  rfl

theorem cell20_427101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_427101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427101 prefixEnd_427101 := by exact prefixLift 427101
  have htrace : WordTrace (prefixWord ++ tailWord_427101) baseStart_427101 baseEnd_427101 := by
    simpa [prefixWord, tailWord_427101, baseEnd_427101] using wordTrace_append hprefix tailTrace_427101
  have hstable : (prefixWord ++ tailWord_427101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427101).length < 2 ^ (prefixWord ++ tailWord_427101).sum := by decide
  have hdescent : baseEnd_427101 < baseStart_427101 := by decide
  rcases family_descends (prefixWord ++ tailWord_427101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427119 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_427119 : Nat := 118140960795 + 427119 * 2 ^ 59
def prefixEnd_427119 : Nat := 4983230072969 + 3 ^ 40 * 427119 * 2
def baseEnd_427119 : Nat := 194948749926950781020641

theorem tailTrace_427119 : CollatzResearch.WordTrace tailWord_427119 prefixEnd_427119 194948749926950781020641 := by
  unfold tailWord_427119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578309739628283962772411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10385539826418855975181607 15578309739628283962772411)
  ·
    refine ⟨23367464609442425944158617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15578309739628283962772411 23367464609442425944158617)
    ·
      refine ⟨17525598457081819458118963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23367464609442425944158617 17525598457081819458118963)
      ·
        refine ⟨26288397685622729187178445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17525598457081819458118963 26288397685622729187178445)
        ·
          refine ⟨9858149132108523445191917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26288397685622729187178445 9858149132108523445191917)
          ·
            refine ⟨3696805924540696291946969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9858149132108523445191917 3696805924540696291946969)
            ·
              refine ⟨2772604443405522218960227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696805924540696291946969 2772604443405522218960227)
              ·
                refine ⟨4158906665108283328440341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772604443405522218960227 4158906665108283328440341)
                ·
                  refine ⟨194948749926950781020641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158906665108283328440341 194948749926950781020641)
                  ·
                    rfl

theorem cell20_427119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_427119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427119 prefixEnd_427119 := by exact prefixLift 427119
  have htrace : WordTrace (prefixWord ++ tailWord_427119) baseStart_427119 baseEnd_427119 := by
    simpa [prefixWord, tailWord_427119, baseEnd_427119] using wordTrace_append hprefix tailTrace_427119
  have hstable : (prefixWord ++ tailWord_427119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427119).length < 2 ^ (prefixWord ++ tailWord_427119).sum := by decide
  have hdescent : baseEnd_427119 < baseStart_427119 := by decide
  rcases family_descends (prefixWord ++ tailWord_427119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427160 : List Nat := [2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_427160 : Nat := 118140960795 + 427160 * 2 ^ 59
def prefixEnd_427160 : Nat := 4983230072969 + 3 ^ 40 * 427160 * 2
def baseEnd_427160 : Nat := 64989154481378953551269

theorem tailTrace_427160 : CollatzResearch.WordTrace tailWord_427160 prefixEnd_427160 64989154481378953551269 := by
  unfold tailWord_427160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789902566239873982507467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10386536754986498643343289 7789902566239873982507467)
  ·
    refine ⟨11684853849359810973761201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789902566239873982507467 11684853849359810973761201)
    ·
      refine ⟨8763640387019858230320901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11684853849359810973761201 8763640387019858230320901)
      ·
        refine ⟨1643182572566223418185169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8763640387019858230320901 1643182572566223418185169)
        ·
          refine ⟨1232386929424667563638877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643182572566223418185169 1232386929424667563638877)
          ·
            refine ⟨462145098534250336364579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232386929424667563638877 462145098534250336364579)
            ·
              refine ⟨693217647801375504546869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462145098534250336364579 693217647801375504546869)
              ·
                refine ⟨64989154481378953551269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 693217647801375504546869 64989154481378953551269)
                ·
                  rfl

theorem cell20_427160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_427160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427160 prefixEnd_427160 := by exact prefixLift 427160
  have htrace : WordTrace (prefixWord ++ tailWord_427160) baseStart_427160 baseEnd_427160 := by
    simpa [prefixWord, tailWord_427160, baseEnd_427160] using wordTrace_append hprefix tailTrace_427160
  have hstable : (prefixWord ++ tailWord_427160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427160).length < 2 ^ (prefixWord ++ tailWord_427160).sum := by decide
  have hdescent : baseEnd_427160 < baseStart_427160 := by decide
  rcases family_descends (prefixWord ++ tailWord_427160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427191 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 2]
def baseStart_427191 : Nat := 118140960795 + 427191 * 2 ^ 59
def prefixEnd_427191 : Nat := 4983230072969 + 3 ^ 40 * 427191 * 2
def baseEnd_427191 : Nat := 194981612688838530620347

theorem tailTrace_427191 : CollatzResearch.WordTrace tailWord_427191 prefixEnd_427191 194981612688838530620347 := by
  unfold tailWord_427191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580935795367440259393427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10387290530244960172928951 15580935795367440259393427)
  ·
    refine ⟨23371403693051160389090141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15580935795367440259393427 23371403693051160389090141)
    ·
      refine ⟨8764276384894185145908803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23371403693051160389090141 8764276384894185145908803)
      ·
        refine ⟨13146414577341277718863205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8764276384894185145908803 13146414577341277718863205)
        ·
          refine ⟨2464952733251489572286851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13146414577341277718863205 2464952733251489572286851)
          ·
            refine ⟨3697429099877234358430277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464952733251489572286851 3697429099877234358430277)
            ·
              refine ⟨693267956226981442205677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3697429099877234358430277 693267956226981442205677)
              ·
                refine ⟨259975483585118040827129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693267956226981442205677 259975483585118040827129)
                ·
                  refine ⟨194981612688838530620347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259975483585118040827129 194981612688838530620347)
                  ·
                    rfl

theorem cell20_427191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2].length) (baseStart_427191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427191 prefixEnd_427191 := by exact prefixLift 427191
  have htrace : WordTrace (prefixWord ++ tailWord_427191) baseStart_427191 baseEnd_427191 := by
    simpa [prefixWord, tailWord_427191, baseEnd_427191] using wordTrace_append hprefix tailTrace_427191
  have hstable : (prefixWord ++ tailWord_427191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427191).length < 2 ^ (prefixWord ++ tailWord_427191).sum := by decide
  have hdescent : baseEnd_427191 < baseStart_427191 := by decide
  rcases family_descends (prefixWord ++ tailWord_427191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427201 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_427201 : Nat := 118140960795 + 427201 * 2 ^ 59
def prefixEnd_427201 : Nat := 4983230072969 + 3 ^ 40 * 427201 * 2
def baseEnd_427201 : Nat := 194986176961322940286973

theorem tailTrace_427201 : CollatzResearch.WordTrace tailWord_427201 prefixEnd_427201 194986176961322940286973 := by
  unfold tailWord_427201
  simp only [CollatzResearch.WordTrace]
  refine ⟨15581300525331211967257457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10387533683554141311504971 15581300525331211967257457)
  ·
    refine ⟨11685975393998408975443093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15581300525331211967257457 11685975393998408975443093)
    ·
      refine ⟨547780096593675420723895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11685975393998408975443093 547780096593675420723895)
      ·
        refine ⟨821670144890513131085843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547780096593675420723895 821670144890513131085843)
        ·
          refine ⟨1232505217335769696628765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821670144890513131085843 1232505217335769696628765)
          ·
            refine ⟨462189456500913636235787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232505217335769696628765 462189456500913636235787)
            ·
              refine ⟨693284184751370454353681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462189456500913636235787 693284184751370454353681)
              ·
                refine ⟨519963138563527840765261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693284184751370454353681 519963138563527840765261)
                ·
                  refine ⟨194986176961322940286973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519963138563527840765261 194986176961322940286973)
                  ·
                    rfl

theorem cell20_427201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_427201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427201 prefixEnd_427201 := by exact prefixLift 427201
  have htrace : WordTrace (prefixWord ++ tailWord_427201) baseStart_427201 baseEnd_427201 := by
    simpa [prefixWord, tailWord_427201, baseEnd_427201] using wordTrace_append hprefix tailTrace_427201
  have hstable : (prefixWord ++ tailWord_427201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427201).length < 2 ^ (prefixWord ++ tailWord_427201).sum := by decide
  have hdescent : baseEnd_427201 < baseStart_427201 := by decide
  rcases family_descends (prefixWord ++ tailWord_427201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427264 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_427264 : Nat := 118140960795 + 427264 * 2 ^ 59
def prefixEnd_427264 : Nat := 4983230072969 + 3 ^ 40 * 427264 * 2
def baseEnd_427264 : Nat := 195014931877974721186715

theorem tailTrace_427264 : CollatzResearch.WordTrace tailWord_427264 prefixEnd_427264 195014931877974721186715 := by
  unfold tailWord_427264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791799162051486863400423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10389065549401982484533897 7791799162051486863400423)
  ·
    refine ⟨11687698743077230295100635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7791799162051486863400423 11687698743077230295100635)
    ·
      refine ⟨17531548114615845442650953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11687698743077230295100635 17531548114615845442650953)
      ·
        refine ⟨13148661085961884081988215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17531548114615845442650953 13148661085961884081988215)
        ·
          refine ⟨19722991628942826122982323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13148661085961884081988215 19722991628942826122982323)
          ·
            refine ⟨29584487443414239184473485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19722991628942826122982323 29584487443414239184473485)
            ·
              refine ⟨11094182791280339694177557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29584487443414239184473485 11094182791280339694177557)
              ·
                refine ⟨520039818341265923164573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11094182791280339694177557 520039818341265923164573)
                ·
                  refine ⟨195014931877974721186715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520039818341265923164573 195014931877974721186715)
                  ·
                    rfl

theorem cell20_427264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_427264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427264 prefixEnd_427264 := by exact prefixLift 427264
  have htrace : WordTrace (prefixWord ++ tailWord_427264) baseStart_427264 baseEnd_427264 := by
    simpa [prefixWord, tailWord_427264, baseEnd_427264] using wordTrace_append hprefix tailTrace_427264
  have hstable : (prefixWord ++ tailWord_427264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427264).length < 2 ^ (prefixWord ++ tailWord_427264).sum := by decide
  have hdescent : baseEnd_427264 < baseStart_427264 := by decide
  rcases family_descends (prefixWord ++ tailWord_427264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427323 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_427323 : Nat := 118140960795 + 427323 * 2 ^ 59
def prefixEnd_427323 : Nat := 4983230072969 + 3 ^ 40 * 427323 * 2
def baseEnd_427323 : Nat := 195041861085632738219807

theorem tailTrace_427323 : CollatzResearch.WordTrace tailWord_427323 prefixEnd_427323 195041861085632738219807 := by
  unfold tailWord_427323
  simp only [CollatzResearch.WordTrace]
  refine ⟨15585750230889226803198623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10390500153926151202132415 15585750230889226803198623)
  ·
    refine ⟨23378625346333840204797935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15585750230889226803198623 23378625346333840204797935)
    ·
      refine ⟨35067938019500760307196903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23378625346333840204797935 35067938019500760307196903)
      ·
        refine ⟨52601907029251140460795355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35067938019500760307196903 52601907029251140460795355)
        ·
          refine ⟨78902860543876710691193033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52601907029251140460795355 78902860543876710691193033)
          ·
            refine ⟨59177145407907533018394775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78902860543876710691193033 59177145407907533018394775)
            ·
              refine ⟨88765718111861299527592163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59177145407907533018394775 88765718111861299527592163)
              ·
                refine ⟨133148577167791949291388245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88765718111861299527592163 133148577167791949291388245)
                ·
                  refine ⟨195041861085632738219807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 133148577167791949291388245 195041861085632738219807)
                  ·
                    rfl

theorem cell20_427323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_427323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427323 prefixEnd_427323 := by exact prefixLift 427323
  have htrace : WordTrace (prefixWord ++ tailWord_427323) baseStart_427323 baseEnd_427323 := by
    simpa [prefixWord, tailWord_427323, baseEnd_427323] using wordTrace_append hprefix tailTrace_427323
  have hstable : (prefixWord ++ tailWord_427323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427323).length < 2 ^ (prefixWord ++ tailWord_427323).sum := by decide
  have hdescent : baseEnd_427323 < baseStart_427323 := by decide
  rcases family_descends (prefixWord ++ tailWord_427323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427326 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_427326 : Nat := 118140960795 + 427326 * 2 ^ 59
def prefixEnd_427326 : Nat := 4983230072969 + 3 ^ 40 * 427326 * 2
def baseEnd_427326 : Nat := 195043230367378061119795

theorem tailTrace_427326 : CollatzResearch.WordTrace tailWord_427326 prefixEnd_427326 195043230367378061119795 := by
  unfold tailWord_427326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948232456234794789444729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10390573099918905543705221 1948232456234794789444729)
  ·
    refine ⟨1461174342176096092083547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1948232456234794789444729 1461174342176096092083547)
    ·
      refine ⟨2191761513264144138125321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461174342176096092083547 2191761513264144138125321)
      ·
        refine ⟨1643821134948108103593991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191761513264144138125321 1643821134948108103593991)
        ·
          refine ⟨2465731702422162155390987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643821134948108103593991 2465731702422162155390987)
          ·
            refine ⟨3698597553633243233086481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465731702422162155390987 3698597553633243233086481)
            ·
              refine ⟨2773948165224932424814861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698597553633243233086481 2773948165224932424814861)
              ·
                refine ⟨1040230561959349659305573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773948165224932424814861 1040230561959349659305573)
                ·
                  refine ⟨195043230367378061119795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040230561959349659305573 195043230367378061119795)
                  ·
                    rfl

theorem cell20_427326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_427326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427326 prefixEnd_427326 := by exact prefixLift 427326
  have htrace : WordTrace (prefixWord ++ tailWord_427326) baseStart_427326 baseEnd_427326 := by
    simpa [prefixWord, tailWord_427326, baseEnd_427326] using wordTrace_append hprefix tailTrace_427326
  have hstable : (prefixWord ++ tailWord_427326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427326).length < 2 ^ (prefixWord ++ tailWord_427326).sum := by decide
  have hdescent : baseEnd_427326 < baseStart_427326 := by decide
  rcases family_descends (prefixWord ++ tailWord_427326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427347 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_427347 : Nat := 118140960795 + 427347 * 2 ^ 59
def prefixEnd_427347 : Nat := 4983230072969 + 3 ^ 40 * 427347 * 2
def baseEnd_427347 : Nat := 195052815339595321419709

theorem tailTrace_427347 : CollatzResearch.WordTrace tailWord_427347 prefixEnd_427347 195052815339595321419709 := by
  unfold tailWord_427347
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586625582802278902072295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10391083721868185934714863 15586625582802278902072295)
  ·
    refine ⟨23379938374203418353108443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15586625582802278902072295 23379938374203418353108443)
    ·
      refine ⟨35069907561305127529662665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23379938374203418353108443 35069907561305127529662665)
      ·
        refine ⟨26302430670978845647246999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35069907561305127529662665 26302430670978845647246999)
        ·
          refine ⟨39453646006468268470870499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26302430670978845647246999 39453646006468268470870499)
          ·
            refine ⟨59180469009702402706305749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39453646006468268470870499 59180469009702402706305749)
            ·
              refine ⟨1387042242414900063429041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59180469009702402706305749 1387042242414900063429041)
              ·
                refine ⟨1040281681811175047571781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387042242414900063429041 1040281681811175047571781)
                ·
                  refine ⟨195052815339595321419709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040281681811175047571781 195052815339595321419709)
                  ·
                    rfl

theorem cell20_427347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_427347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427347 prefixEnd_427347 := by exact prefixLift 427347
  have htrace : WordTrace (prefixWord ++ tailWord_427347) baseStart_427347 baseEnd_427347 := by
    simpa [prefixWord, tailWord_427347, baseEnd_427347] using wordTrace_append hprefix tailTrace_427347
  have hstable : (prefixWord ++ tailWord_427347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427347).length < 2 ^ (prefixWord ++ tailWord_427347).sum := by decide
  have hdescent : baseEnd_427347 < baseStart_427347 := by decide
  rcases family_descends (prefixWord ++ tailWord_427347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427354 : List Nat := [3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_427354 : Nat := 118140960795 + 427354 * 2 ^ 59
def prefixEnd_427354 : Nat := 4983230072969 + 3 ^ 40 * 427354 * 2
def baseEnd_427354 : Nat := 65018670110111469395449

theorem tailTrace_427354 : CollatzResearch.WordTrace tailWord_427354 prefixEnd_427354 65018670110111469395449 := by
  unfold tailWord_427354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896720223444229774394279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10391253929184612731718077 3896720223444229774394279)
  ·
    refine ⟨5845080335166344661591419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3896720223444229774394279 5845080335166344661591419)
    ·
      refine ⟨8767620502749516992387129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845080335166344661591419 8767620502749516992387129)
      ·
        refine ⟨6575715377062137744290347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8767620502749516992387129 6575715377062137744290347)
        ·
          refine ⟨9863573065593206616435521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575715377062137744290347 9863573065593206616435521)
          ·
            refine ⟨7397679799194904962326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9863573065593206616435521 7397679799194904962326641)
            ·
              refine ⟨5548259849396178721744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7397679799194904962326641 5548259849396178721744981)
              ·
                refine ⟨65018670110111469395449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5548259849396178721744981 65018670110111469395449)
                ·
                  rfl

theorem cell20_427354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_427354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427354 prefixEnd_427354 := by exact prefixLift 427354
  have htrace : WordTrace (prefixWord ++ tailWord_427354) baseStart_427354 baseEnd_427354 := by
    simpa [prefixWord, tailWord_427354, baseEnd_427354] using wordTrace_append hprefix tailTrace_427354
  have hstable : (prefixWord ++ tailWord_427354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427354).length < 2 ^ (prefixWord ++ tailWord_427354).sum := by decide
  have hdescent : baseEnd_427354 < baseStart_427354 := by decide
  rcases family_descends (prefixWord ++ tailWord_427354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427374 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_427374 : Nat := 118140960795 + 427374 * 2 ^ 59
def prefixEnd_427374 : Nat := 4983230072969 + 3 ^ 40 * 427374 * 2
def baseEnd_427374 : Nat := 195065138875303227519599

theorem tailTrace_427374 : CollatzResearch.WordTrace tailWord_427374 prefixEnd_427374 195065138875303227519599 := by
  unfold tailWord_427374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948451294213057814163147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10391740235802975008870117 1948451294213057814163147)
  ·
    refine ⟨2922676941319586721244721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948451294213057814163147 2922676941319586721244721)
    ·
      refine ⟨2192007705989690040933541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2922676941319586721244721 2192007705989690040933541)
      ·
        refine ⟨411001444873066882675039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2192007705989690040933541 411001444873066882675039)
        ·
          refine ⟨616502167309600324012559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411001444873066882675039 616502167309600324012559)
          ·
            refine ⟨924753250964400486018839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616502167309600324012559 924753250964400486018839)
            ·
              refine ⟨1387129876446600729028259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924753250964400486018839 1387129876446600729028259)
              ·
                refine ⟨2080694814669901093542389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387129876446600729028259 2080694814669901093542389)
                ·
                  refine ⟨195065138875303227519599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080694814669901093542389 195065138875303227519599)
                  ·
                    rfl

theorem cell20_427374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_427374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427374 prefixEnd_427374 := by exact prefixLift 427374
  have htrace : WordTrace (prefixWord ++ tailWord_427374) baseStart_427374 baseEnd_427374 := by
    simpa [prefixWord, tailWord_427374, baseEnd_427374] using wordTrace_append hprefix tailTrace_427374
  have hstable : (prefixWord ++ tailWord_427374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427374).length < 2 ^ (prefixWord ++ tailWord_427374).sum := by decide
  have hdescent : baseEnd_427374 < baseStart_427374 := by decide
  rcases family_descends (prefixWord ++ tailWord_427374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427378 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_427378 : Nat := 118140960795 + 427378 * 2 ^ 59
def prefixEnd_427378 : Nat := 4983230072969 + 3 ^ 40 * 427378 * 2
def baseEnd_427378 : Nat := 195066964584296991386249

theorem tailTrace_427378 : CollatzResearch.WordTrace tailWord_427378 prefixEnd_427378 195066964584296991386249 := by
  unfold tailWord_427378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896939061422492799112697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10391837497126647464300525 3896939061422492799112697)
  ·
    refine ⟨2922704296066869599334523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3896939061422492799112697 2922704296066869599334523)
    ·
      refine ⟨4384056444100304399001785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922704296066869599334523 4384056444100304399001785)
      ·
        refine ⟨3288042333075228299251339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4384056444100304399001785 3288042333075228299251339)
        ·
          refine ⟨4932063499612842448877009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288042333075228299251339 4932063499612842448877009)
          ·
            refine ⟨3699047624709631836657757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4932063499612842448877009 3699047624709631836657757)
            ·
              refine ⟨1387142859266111938746659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3699047624709631836657757 1387142859266111938746659)
              ·
                refine ⟨2080714288899167908119989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387142859266111938746659 2080714288899167908119989)
                ·
                  refine ⟨195066964584296991386249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080714288899167908119989 195066964584296991386249)
                  ·
                    rfl

theorem cell20_427378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_427378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427378 prefixEnd_427378 := by exact prefixLift 427378
  have htrace : WordTrace (prefixWord ++ tailWord_427378) baseStart_427378 baseEnd_427378 := by
    simpa [prefixWord, tailWord_427378, baseEnd_427378] using wordTrace_append hprefix tailTrace_427378
  have hstable : (prefixWord ++ tailWord_427378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427378).length < 2 ^ (prefixWord ++ tailWord_427378).sum := by decide
  have hdescent : baseEnd_427378 < baseStart_427378 := by decide
  rcases family_descends (prefixWord ++ tailWord_427378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427381 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_427381 : Nat := 118140960795 + 427381 * 2 ^ 59
def prefixEnd_427381 : Nat := 4983230072969 + 3 ^ 40 * 427381 * 2
def baseEnd_427381 : Nat := 195068333866042314286237

theorem tailTrace_427381 : CollatzResearch.WordTrace tailWord_427381 prefixEnd_427381 195068333866042314286237 := by
  unfold tailWord_427381
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587865664679102708809997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10391910443119401805873331 15587865664679102708809997)
  ·
    refine ⟨5845449624254663515803749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15587865664679102708809997 5845449624254663515803749)
    ·
      refine ⟨1096021804547749409213203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5845449624254663515803749 1096021804547749409213203)
      ·
        refine ⟨1644032706821624113819805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096021804547749409213203 1644032706821624113819805)
        ·
          refine ⟨616512265058109042682427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1644032706821624113819805 616512265058109042682427)
          ·
            refine ⟨924768397587163564023641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616512265058109042682427 924768397587163564023641)
            ·
              refine ⟨693576298190372673017731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924768397587163564023641 693576298190372673017731)
              ·
                refine ⟨1040364447285559009526597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693576298190372673017731 1040364447285559009526597)
                ·
                  refine ⟨195068333866042314286237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040364447285559009526597 195068333866042314286237)
                  ·
                    rfl

theorem cell20_427381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_427381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427381 prefixEnd_427381 := by exact prefixLift 427381
  have htrace : WordTrace (prefixWord ++ tailWord_427381) baseStart_427381 baseEnd_427381 := by
    simpa [prefixWord, tailWord_427381, baseEnd_427381] using wordTrace_append hprefix tailTrace_427381
  have hstable : (prefixWord ++ tailWord_427381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427381).length < 2 ^ (prefixWord ++ tailWord_427381).sum := by decide
  have hdescent : baseEnd_427381 < baseStart_427381 := by decide
  rcases family_descends (prefixWord ++ tailWord_427381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427385 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_427385 : Nat := 118140960795 + 427385 * 2 ^ 59
def prefixEnd_427385 : Nat := 4983230072969 + 3 ^ 40 * 427385 * 2
def baseEnd_427385 : Nat := 195070159575036078152887

theorem tailTrace_427385 : CollatzResearch.WordTrace tailWord_427385 prefixEnd_427385 195070159575036078152887 := by
  unfold tailWord_427385
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588011556664611391955609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10392007704443074261303739 15588011556664611391955609)
  ·
    refine ⟨11691008667498458543966707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15588011556664611391955609 11691008667498458543966707)
    ·
      refine ⟨17536513001247687815950061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11691008667498458543966707 17536513001247687815950061)
      ·
        refine ⟨6576192375467882930981273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17536513001247687815950061 6576192375467882930981273)
        ·
          refine ⟨4932144281600912198235955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576192375467882930981273 4932144281600912198235955)
          ·
            refine ⟨7398216422401368297353933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932144281600912198235955 7398216422401368297353933)
            ·
              refine ⟨2774331158400513111507725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7398216422401368297353933 2774331158400513111507725)
              ·
                refine ⟨1040374184400192416815397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2774331158400513111507725 1040374184400192416815397)
                ·
                  refine ⟨195070159575036078152887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040374184400192416815397 195070159575036078152887)
                  ·
                    rfl

theorem cell20_427385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_427385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427385 prefixEnd_427385 := by exact prefixLift 427385
  have htrace : WordTrace (prefixWord ++ tailWord_427385) baseStart_427385 baseEnd_427385 := by
    simpa [prefixWord, tailWord_427385, baseEnd_427385] using wordTrace_append hprefix tailTrace_427385
  have hstable : (prefixWord ++ tailWord_427385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427385).length < 2 ^ (prefixWord ++ tailWord_427385).sum := by decide
  have hdescent : baseEnd_427385 < baseStart_427385 := by decide
  rcases family_descends (prefixWord ++ tailWord_427385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427495 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 2]
def baseStart_427495 : Nat := 118140960795 + 427495 * 2 ^ 59
def prefixEnd_427495 : Nat := 4983230072969 + 3 ^ 40 * 427495 * 2
def baseEnd_427495 : Nat := 195120366572364584485771

theorem tailTrace_427495 : CollatzResearch.WordTrace tailWord_427495 prefixEnd_427495 195120366572364584485771 := by
  unfold tailWord_427495
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592023586266100178459939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394682390844066785639959 15592023586266100178459939)
  ·
    refine ⟨23388035379399150267689909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15592023586266100178459939 23388035379399150267689909)
    ·
      refine ⟨2192628316818670337595929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23388035379399150267689909 2192628316818670337595929)
      ·
        refine ⟨1644471237614002753196947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192628316818670337595929 1644471237614002753196947)
        ·
          refine ⟨2466706856421004129795421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644471237614002753196947 2466706856421004129795421)
          ·
            refine ⟨925015071157876548673283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2466706856421004129795421 925015071157876548673283)
            ·
              refine ⟨1387522606736814823009925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925015071157876548673283 1387522606736814823009925)
              ·
                refine ⟨260160488763152779314361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1387522606736814823009925 260160488763152779314361)
                ·
                  refine ⟨195120366572364584485771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260160488763152779314361 195120366572364584485771)
                  ·
                    rfl

theorem cell20_427495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2].length) (baseStart_427495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427495 prefixEnd_427495 := by exact prefixLift 427495
  have htrace : WordTrace (prefixWord ++ tailWord_427495) baseStart_427495 baseEnd_427495 := by
    simpa [prefixWord, tailWord_427495, baseEnd_427495] using wordTrace_append hprefix tailTrace_427495
  have hstable : (prefixWord ++ tailWord_427495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427495).length < 2 ^ (prefixWord ++ tailWord_427495).sum := by decide
  have hdescent : baseEnd_427495 < baseStart_427495 := by decide
  rcases family_descends (prefixWord ++ tailWord_427495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427513 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_427513 : Nat := 118140960795 + 427513 * 2 ^ 59
def prefixEnd_427513 : Nat := 4983230072969 + 3 ^ 40 * 427513 * 2
def baseEnd_427513 : Nat := 195128582262836521885697

theorem tailTrace_427513 : CollatzResearch.WordTrace tailWord_427513 prefixEnd_427513 195128582262836521885697 := by
  unfold tailWord_427513
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592680100200889252615193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10395120066800592835076795 15592680100200889252615193)
  ·
    refine ⟨11694510075150666939461395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15592680100200889252615193 11694510075150666939461395)
    ·
      refine ⟨17541765112726000409192093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11694510075150666939461395 17541765112726000409192093)
      ·
        refine ⟨6578161917272250153447035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17541765112726000409192093 6578161917272250153447035)
        ·
          refine ⟨9867242875908375230170553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578161917272250153447035 9867242875908375230170553)
          ·
            refine ⟨7400432156931281422627915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9867242875908375230170553 7400432156931281422627915)
            ·
              refine ⟨11100648235396922133941873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400432156931281422627915 11100648235396922133941873)
              ·
                refine ⟨8325486176547691600456405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11100648235396922133941873 8325486176547691600456405)
                ·
                  refine ⟨195128582262836521885697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8325486176547691600456405 195128582262836521885697)
                  ·
                    rfl

theorem cell20_427513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_427513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427513 prefixEnd_427513 := by exact prefixLift 427513
  have htrace : WordTrace (prefixWord ++ tailWord_427513) baseStart_427513 baseEnd_427513 := by
    simpa [prefixWord, tailWord_427513, baseEnd_427513] using wordTrace_append hprefix tailTrace_427513
  have hstable : (prefixWord ++ tailWord_427513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427513).length < 2 ^ (prefixWord ++ tailWord_427513).sum := by decide
  have hdescent : baseEnd_427513 < baseStart_427513 := by decide
  rcases family_descends (prefixWord ++ tailWord_427513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427540 : List Nat := [2, 4, 3, 1, 2, 1, 7]
def baseStart_427540 : Nat := 118140960795 + 427540 * 2 ^ 59
def prefixEnd_427540 : Nat := 4983230072969 + 3 ^ 40 * 427540 * 2
def baseEnd_427540 : Nat := 21682322866504936442843

theorem tailTrace_427540 : CollatzResearch.WordTrace tailWord_427540 prefixEnd_427540 21682322866504936442843 := by
  unfold tailWord_427540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796832435551536431924037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10395776580735381909232049 7796832435551536431924037)
  ·
    refine ⟨1461906081665913080985757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7796832435551536431924037 1461906081665913080985757)
    ·
      refine ⟨548214780624717405369659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1461906081665913080985757 548214780624717405369659)
      ·
        refine ⟨822322170937076108054489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548214780624717405369659 822322170937076108054489)
        ·
          refine ⟨616741628202807081040867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822322170937076108054489 616741628202807081040867)
          ·
            refine ⟨925112442304210621561301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616741628202807081040867 925112442304210621561301)
            ·
              refine ⟨21682322866504936442843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 925112442304210621561301 21682322866504936442843)
              ·
                rfl

theorem cell20_427540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_427540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427540 prefixEnd_427540 := by exact prefixLift 427540
  have htrace : WordTrace (prefixWord ++ tailWord_427540) baseStart_427540 baseEnd_427540 := by
    simpa [prefixWord, tailWord_427540, baseEnd_427540] using wordTrace_append hprefix tailTrace_427540
  have hstable : (prefixWord ++ tailWord_427540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427540).length < 2 ^ (prefixWord ++ tailWord_427540).sum := by decide
  have hdescent : baseEnd_427540 < baseStart_427540 := by decide
  rcases family_descends (prefixWord ++ tailWord_427540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427574 : List Nat := [5, 1, 2, 1, 4, 1, 2, 4]
def baseStart_427574 : Nat := 118140960795 + 427574 * 2 ^ 59
def prefixEnd_427574 : Nat := 4983230072969 + 3 ^ 40 * 427574 * 2
def baseEnd_427574 : Nat := 65052141441663806950705

theorem tailTrace_427574 : CollatzResearch.WordTrace tailWord_427574 prefixEnd_427574 65052141441663806950705 := by
  unfold tailWord_427574
  simp only [CollatzResearch.WordTrace]
  refine ⟨974681559561243541911611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10396603301986597780390517 974681559561243541911611)
  ·
    refine ⟨1462022339341865312867417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974681559561243541911611 1462022339341865312867417)
    ·
      refine ⟨1096516754506398984650563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1462022339341865312867417 1096516754506398984650563)
      ·
        refine ⟨1644775131759598476975845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096516754506398984650563 1644775131759598476975845)
        ·
          refine ⟨308395337204924714432971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1644775131759598476975845 308395337204924714432971)
          ·
            refine ⟨462593005807387071649457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308395337204924714432971 462593005807387071649457)
            ·
              refine ⟨346944754355540303737093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462593005807387071649457 346944754355540303737093)
              ·
                refine ⟨65052141441663806950705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346944754355540303737093 65052141441663806950705)
                ·
                  rfl

theorem cell20_427574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_427574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427574 prefixEnd_427574 := by exact prefixLift 427574
  have htrace : WordTrace (prefixWord ++ tailWord_427574) baseStart_427574 baseEnd_427574 := by
    simpa [prefixWord, tailWord_427574, baseEnd_427574] using wordTrace_append hprefix tailTrace_427574
  have hstable : (prefixWord ++ tailWord_427574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427574).length < 2 ^ (prefixWord ++ tailWord_427574).sum := by decide
  have hdescent : baseEnd_427574 < baseStart_427574 := by decide
  rcases family_descends (prefixWord ++ tailWord_427574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427575 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_427575 : Nat := 118140960795 + 427575 * 2 ^ 59
def prefixEnd_427575 : Nat := 4983230072969 + 3 ^ 40 * 427575 * 2
def baseEnd_427575 : Nat := 195156880752239861818777

theorem tailTrace_427575 : CollatzResearch.WordTrace tailWord_427575 prefixEnd_427575 195156880752239861818777 := by
  unfold tailWord_427575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15594941425976273841372179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10396627617317515894248119 15594941425976273841372179)
  ·
    refine ⟨23392412138964410762058269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15594941425976273841372179 23392412138964410762058269)
    ·
      refine ⟨8772154552111654035771851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23392412138964410762058269 8772154552111654035771851)
      ·
        refine ⟨13158231828167481053657777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8772154552111654035771851 13158231828167481053657777)
        ·
          refine ⟨9868673871125610790243333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13158231828167481053657777 9868673871125610790243333)
          ·
            refine ⟨1850376350836052023170625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9868673871125610790243333 1850376350836052023170625)
            ·
              refine ⟨1387782263127039017377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850376350836052023170625 1387782263127039017377969)
              ·
                refine ⟨1040836697345279263033477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387782263127039017377969 1040836697345279263033477)
                ·
                  refine ⟨195156880752239861818777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1040836697345279263033477 195156880752239861818777)
                  ·
                    rfl

theorem cell20_427575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_427575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427575 prefixEnd_427575 := by exact prefixLift 427575
  have htrace : WordTrace (prefixWord ++ tailWord_427575) baseStart_427575 baseEnd_427575 := by
    simpa [prefixWord, tailWord_427575, baseEnd_427575] using wordTrace_append hprefix tailTrace_427575
  have hstable : (prefixWord ++ tailWord_427575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427575).length < 2 ^ (prefixWord ++ tailWord_427575).sum := by decide
  have hdescent : baseEnd_427575 < baseStart_427575 := by decide
  rcases family_descends (prefixWord ++ tailWord_427575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427589 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_427589 : Nat := 118140960795 + 427589 * 2 ^ 59
def prefixEnd_427589 : Nat := 4983230072969 + 3 ^ 40 * 427589 * 2
def baseEnd_427589 : Nat := 195163270733718035352053

theorem tailTrace_427589 : CollatzResearch.WordTrace tailWord_427589 prefixEnd_427589 195163270733718035352053 := by
  unfold tailWord_427589
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595452047925554232381821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10396968031950369488254547 15595452047925554232381821)
  ·
    refine ⟨5848294517972082837143183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15595452047925554232381821 5848294517972082837143183)
    ·
      refine ⟨8772441776958124255714775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5848294517972082837143183 8772441776958124255714775)
      ·
        refine ⟨13158662665437186383572163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8772441776958124255714775 13158662665437186383572163)
        ·
          refine ⟨19737993998155779575358245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13158662665437186383572163 19737993998155779575358245)
          ·
            refine ⟨3700873874654208670379671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19737993998155779575358245 3700873874654208670379671)
            ·
              refine ⟨5551310811981313005569507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700873874654208670379671 5551310811981313005569507)
              ·
                refine ⟨8326966217971969508354261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551310811981313005569507 8326966217971969508354261)
                ·
                  refine ⟨195163270733718035352053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8326966217971969508354261 195163270733718035352053)
                  ·
                    rfl

theorem cell20_427589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_427589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427589 prefixEnd_427589 := by exact prefixLift 427589
  have htrace : WordTrace (prefixWord ++ tailWord_427589) baseStart_427589 baseEnd_427589 := by
    simpa [prefixWord, tailWord_427589, baseEnd_427589] using wordTrace_append hprefix tailTrace_427589
  have hstable : (prefixWord ++ tailWord_427589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427589).length < 2 ^ (prefixWord ++ tailWord_427589).sum := by decide
  have hdescent : baseEnd_427589 < baseStart_427589 := by decide
  rcases family_descends (prefixWord ++ tailWord_427589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427620 : List Nat := [2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_427620 : Nat := 118140960795 + 427620 * 2 ^ 59
def prefixEnd_427620 : Nat := 4983230072969 + 3 ^ 40 * 427620 * 2
def baseEnd_427620 : Nat := 65059139992806568439531

theorem tailTrace_427620 : CollatzResearch.WordTrace tailWord_427620 prefixEnd_427620 65059139992806568439531 := by
  unfold tailWord_427620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798291355406623263380157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10397721807208831017840209 7798291355406623263380157)
  ·
    refine ⟨2924359258277483723767559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7798291355406623263380157 2924359258277483723767559)
    ·
      refine ⟨4386538887416225585651339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924359258277483723767559 4386538887416225585651339)
      ·
        refine ⟨6579808331124338378477009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386538887416225585651339 6579808331124338378477009)
        ·
          refine ⟨4934856248343253783857757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579808331124338378477009 4934856248343253783857757)
          ·
            refine ⟨1850571093128720168946659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4934856248343253783857757 1850571093128720168946659)
            ·
              refine ⟨2775856639693080253419989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850571093128720168946659 2775856639693080253419989)
              ·
                refine ⟨65059139992806568439531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2775856639693080253419989 65059139992806568439531)
                ·
                  rfl

theorem cell20_427620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_427620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427620 prefixEnd_427620 := by exact prefixLift 427620
  have htrace : WordTrace (prefixWord ++ tailWord_427620) baseStart_427620 baseEnd_427620 := by
    simpa [prefixWord, tailWord_427620, baseEnd_427620] using wordTrace_append hprefix tailTrace_427620
  have hstable : (prefixWord ++ tailWord_427620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427620).length < 2 ^ (prefixWord ++ tailWord_427620).sum := by decide
  have hdescent : baseEnd_427620 < baseStart_427620 := by decide
  rcases family_descends (prefixWord ++ tailWord_427620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427623 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 3]
def baseStart_427623 : Nat := 118140960795 + 427623 * 2 ^ 59
def prefixEnd_427623 : Nat := 4983230072969 + 3 ^ 40 * 427623 * 2
def baseEnd_427623 : Nat := 195178789260165028218581

theorem tailTrace_427623 : CollatzResearch.WordTrace tailWord_427623 prefixEnd_427623 195178789260165028218581 := by
  unfold tailWord_427623
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596692129802378039119523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10397794753201585359413015 15596692129802378039119523)
  ·
    refine ⟨23395038194703567058679285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596692129802378039119523 23395038194703567058679285)
    ·
      refine ⟨2193284830753459411751183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23395038194703567058679285 2193284830753459411751183)
      ·
        refine ⟨3289927246130189117626775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193284830753459411751183 3289927246130189117626775)
        ·
          refine ⟨4934890869195283676440163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289927246130189117626775 4934890869195283676440163)
          ·
            refine ⟨7402336303792925514660245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934890869195283676440163 7402336303792925514660245)
            ·
              refine ⟨346984514240293383499699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7402336303792925514660245 346984514240293383499699)
              ·
                refine ⟨520476771360440075249549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346984514240293383499699 520476771360440075249549)
                ·
                  refine ⟨195178789260165028218581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520476771360440075249549 195178789260165028218581)
                  ·
                    rfl

theorem cell20_427623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_427623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427623 prefixEnd_427623 := by exact prefixLift 427623
  have htrace : WordTrace (prefixWord ++ tailWord_427623) baseStart_427623 baseEnd_427623 := by
    simpa [prefixWord, tailWord_427623, baseEnd_427623] using wordTrace_append hprefix tailTrace_427623
  have hstable : (prefixWord ++ tailWord_427623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427623).length < 2 ^ (prefixWord ++ tailWord_427623).sum := by decide
  have hdescent : baseEnd_427623 < baseStart_427623 := by decide
  rcases family_descends (prefixWord ++ tailWord_427623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427637 : List Nat := [1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_427637 : Nat := 118140960795 + 427637 * 2 ^ 59
def prefixEnd_427637 : Nat := 4983230072969 + 3 ^ 40 * 427637 * 2
def baseEnd_427637 : Nat := 65061726413881067250619

theorem tailTrace_427637 : CollatzResearch.WordTrace tailWord_427637 prefixEnd_427637 65061726413881067250619 := by
  unfold tailWord_427637
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597202751751658430129165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10398135167834438953419443 15597202751751658430129165)
  ·
    refine ⟨5848951031906871911298437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15597202751751658430129165 5848951031906871911298437)
    ·
      refine ⟨1096678318482538483368457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5848951031906871911298437 1096678318482538483368457)
      ·
        refine ⟨822508738861903862526343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1096678318482538483368457 822508738861903862526343)
        ·
          refine ⟨1233763108292855793789515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822508738861903862526343 1233763108292855793789515)
          ·
            refine ⟨1850644662439283690684273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233763108292855793789515 1850644662439283690684273)
            ·
              refine ⟨1387983496829462768013205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850644662439283690684273 1387983496829462768013205)
              ·
                refine ⟨65061726413881067250619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1387983496829462768013205 65061726413881067250619)
                ·
                  rfl

theorem cell20_427637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_427637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427637 prefixEnd_427637 := by exact prefixLift 427637
  have htrace : WordTrace (prefixWord ++ tailWord_427637) baseStart_427637 baseEnd_427637 := by
    simpa [prefixWord, tailWord_427637, baseEnd_427637] using wordTrace_append hprefix tailTrace_427637
  have hstable : (prefixWord ++ tailWord_427637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427637).length < 2 ^ (prefixWord ++ tailWord_427637).sum := by decide
  have hdescent : baseEnd_427637 < baseStart_427637 := by decide
  rcases family_descends (prefixWord ++ tailWord_427637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427658 : List Nat := [3, 1, 2, 3, 2, 9]
def baseStart_427658 : Nat := 118140960795 + 427658 * 2 ^ 59
def prefixEnd_427658 : Nat := 4983230072969 + 3 ^ 40 * 427658 * 2
def baseEnd_427658 : Nat := 7229435711624461557473

theorem tailTrace_427658 : CollatzResearch.WordTrace tailWord_427658 prefixEnd_427658 7229435711624461557473 := by
  unfold tailWord_427658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899492171168894754160907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10398645789783719344429085 3899492171168894754160907)
  ·
    refine ⟨5849238256753342131241361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3899492171168894754160907 5849238256753342131241361)
    ·
      refine ⟨4386928692565006598431021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5849238256753342131241361 4386928692565006598431021)
      ·
        refine ⟨1645098259711877474411633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4386928692565006598431021 1645098259711877474411633)
        ·
          refine ⟨1233823694783908105808725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645098259711877474411633 1233823694783908105808725)
          ·
            refine ⟨7229435711624461557473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1233823694783908105808725 7229435711624461557473)
            ·
              rfl

theorem cell20_427658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 9].length) (baseStart_427658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427658 prefixEnd_427658 := by exact prefixLift 427658
  have htrace : WordTrace (prefixWord ++ tailWord_427658) baseStart_427658 baseEnd_427658 := by
    simpa [prefixWord, tailWord_427658, baseEnd_427658] using wordTrace_append hprefix tailTrace_427658
  have hstable : (prefixWord ++ tailWord_427658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427658).length < 2 ^ (prefixWord ++ tailWord_427658).sum := by decide
  have hdescent : baseEnd_427658 < baseStart_427658 := by decide
  rcases family_descends (prefixWord ++ tailWord_427658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427688 : List Nat := [2, 1, 7, 1, 1, 1, 3, 4]
def baseStart_427688 : Nat := 118140960795 + 427688 * 2 ^ 59
def prefixEnd_427688 : Nat := 4983230072969 + 3 ^ 40 * 427688 * 2
def baseEnd_427688 : Nat := 65069485677104563683883

theorem tailTrace_427688 : CollatzResearch.WordTrace tailWord_427688 prefixEnd_427688 65069485677104563683883 := by
  unfold tailWord_427688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799531437283447070117859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10399375249711262760157145 7799531437283447070117859)
  ·
    refine ⟨11699297155925170605176789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7799531437283447070117859 11699297155925170605176789)
    ·
      refine ⟨274202277091996186058831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11699297155925170605176789 274202277091996186058831)
      ·
        refine ⟨411303415637994279088247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274202277091996186058831 411303415637994279088247)
        ·
          refine ⟨616955123456991418632371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411303415637994279088247 616955123456991418632371)
          ·
            refine ⟨925432685185487127948557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616955123456991418632371 925432685185487127948557)
            ·
              refine ⟨347037256944557672980709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925432685185487127948557 347037256944557672980709)
              ·
                refine ⟨65069485677104563683883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347037256944557672980709 65069485677104563683883)
                ·
                  rfl

theorem cell20_427688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_427688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427688 prefixEnd_427688 := by exact prefixLift 427688
  have htrace : WordTrace (prefixWord ++ tailWord_427688) baseStart_427688 baseEnd_427688 := by
    simpa [prefixWord, tailWord_427688, baseEnd_427688] using wordTrace_append hprefix tailTrace_427688
  have hstable : (prefixWord ++ tailWord_427688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427688).length < 2 ^ (prefixWord ++ tailWord_427688).sum := by decide
  have hdescent : baseEnd_427688 < baseStart_427688 := by decide
  rcases family_descends (prefixWord ++ tailWord_427688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427702 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_427702 : Nat := 118140960795 + 427702 * 2 ^ 59
def prefixEnd_427702 : Nat := 4983230072969 + 3 ^ 40 * 427702 * 2
def baseEnd_427702 : Nat := 195214847012791864584925

theorem tailTrace_427702 : CollatzResearch.WordTrace tailWord_427702 prefixEnd_427702 195214847012791864584925 := by
  unfold tailWord_427702
  simp only [CollatzResearch.WordTrace]
  refine ⟨974973343532260908202835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10399715664344116354163573 974973343532260908202835)
  ·
    refine ⟨1462460015298391362304253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974973343532260908202835 1462460015298391362304253)
    ·
      refine ⟨548422505736896760864095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1462460015298391362304253 548422505736896760864095)
      ·
        refine ⟨822633758605345141296143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548422505736896760864095 822633758605345141296143)
        ·
          refine ⟨1233950637908017711944215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822633758605345141296143 1233950637908017711944215)
          ·
            refine ⟨1850925956862026567916323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233950637908017711944215 1850925956862026567916323)
            ·
              refine ⟨2776388935293039851874485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850925956862026567916323 2776388935293039851874485)
              ·
                refine ⟨260286462683722486113233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2776388935293039851874485 260286462683722486113233)
                ·
                  refine ⟨195214847012791864584925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260286462683722486113233 195214847012791864584925)
                  ·
                    rfl

theorem cell20_427702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_427702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427702 prefixEnd_427702 := by exact prefixLift 427702
  have htrace : WordTrace (prefixWord ++ tailWord_427702) baseStart_427702 baseEnd_427702 := by
    simpa [prefixWord, tailWord_427702, baseEnd_427702] using wordTrace_append hprefix tailTrace_427702
  have hstable : (prefixWord ++ tailWord_427702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427702).length < 2 ^ (prefixWord ++ tailWord_427702).sum := by decide
  have hdescent : baseEnd_427702 < baseStart_427702 := by decide
  rcases family_descends (prefixWord ++ tailWord_427702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427706 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_427706 : Nat := 118140960795 + 427706 * 2 ^ 59
def prefixEnd_427706 : Nat := 4983230072969 + 3 ^ 40 * 427706 * 2
def baseEnd_427706 : Nat := 195216672721785628451575

theorem tailTrace_427706 : CollatzResearch.WordTrace tailWord_427706 prefixEnd_427706 195216672721785628451575 := by
  unfold tailWord_427706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899929847125420803597743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10399812925667788809593981 3899929847125420803597743)
  ·
    refine ⟨5849894770688131205396615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3899929847125420803597743 5849894770688131205396615)
    ·
      refine ⟨8774842156032196808094923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5849894770688131205396615 8774842156032196808094923)
      ·
        refine ⟨13162263234048295212142385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8774842156032196808094923 13162263234048295212142385)
        ·
          refine ⟨9871697425536221409106789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13162263234048295212142385 9871697425536221409106789)
          ·
            refine ⟨1850943267288041514207523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9871697425536221409106789 1850943267288041514207523)
            ·
              refine ⟨2776414900932062271311285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850943267288041514207523 2776414900932062271311285)
              ·
                refine ⟨260288896962380837935433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2776414900932062271311285 260288896962380837935433)
                ·
                  refine ⟨195216672721785628451575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260288896962380837935433 195216672721785628451575)
                  ·
                    rfl

theorem cell20_427706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_427706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427706 prefixEnd_427706 := by exact prefixLift 427706
  have htrace : WordTrace (prefixWord ++ tailWord_427706) baseStart_427706 baseEnd_427706 := by
    simpa [prefixWord, tailWord_427706, baseEnd_427706] using wordTrace_append hprefix tailTrace_427706
  have hstable : (prefixWord ++ tailWord_427706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427706).length < 2 ^ (prefixWord ++ tailWord_427706).sum := by decide
  have hdescent : baseEnd_427706 < baseStart_427706 := by decide
  rcases family_descends (prefixWord ++ tailWord_427706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427737 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 3]
def baseStart_427737 : Nat := 118140960795 + 427737 * 2 ^ 59
def prefixEnd_427737 : Nat := 4983230072969 + 3 ^ 40 * 427737 * 2
def baseEnd_427737 : Nat := 195230821966487298418115

theorem tailTrace_427737 : CollatzResearch.WordTrace tailWord_427737 prefixEnd_427737 195230821966487298418115 := by
  unfold tailWord_427737
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600850051389375508769465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10400566700926250339179643 15600850051389375508769465)
  ·
    refine ⟨11700637538542031631577099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15600850051389375508769465 11700637538542031631577099)
    ·
      refine ⟨17550956307813047447365649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11700637538542031631577099 17550956307813047447365649)
      ·
        refine ⟨13163217230859785585524237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17550956307813047447365649 13163217230859785585524237)
        ·
          refine ⟨4936206461572419594571589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13163217230859785585524237 4936206461572419594571589)
          ·
            refine ⟨925538711544828673982173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4936206461572419594571589 925538711544828673982173)
            ·
              refine ⟨347077016829310752743315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925538711544828673982173 347077016829310752743315)
              ·
                refine ⟨520615525243966129114973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347077016829310752743315 520615525243966129114973)
                ·
                  refine ⟨195230821966487298418115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520615525243966129114973 195230821966487298418115)
                  ·
                    rfl

theorem cell20_427737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_427737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427737 prefixEnd_427737 := by exact prefixLift 427737
  have htrace : WordTrace (prefixWord ++ tailWord_427737) baseStart_427737 baseEnd_427737 := by
    simpa [prefixWord, tailWord_427737, baseEnd_427737] using wordTrace_append hprefix tailTrace_427737
  have hstable : (prefixWord ++ tailWord_427737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427737).length < 2 ^ (prefixWord ++ tailWord_427737).sum := by decide
  have hdescent : baseEnd_427737 < baseStart_427737 := by decide
  rcases family_descends (prefixWord ++ tailWord_427737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427747 : List Nat := [1, 1, 1, 7, 3, 1, 2, 4]
def baseStart_427747 : Nat := 118140960795 + 427747 * 2 ^ 59
def prefixEnd_427747 : Nat := 4983230072969 + 3 ^ 40 * 427747 * 2
def baseEnd_427747 : Nat := 65078462079657236028247

theorem tailTrace_427747 : CollatzResearch.WordTrace tailWord_427747 prefixEnd_427747 65078462079657236028247 := by
  unfold tailWord_427747
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601214781353147216633495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10400809854235431477755663 15601214781353147216633495)
  ·
    refine ⟨23401822172029720824950243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15601214781353147216633495 23401822172029720824950243)
    ·
      refine ⟨35102733258044581237425365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23401822172029720824950243 35102733258044581237425365)
      ·
        refine ⟨822720310735419872752157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35102733258044581237425365 822720310735419872752157)
        ·
          refine ⟨308520116525782452282059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822720310735419872752157 308520116525782452282059)
          ·
            refine ⟨462780174788673678423089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308520116525782452282059 462780174788673678423089)
            ·
              refine ⟨347085131091505258817317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462780174788673678423089 347085131091505258817317)
              ·
                refine ⟨65078462079657236028247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347085131091505258817317 65078462079657236028247)
                ·
                  rfl

theorem cell20_427747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_427747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427747 prefixEnd_427747 := by exact prefixLift 427747
  have htrace : WordTrace (prefixWord ++ tailWord_427747) baseStart_427747 baseEnd_427747 := by
    simpa [prefixWord, tailWord_427747, baseEnd_427747] using wordTrace_append hprefix tailTrace_427747
  have hstable : (prefixWord ++ tailWord_427747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427747).length < 2 ^ (prefixWord ++ tailWord_427747).sum := by decide
  have hdescent : baseEnd_427747 < baseStart_427747 := by decide
  rcases family_descends (prefixWord ++ tailWord_427747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427761 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 2]
def baseStart_427761 : Nat := 118140960795 + 427761 * 2 ^ 59
def prefixEnd_427761 : Nat := 4983230072969 + 3 ^ 40 * 427761 * 2
def baseEnd_427761 : Nat := 195241776220449881618017

theorem tailTrace_427761 : CollatzResearch.WordTrace tailWord_427761 prefixEnd_427761 195241776220449881618017 := by
  unfold tailWord_427761
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601725403302427607643137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10401150268868285071762091 15601725403302427607643137)
  ·
    refine ⟨11701294052476820705732353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15601725403302427607643137 11701294052476820705732353)
    ·
      refine ⟨8775970539357615529299265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11701294052476820705732353 8775970539357615529299265)
      ·
        refine ⟨6581977904518211646974449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8775970539357615529299265 6581977904518211646974449)
        ·
          refine ⟨4936483428388658735230837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6581977904518211646974449 4936483428388658735230837)
          ·
            refine ⟨462795321411436756427891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4936483428388658735230837 462795321411436756427891)
            ·
              refine ⟨694192982117155134641837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462795321411436756427891 694192982117155134641837)
              ·
                refine ⟨260322368293933175490689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694192982117155134641837 260322368293933175490689)
                ·
                  refine ⟨195241776220449881618017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260322368293933175490689 195241776220449881618017)
                  ·
                    rfl

theorem cell20_427761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_427761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427761 prefixEnd_427761 := by exact prefixLift 427761
  have htrace : WordTrace (prefixWord ++ tailWord_427761) baseStart_427761 baseEnd_427761 := by
    simpa [prefixWord, tailWord_427761, baseEnd_427761] using wordTrace_append hprefix tailTrace_427761
  have hstable : (prefixWord ++ tailWord_427761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427761).length < 2 ^ (prefixWord ++ tailWord_427761).sum := by decide
  have hdescent : baseEnd_427761 < baseStart_427761 := by decide
  rcases family_descends (prefixWord ++ tailWord_427761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427778 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_427778 : Nat := 118140960795 + 427778 * 2 ^ 59
def prefixEnd_427778 : Nat := 4983230072969 + 3 ^ 40 * 427778 * 2
def baseEnd_427778 : Nat := 195249535483673378051281

theorem tailTrace_427778 : CollatzResearch.WordTrace tailWord_427778 prefixEnd_427778 195249535483673378051281 := by
  unfold tailWord_427778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900586361060209877752997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10401563629493893007341325 3900586361060209877752997)
  ·
    refine ⟨731359942698789352078687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3900586361060209877752997 731359942698789352078687)
    ·
      refine ⟨1097039914048184028118031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731359942698789352078687 1097039914048184028118031)
      ·
        refine ⟨1645559871072276042177047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097039914048184028118031 1645559871072276042177047)
        ·
          refine ⟨2468339806608414063265571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645559871072276042177047 2468339806608414063265571)
          ·
            refine ⟨3702509709912621094898357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468339806608414063265571 3702509709912621094898357)
            ·
              refine ⟨347110285304308227646721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3702509709912621094898357 347110285304308227646721)
              ·
                refine ⟨260332713978231170735041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347110285304308227646721 260332713978231170735041)
                ·
                  refine ⟨195249535483673378051281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260332713978231170735041 195249535483673378051281)
                  ·
                    rfl

theorem cell20_427778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_427778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427778 prefixEnd_427778 := by exact prefixLift 427778
  have htrace : WordTrace (prefixWord ++ tailWord_427778) baseStart_427778 baseEnd_427778 := by
    simpa [prefixWord, tailWord_427778, baseEnd_427778] using wordTrace_append hprefix tailTrace_427778
  have hstable : (prefixWord ++ tailWord_427778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427778).length < 2 ^ (prefixWord ++ tailWord_427778).sum := by decide
  have hdescent : baseEnd_427778 < baseStart_427778 := by decide
  rcases family_descends (prefixWord ++ tailWord_427778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427779 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_427779 : Nat := 118140960795 + 427779 * 2 ^ 59
def prefixEnd_427779 : Nat := 4983230072969 + 3 ^ 40 * 427779 * 2
def baseEnd_427779 : Nat := 195249991910921819017943

theorem tailTrace_427779 : CollatzResearch.WordTrace tailWord_427779 prefixEnd_427779 195249991910921819017943 := by
  unfold tailWord_427779
  simp only [CollatzResearch.WordTrace]
  refine ⟨15602381917237216681798391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10401587944824811121198927 15602381917237216681798391)
  ·
    refine ⟨23403572875855825022697587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15602381917237216681798391 23403572875855825022697587)
    ·
      refine ⟨35105359313783737534046381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23403572875855825022697587 35105359313783737534046381)
      ·
        refine ⟨13164509742668901575267393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35105359313783737534046381 13164509742668901575267393)
        ·
          refine ⟨9873382307001676181450545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13164509742668901575267393 9873382307001676181450545)
          ·
            refine ⟨7405036730251257136087909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9873382307001676181450545 7405036730251257136087909)
            ·
              refine ⟨1388444386922110713016483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7405036730251257136087909 1388444386922110713016483)
              ·
                refine ⟨2082666580383166069524725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388444386922110713016483 2082666580383166069524725)
                ·
                  refine ⟨195249991910921819017943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2082666580383166069524725 195249991910921819017943)
                  ·
                    rfl

theorem cell20_427779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_427779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427779 prefixEnd_427779 := by exact prefixLift 427779
  have htrace : WordTrace (prefixWord ++ tailWord_427779) baseStart_427779 baseEnd_427779 := by
    simpa [prefixWord, tailWord_427779, baseEnd_427779] using wordTrace_append hprefix tailTrace_427779
  have hstable : (prefixWord ++ tailWord_427779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427779).length < 2 ^ (prefixWord ++ tailWord_427779).sum := by decide
  have hdescent : baseEnd_427779 < baseStart_427779 := by decide
  rcases family_descends (prefixWord ++ tailWord_427779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427810 : List Nat := [3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_427810 : Nat := 118140960795 + 427810 * 2 ^ 59
def prefixEnd_427810 : Nat := 4983230072969 + 3 ^ 40 * 427810 * 2
def baseEnd_427810 : Nat := 65088047051874496328161

theorem tailTrace_427810 : CollatzResearch.WordTrace tailWord_427810 prefixEnd_427810 65088047051874496328161 := by
  unfold tailWord_427810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900878145031227244044221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10402341720083272650784589 3900878145031227244044221)
  ·
    refine ⟨1462829304386710216516583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3900878145031227244044221 1462829304386710216516583)
    ·
      refine ⟨2194243956580065324774875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462829304386710216516583 2194243956580065324774875)
      ·
        refine ⟨3291365934870097987162313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194243956580065324774875 3291365934870097987162313)
        ·
          refine ⟨2468524451152573490371735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3291365934870097987162313 2468524451152573490371735)
          ·
            refine ⟨3702786676728860235557603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468524451152573490371735 3702786676728860235557603)
            ·
              refine ⟨5554180015093290353336405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702786676728860235557603 5554180015093290353336405)
              ·
                refine ⟨65088047051874496328161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5554180015093290353336405 65088047051874496328161)
                ·
                  rfl

theorem cell20_427810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_427810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427810 prefixEnd_427810 := by exact prefixLift 427810
  have htrace : WordTrace (prefixWord ++ tailWord_427810) baseStart_427810 baseEnd_427810 := by
    simpa [prefixWord, tailWord_427810, baseEnd_427810] using wordTrace_append hprefix tailTrace_427810
  have hstable : (prefixWord ++ tailWord_427810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427810).length < 2 ^ (prefixWord ++ tailWord_427810).sum := by decide
  have hdescent : baseEnd_427810 < baseStart_427810 := by decide
  rcases family_descends (prefixWord ++ tailWord_427810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427830 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_427830 : Nat := 118140960795 + 427830 * 2 ^ 59
def prefixEnd_427830 : Nat := 4983230072969 + 3 ^ 40 * 427830 * 2
def baseEnd_427830 : Nat := 195273269700592308317735

theorem tailTrace_427830 : CollatzResearch.WordTrace tailWord_427830 prefixEnd_427830 195273269700592308317735 := by
  unfold tailWord_427830
  simp only [CollatzResearch.WordTrace]
  refine ⟨975265127503278274494059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10402828026701634927936629 975265127503278274494059)
  ·
    refine ⟨1462897691254917411741089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975265127503278274494059 1462897691254917411741089)
    ·
      refine ⟨1097173268441188058805817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1462897691254917411741089 1097173268441188058805817)
      ·
        refine ⟨822879951330891044104363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097173268441188058805817 822879951330891044104363)
        ·
          refine ⟨1234319926996336566156545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822879951330891044104363 1234319926996336566156545)
          ·
            refine ⟨925739945247252424617409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234319926996336566156545 925739945247252424617409)
            ·
              refine ⟨694304958935439318463057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925739945247252424617409 694304958935439318463057)
              ·
                refine ⟨520728719201579488847293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694304958935439318463057 520728719201579488847293)
                ·
                  refine ⟨195273269700592308317735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520728719201579488847293 195273269700592308317735)
                  ·
                    rfl

theorem cell20_427830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_427830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427830 prefixEnd_427830 := by exact prefixLift 427830
  have htrace : WordTrace (prefixWord ++ tailWord_427830) baseStart_427830 baseEnd_427830 := by
    simpa [prefixWord, tailWord_427830, baseEnd_427830] using wordTrace_append hprefix tailTrace_427830
  have hstable : (prefixWord ++ tailWord_427830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427830).length < 2 ^ (prefixWord ++ tailWord_427830).sum := by decide
  have hdescent : baseEnd_427830 < baseStart_427830 := by decide
  rcases family_descends (prefixWord ++ tailWord_427830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427833 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 2]
def baseStart_427833 : Nat := 118140960795 + 427833 * 2 ^ 59
def prefixEnd_427833 : Nat := 4983230072969 + 3 ^ 40 * 427833 * 2
def baseEnd_427833 : Nat := 195274638982337631217723

theorem tailTrace_427833 : CollatzResearch.WordTrace tailWord_427833 prefixEnd_427833 195274638982337631217723 := by
  unfold tailWord_427833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15604351459041583904264153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10402900972694389269509435 15604351459041583904264153)
  ·
    refine ⟨11703263594281187928198115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15604351459041583904264153 11703263594281187928198115)
    ·
      refine ⟨17554895391421781892297173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11703263594281187928198115 17554895391421781892297173)
      ·
        refine ⟨411442860736448013100715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17554895391421781892297173 411442860736448013100715)
        ·
          refine ⟨617164291104672019651073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411442860736448013100715 617164291104672019651073)
          ·
            refine ⟨462873218328504014738305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617164291104672019651073 462873218328504014738305)
            ·
              refine ⟨347154913746378011053729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462873218328504014738305 347154913746378011053729)
              ·
                refine ⟨260366185309783508290297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347154913746378011053729 260366185309783508290297)
                ·
                  refine ⟨195274638982337631217723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260366185309783508290297 195274638982337631217723)
                  ·
                    rfl

theorem cell20_427833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_427833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427833 prefixEnd_427833 := by exact prefixLift 427833
  have htrace : WordTrace (prefixWord ++ tailWord_427833) baseStart_427833 baseEnd_427833 := by
    simpa [prefixWord, tailWord_427833, baseEnd_427833] using wordTrace_append hprefix tailTrace_427833
  have hstable : (prefixWord ++ tailWord_427833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427833).length < 2 ^ (prefixWord ++ tailWord_427833).sum := by decide
  have hdescent : baseEnd_427833 < baseStart_427833 := by decide
  rcases family_descends (prefixWord ++ tailWord_427833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427834 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_427834 : Nat := 118140960795 + 427834 * 2 ^ 59
def prefixEnd_427834 : Nat := 4983230072969 + 3 ^ 40 * 427834 * 2
def baseEnd_427834 : Nat := 195275095409586072184385

theorem tailTrace_427834 : CollatzResearch.WordTrace tailWord_427834 prefixEnd_427834 195275095409586072184385 := by
  unfold tailWord_427834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901096983009490268762639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10402925288025307383367037 3901096983009490268762639)
  ·
    refine ⟨5851645474514235403143959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3901096983009490268762639 5851645474514235403143959)
    ·
      refine ⟨8777468211771353104715939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5851645474514235403143959 8777468211771353104715939)
      ·
        refine ⟨13166202317657029657073909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777468211771353104715939 13166202317657029657073909)
        ·
          refine ⟨1234331467280346530350679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13166202317657029657073909 1234331467280346530350679)
          ·
            refine ⟨1851497200920519795526019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234331467280346530350679 1851497200920519795526019)
            ·
              refine ⟨2777245801380779693289029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851497200920519795526019 2777245801380779693289029)
              ·
                refine ⟨520733587758896192491693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2777245801380779693289029 520733587758896192491693)
                ·
                  refine ⟨195275095409586072184385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520733587758896192491693 195275095409586072184385)
                  ·
                    rfl

theorem cell20_427834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_427834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427834 prefixEnd_427834 := by exact prefixLift 427834
  have htrace : WordTrace (prefixWord ++ tailWord_427834) baseStart_427834 baseEnd_427834 := by
    simpa [prefixWord, tailWord_427834, baseEnd_427834] using wordTrace_append hprefix tailTrace_427834
  have hstable : (prefixWord ++ tailWord_427834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427834).length < 2 ^ (prefixWord ++ tailWord_427834).sum := by decide
  have hdescent : baseEnd_427834 < baseStart_427834 := by decide
  rcases family_descends (prefixWord ++ tailWord_427834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427837 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 2]
def baseStart_427837 : Nat := 118140960795 + 427837 * 2 ^ 59
def prefixEnd_427837 : Nat := 4983230072969 + 3 ^ 40 * 427837 * 2
def baseEnd_427837 : Nat := 195276464691331395084373

theorem tailTrace_427837 : CollatzResearch.WordTrace tailWord_427837 prefixEnd_427837 195276464691331395084373 := by
  unfold tailWord_427837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15604497351027092587409765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10402998234018061724939843 15604497351027092587409765)
  ·
    refine ⟨2925843253317579860139331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15604497351027092587409765 2925843253317579860139331)
    ·
      refine ⟨4388764879976369790208997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2925843253317579860139331 4388764879976369790208997)
      ·
        refine ⟨822893414995569335664187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4388764879976369790208997 822893414995569335664187)
        ·
          refine ⟨1234340122493354003496281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822893414995569335664187 1234340122493354003496281)
          ·
            refine ⟨925755091870015502622211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234340122493354003496281 925755091870015502622211)
            ·
              refine ⟨1388632637805023253933317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925755091870015502622211 1388632637805023253933317)
              ·
                refine ⟨260368619588441860112497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1388632637805023253933317 260368619588441860112497)
                ·
                  refine ⟨195276464691331395084373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260368619588441860112497 195276464691331395084373)
                  ·
                    rfl

theorem cell20_427837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_427837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427837 prefixEnd_427837 := by exact prefixLift 427837
  have htrace : WordTrace (prefixWord ++ tailWord_427837) baseStart_427837 baseEnd_427837 := by
    simpa [prefixWord, tailWord_427837, baseEnd_427837] using wordTrace_append hprefix tailTrace_427837
  have hstable : (prefixWord ++ tailWord_427837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427837).length < 2 ^ (prefixWord ++ tailWord_427837).sum := by decide
  have hdescent : baseEnd_427837 < baseStart_427837 := by decide
  rcases family_descends (prefixWord ++ tailWord_427837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427848 : List Nat := [2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_427848 : Nat := 118140960795 + 427848 * 2 ^ 59
def prefixEnd_427848 : Nat := 4983230072969 + 3 ^ 40 * 427848 * 2
def baseEnd_427848 : Nat := 65093828463688081905887

theorem tailTrace_427848 : CollatzResearch.WordTrace tailWord_427848 prefixEnd_427848 65093828463688081905887 := by
  unfold tailWord_427848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802449276993620733030099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10403265702658160977373465 7802449276993620733030099)
  ·
    refine ⟨11703673915490431099545149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7802449276993620733030099 11703673915490431099545149)
    ·
      refine ⟨4388877718308911662329431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11703673915490431099545149 4388877718308911662329431)
      ·
        refine ⟨6583316577463367493494147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4388877718308911662329431 6583316577463367493494147)
        ·
          refine ⟨9874974866195051240241221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583316577463367493494147 9874974866195051240241221)
          ·
            refine ⟨1851557787411572107545229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9874974866195051240241221 1851557787411572107545229)
            ·
              refine ⟨694334170279339540329461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1851557787411572107545229 694334170279339540329461)
              ·
                refine ⟨65093828463688081905887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694334170279339540329461 65093828463688081905887)
                ·
                  rfl

theorem cell20_427848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_427848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427848 prefixEnd_427848 := by exact prefixLift 427848
  have htrace : WordTrace (prefixWord ++ tailWord_427848) baseStart_427848 baseEnd_427848 := by
    simpa [prefixWord, tailWord_427848, baseEnd_427848] using wordTrace_append hprefix tailTrace_427848
  have hstable : (prefixWord ++ tailWord_427848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427848).length < 2 ^ (prefixWord ++ tailWord_427848).sum := by decide
  have hdescent : baseEnd_427848 < baseStart_427848 := by decide
  rcases family_descends (prefixWord ++ tailWord_427848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427875 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 2]
def baseStart_427875 : Nat := 118140960795 + 427875 * 2 ^ 59
def prefixEnd_427875 : Nat := 4983230072969 + 3 ^ 40 * 427875 * 2
def baseEnd_427875 : Nat := 195293808926772151817551

theorem tailTrace_427875 : CollatzResearch.WordTrace tailWord_427875 prefixEnd_427875 195293808926772151817551 := by
  unfold tailWord_427875
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605883324889425077293079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10403922216592950051528719 15605883324889425077293079)
  ·
    refine ⟨23408824987334137615939619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15605883324889425077293079 23408824987334137615939619)
    ·
      refine ⟨35113237481001206423909429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23408824987334137615939619 35113237481001206423909429)
      ·
        refine ⟨3291866013843863102241509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35113237481001206423909429 3291866013843863102241509)
        ·
          refine ⟨617224877595724331670283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3291866013843863102241509 617224877595724331670283)
          ·
            refine ⟨925837316393586497505425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617224877595724331670283 925837316393586497505425)
            ·
              refine ⟨694377987295189873129069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925837316393586497505425 694377987295189873129069)
              ·
                refine ⟨260391745235696202423401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694377987295189873129069 260391745235696202423401)
                ·
                  refine ⟨195293808926772151817551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260391745235696202423401 195293808926772151817551)
                  ·
                    rfl

theorem cell20_427875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 2].length) (baseStart_427875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427875 prefixEnd_427875 := by exact prefixLift 427875
  have htrace : WordTrace (prefixWord ++ tailWord_427875) baseStart_427875 baseEnd_427875 := by
    simpa [prefixWord, tailWord_427875, baseEnd_427875] using wordTrace_append hprefix tailTrace_427875
  have hstable : (prefixWord ++ tailWord_427875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427875).length < 2 ^ (prefixWord ++ tailWord_427875).sum := by decide
  have hdescent : baseEnd_427875 < baseStart_427875 := by decide
  rcases family_descends (prefixWord ++ tailWord_427875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427926 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_427926 : Nat := 118140960795 + 427926 * 2 ^ 59
def prefixEnd_427926 : Nat := 4983230072969 + 3 ^ 40 * 427926 * 2
def baseEnd_427926 : Nat := 195317086716442641117343

theorem tailTrace_427926 : CollatzResearch.WordTrace tailWord_427926 prefixEnd_427926 195317086716442641117343 := by
  unfold tailWord_427926
  simp only [CollatzResearch.WordTrace]
  refine ⟨975483965481541299212477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10405162298469773858266421 975483965481541299212477)
  ·
    refine ⟨365806487055577987204679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 975483965481541299212477 365806487055577987204679)
    ·
      refine ⟨548709730583366980807019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365806487055577987204679 548709730583366980807019)
      ·
        refine ⟨823064595875050471210529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548709730583366980807019 823064595875050471210529)
        ·
          refine ⟨617298446906287853407897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823064595875050471210529 617298446906287853407897)
          ·
            refine ⟨462973835179715890055923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617298446906287853407897 462973835179715890055923)
            ·
              refine ⟨694460752769573835083885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462973835179715890055923 694460752769573835083885)
              ·
                refine ⟨260422782288590188156457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694460752769573835083885 260422782288590188156457)
                ·
                  refine ⟨195317086716442641117343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260422782288590188156457 195317086716442641117343)
                  ·
                    rfl

theorem cell20_427926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_427926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427926 prefixEnd_427926 := by exact prefixLift 427926
  have htrace : WordTrace (prefixWord ++ tailWord_427926) baseStart_427926 baseEnd_427926 := by
    simpa [prefixWord, tailWord_427926, baseEnd_427926] using wordTrace_append hprefix tailTrace_427926
  have hstable : (prefixWord ++ tailWord_427926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427926).length < 2 ^ (prefixWord ++ tailWord_427926).sum := by decide
  have hdescent : baseEnd_427926 < baseStart_427926 := by decide
  rcases family_descends (prefixWord ++ tailWord_427926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427965 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 3]
def baseStart_427965 : Nat := 118140960795 + 427965 * 2 ^ 59
def prefixEnd_427965 : Nat := 4983230072969 + 3 ^ 40 * 427965 * 2
def baseEnd_427965 : Nat := 195334887379131838817183

theorem tailTrace_427965 : CollatzResearch.WordTrace tailWord_427965 prefixEnd_427965 195334887379131838817183 := by
  unfold tailWord_427965
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609165894563370448069349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10406110596375580298712899 15609165894563370448069349)
  ·
    refine ⟨2926718605230631959013003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15609165894563370448069349 2926718605230631959013003)
    ·
      refine ⟨4390077907845947938519505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926718605230631959013003 4390077907845947938519505)
      ·
        refine ⟨3292558430884460953889629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4390077907845947938519505 3292558430884460953889629)
        ·
          refine ⟨1234709411581672857708611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3292558430884460953889629 1234709411581672857708611)
          ·
            refine ⟨1852064117372509286562917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234709411581672857708611 1852064117372509286562917)
            ·
              refine ⟨347262022007345491230547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1852064117372509286562917 347262022007345491230547)
              ·
                refine ⟨520893033011018236845821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347262022007345491230547 520893033011018236845821)
                ·
                  refine ⟨195334887379131838817183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520893033011018236845821 195334887379131838817183)
                  ·
                    rfl

theorem cell20_427965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_427965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427965 prefixEnd_427965 := by exact prefixLift 427965
  have htrace : WordTrace (prefixWord ++ tailWord_427965) baseStart_427965 baseEnd_427965 := by
    simpa [prefixWord, tailWord_427965, baseEnd_427965] using wordTrace_append hprefix tailTrace_427965
  have hstable : (prefixWord ++ tailWord_427965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427965).length < 2 ^ (prefixWord ++ tailWord_427965).sum := by decide
  have hdescent : baseEnd_427965 < baseStart_427965 := by decide
  rcases family_descends (prefixWord ++ tailWord_427965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427983 : List Nat := [1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_427983 : Nat := 118140960795 + 427983 * 2 ^ 59
def prefixEnd_427983 : Nat := 4983230072969 + 3 ^ 40 * 427983 * 2
def baseEnd_427983 : Nat := 65114367689867925405703

theorem tailTrace_427983 : CollatzResearch.WordTrace tailWord_427983 prefixEnd_427983 65114367689867925405703 := by
  unfold tailWord_427983
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609822408498159522224603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10406548272332106348149735 15609822408498159522224603)
  ·
    refine ⟨23414733612747239283336905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15609822408498159522224603 23414733612747239283336905)
    ·
      refine ⟨17561050209560429462502679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23414733612747239283336905 17561050209560429462502679)
      ·
        refine ⟨26341575314340644193754019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17561050209560429462502679 26341575314340644193754019)
        ·
          refine ⟨39512362971510966290631029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26341575314340644193754019 39512362971510966290631029)
          ·
            refine ⟨3704284028579153089746659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39512362971510966290631029 3704284028579153089746659)
            ·
              refine ⟨5556426042868729634619989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704284028579153089746659 5556426042868729634619989)
              ·
                refine ⟨65114367689867925405703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5556426042868729634619989 65114367689867925405703)
                ·
                  rfl

theorem cell20_427983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_427983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427983 prefixEnd_427983 := by exact prefixLift 427983
  have htrace : WordTrace (prefixWord ++ tailWord_427983) baseStart_427983 baseEnd_427983 := by
    simpa [prefixWord, tailWord_427983, baseEnd_427983] using wordTrace_append hprefix tailTrace_427983
  have hstable : (prefixWord ++ tailWord_427983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427983).length < 2 ^ (prefixWord ++ tailWord_427983).sum := by decide
  have hdescent : baseEnd_427983 < baseStart_427983 := by decide
  rcases family_descends (prefixWord ++ tailWord_427983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427996 : List Nat := [2, 2, 6, 1, 1, 8]
def baseStart_427996 : Nat := 118140960795 + 427996 * 2 ^ 59
def prefixEnd_427996 : Nat := 4983230072969 + 3 ^ 40 * 427996 * 2
def baseEnd_427996 : Nat := 7235149504586426251249

theorem tailTrace_427996 : CollatzResearch.WordTrace tailWord_427996 prefixEnd_427996 7235149504586426251249 := by
  unfold tailWord_427996
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805148278725531371223921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10406864371634041828298561 7805148278725531371223921)
  ·
    refine ⟨5853861209044148528417941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7805148278725531371223921 5853861209044148528417941)
    ·
      refine ⟨274399744173944462269591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5853861209044148528417941 274399744173944462269591)
      ·
        refine ⟨411599616260916693404387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274399744173944462269591 411599616260916693404387)
        ·
          refine ⟨617399424391375040106581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411599616260916693404387 617399424391375040106581)
          ·
            refine ⟨7235149504586426251249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 617399424391375040106581 7235149504586426251249)
            ·
              rfl

theorem cell20_427996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 8].length) (baseStart_427996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_427996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_427996 prefixEnd_427996 := by exact prefixLift 427996
  have htrace : WordTrace (prefixWord ++ tailWord_427996) baseStart_427996 baseEnd_427996 := by
    simpa [prefixWord, tailWord_427996, baseEnd_427996] using wordTrace_append hprefix tailTrace_427996
  have hstable : (prefixWord ++ tailWord_427996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427996).length < 2 ^ (prefixWord ++ tailWord_427996).sum := by decide
  have hdescent : baseEnd_427996 < baseStart_427996 := by decide
  rcases family_descends (prefixWord ++ tailWord_427996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428002 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_428002 : Nat := 118140960795 + 428002 * 2 ^ 59
def prefixEnd_428002 : Nat := 4983230072969 + 3 ^ 40 * 428002 * 2
def baseEnd_428002 : Nat := 195351775187324154583699

theorem tailTrace_428002 : CollatzResearch.WordTrace tailWord_428002 prefixEnd_428002 195351775187324154583699 := by
  unfold tailWord_428002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902628848857331441791565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10407010263619550511444173 3902628848857331441791565)
  ·
    refine ⟨1463485818321499290671837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3902628848857331441791565 1463485818321499290671837)
    ·
      refine ⟨548807181870562234001939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1463485818321499290671837 548807181870562234001939)
      ·
        refine ⟨823210772805843351002909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548807181870562234001939 823210772805843351002909)
        ·
          refine ⟨308704039802191256626091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 823210772805843351002909 308704039802191256626091)
          ·
            refine ⟨463056059703286884939137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308704039802191256626091 463056059703286884939137)
            ·
              refine ⟨347292044777465163704353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463056059703286884939137 347292044777465163704353)
              ·
                refine ⟨260469033583098872778265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347292044777465163704353 260469033583098872778265)
                ·
                  refine ⟨195351775187324154583699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260469033583098872778265 195351775187324154583699)
                  ·
                    rfl

theorem cell20_428002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_428002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428002 prefixEnd_428002 := by exact prefixLift 428002
  have htrace : WordTrace (prefixWord ++ tailWord_428002) baseStart_428002 baseEnd_428002 := by
    simpa [prefixWord, tailWord_428002, baseEnd_428002] using wordTrace_append hprefix tailTrace_428002
  have hstable : (prefixWord ++ tailWord_428002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428002).length < 2 ^ (prefixWord ++ tailWord_428002).sum := by decide
  have hdescent : baseEnd_428002 < baseStart_428002 := by decide
  rcases family_descends (prefixWord ++ tailWord_428002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428010 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_428010 : Nat := 118140960795 + 428010 * 2 ^ 59
def prefixEnd_428010 : Nat := 4983230072969 + 3 ^ 40 * 428010 * 2
def baseEnd_428010 : Nat := 195355426605311682316999

theorem tailTrace_428010 : CollatzResearch.WordTrace tailWord_428010 prefixEnd_428010 195355426605311682316999 := by
  unfold tailWord_428010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902701794850085783364371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10407204786266895422304989 3902701794850085783364371)
  ·
    refine ⟨5854052692275128675046557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3902701794850085783364371 5854052692275128675046557)
    ·
      refine ⟨2195269759603173253142459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5854052692275128675046557 2195269759603173253142459)
      ·
        refine ⟨3292904639404759879713689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195269759603173253142459 3292904639404759879713689)
        ·
          refine ⟨2469678479553569909785267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292904639404759879713689 2469678479553569909785267)
          ·
            refine ⟨3704517719330354864677901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469678479553569909785267 3704517719330354864677901)
            ·
              refine ⟨1389194144748883074254213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3704517719330354864677901 1389194144748883074254213)
              ·
                refine ⟨260473902140415576422665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1389194144748883074254213 260473902140415576422665)
                ·
                  refine ⟨195355426605311682316999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260473902140415576422665 195355426605311682316999)
                  ·
                    rfl

theorem cell20_428010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_428010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428010 prefixEnd_428010 := by exact prefixLift 428010
  have htrace : WordTrace (prefixWord ++ tailWord_428010) baseStart_428010 baseEnd_428010 := by
    simpa [prefixWord, tailWord_428010, baseEnd_428010] using wordTrace_append hprefix tailTrace_428010
  have hstable : (prefixWord ++ tailWord_428010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428010).length < 2 ^ (prefixWord ++ tailWord_428010).sum := by decide
  have hdescent : baseEnd_428010 < baseStart_428010 := by decide
  rcases family_descends (prefixWord ++ tailWord_428010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428013 : List Nat := [1, 5, 1, 4, 2, 1, 1, 5]
def baseStart_428013 : Nat := 118140960795 + 428013 * 2 ^ 59
def prefixEnd_428013 : Nat := 4983230072969 + 3 ^ 40 * 428013 * 2
def baseEnd_428013 : Nat := 65118931962352335072329

theorem tailTrace_428013 : CollatzResearch.WordTrace tailWord_428013 prefixEnd_428013 65118931962352335072329 := by
  unfold tailWord_428013
  simp only [CollatzResearch.WordTrace]
  refine ⟨15610916598389474645816693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10407277732259649763877795 15610916598389474645816693)
  ·
    refine ⟨1463523431099013248045315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15610916598389474645816693 1463523431099013248045315)
    ·
      refine ⟨2195285146648519872067973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463523431099013248045315 2195285146648519872067973)
      ·
        refine ⟨411615964996597476012745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2195285146648519872067973 411615964996597476012745)
        ·
          refine ⟨308711973747448107009559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411615964996597476012745 308711973747448107009559)
          ·
            refine ⟨463067960621172160514339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308711973747448107009559 463067960621172160514339)
            ·
              refine ⟨694601940931758240771509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463067960621172160514339 694601940931758240771509)
              ·
                refine ⟨65118931962352335072329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694601940931758240771509 65118931962352335072329)
                ·
                  rfl

theorem cell20_428013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_428013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428013 prefixEnd_428013 := by exact prefixLift 428013
  have htrace : WordTrace (prefixWord ++ tailWord_428013) baseStart_428013 baseEnd_428013 := by
    simpa [prefixWord, tailWord_428013, baseEnd_428013] using wordTrace_append hprefix tailTrace_428013
  have hstable : (prefixWord ++ tailWord_428013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428013).length < 2 ^ (prefixWord ++ tailWord_428013).sum := by decide
  have hdescent : baseEnd_428013 < baseStart_428013 := by decide
  rcases family_descends (prefixWord ++ tailWord_428013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428017 : List Nat := [1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_428017 : Nat := 118140960795 + 428017 * 2 ^ 59
def prefixEnd_428017 : Nat := 4983230072969 + 3 ^ 40 * 428017 * 2
def baseEnd_428017 : Nat := 65119540532016923027879

theorem tailTrace_428017 : CollatzResearch.WordTrace tailWord_428017 prefixEnd_428017 65119540532016923027879 := by
  unfold tailWord_428017
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611062490374983328962305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10407374993583322219308203 15611062490374983328962305)
  ·
    refine ⟨11708296867781237496721729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15611062490374983328962305 11708296867781237496721729)
    ·
      refine ⟨8781222650835928122541297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11708296867781237496721729 8781222650835928122541297)
      ·
        refine ⟨6585916988126946091905973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8781222650835928122541297 6585916988126946091905973)
        ·
          refine ⟨617429717636901196116185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6585916988126946091905973 617429717636901196116185)
          ·
            refine ⟨463072288227675897087139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617429717636901196116185 463072288227675897087139)
            ·
              refine ⟨694608432341513845630709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463072288227675897087139 694608432341513845630709)
              ·
                refine ⟨65119540532016923027879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694608432341513845630709 65119540532016923027879)
                ·
                  rfl

theorem cell20_428017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_428017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428017 prefixEnd_428017 := by exact prefixLift 428017
  have htrace : WordTrace (prefixWord ++ tailWord_428017) baseStart_428017 baseEnd_428017 := by
    simpa [prefixWord, tailWord_428017, baseEnd_428017] using wordTrace_append hprefix tailTrace_428017
  have hstable : (prefixWord ++ tailWord_428017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428017).length < 2 ^ (prefixWord ++ tailWord_428017).sum := by decide
  have hdescent : baseEnd_428017 < baseStart_428017 := by decide
  rcases family_descends (prefixWord ++ tailWord_428017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428069 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_428069 : Nat := 118140960795 + 428069 * 2 ^ 59
def prefixEnd_428069 : Nat := 4983230072969 + 3 ^ 40 * 428069 * 2
def baseEnd_428069 : Nat := 195382355812969699350091

theorem tailTrace_428069 : CollatzResearch.WordTrace tailWord_428069 prefixEnd_428069 195382355812969699350091 := by
  unfold tailWord_428069
  simp only [CollatzResearch.WordTrace]
  refine ⟨15612959086186596209855261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10408639390791064139903507 15612959086186596209855261)
  ·
    refine ⟨5854859657319973578695723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15612959086186596209855261 5854859657319973578695723)
    ·
      refine ⟨8782289485979960368043585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854859657319973578695723 8782289485979960368043585)
      ·
        refine ⟨6586717114484970276032689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8782289485979960368043585 6586717114484970276032689)
        ·
          refine ⟨4940037835863727707024517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6586717114484970276032689 4940037835863727707024517)
          ·
            refine ⟨926257094224448945067097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4940037835863727707024517 926257094224448945067097)
            ·
              refine ⟨694692820668336708800323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926257094224448945067097 694692820668336708800323)
              ·
                refine ⟨1042039231002505063200485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694692820668336708800323 1042039231002505063200485)
                ·
                  refine ⟨195382355812969699350091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042039231002505063200485 195382355812969699350091)
                  ·
                    rfl

theorem cell20_428069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_428069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428069 prefixEnd_428069 := by exact prefixLift 428069
  have htrace : WordTrace (prefixWord ++ tailWord_428069) baseStart_428069 baseEnd_428069 := by
    simpa [prefixWord, tailWord_428069, baseEnd_428069] using wordTrace_append hprefix tailTrace_428069
  have hstable : (prefixWord ++ tailWord_428069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428069).length < 2 ^ (prefixWord ++ tailWord_428069).sum := by decide
  have hdescent : baseEnd_428069 < baseStart_428069 := by decide
  rcases family_descends (prefixWord ++ tailWord_428069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428083 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_428083 : Nat := 118140960795 + 428083 * 2 ^ 59
def prefixEnd_428083 : Nat := 4983230072969 + 3 ^ 40 * 428083 * 2
def baseEnd_428083 : Nat := 195388745794447872883367

theorem tailTrace_428083 : CollatzResearch.WordTrace tailWord_428083 prefixEnd_428083 195388745794447872883367 := by
  unfold tailWord_428083
  simp only [CollatzResearch.WordTrace]
  refine ⟨15613469708135876600864903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10408979805423917733909935 15613469708135876600864903)
  ·
    refine ⟨23420204562203814901297355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15613469708135876600864903 23420204562203814901297355)
    ·
      refine ⟨35130306843305722351946033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23420204562203814901297355 35130306843305722351946033)
      ·
        refine ⟨26347730132479291763959525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35130306843305722351946033 26347730132479291763959525)
        ·
          refine ⟨4940199399839867205742411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26347730132479291763959525 4940199399839867205742411)
          ·
            refine ⟨7410299099759800808613617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940199399839867205742411 7410299099759800808613617)
            ·
              refine ⟨5557724324819850606460213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7410299099759800808613617 5557724324819850606460213)
              ·
                refine ⟨521036655451860994355645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5557724324819850606460213 521036655451860994355645)
                ·
                  refine ⟨195388745794447872883367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521036655451860994355645 195388745794447872883367)
                  ·
                    rfl

theorem cell20_428083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_428083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428083 prefixEnd_428083 := by exact prefixLift 428083
  have htrace : WordTrace (prefixWord ++ tailWord_428083) baseStart_428083 baseEnd_428083 := by
    simpa [prefixWord, tailWord_428083, baseEnd_428083] using wordTrace_append hprefix tailTrace_428083
  have hstable : (prefixWord ++ tailWord_428083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428083).length < 2 ^ (prefixWord ++ tailWord_428083).sum := by decide
  have hdescent : baseEnd_428083 < baseStart_428083 := by decide
  rcases family_descends (prefixWord ++ tailWord_428083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428121 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_428121 : Nat := 118140960795 + 428121 * 2 ^ 59
def prefixEnd_428121 : Nat := 4983230072969 + 3 ^ 40 * 428121 * 2
def baseEnd_428121 : Nat := 195406090029888629616545

theorem tailTrace_428121 : CollatzResearch.WordTrace tailWord_428121 prefixEnd_428121 195406090029888629616545 := by
  unfold tailWord_428121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614855681998209090748217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10409903787998806060498811 15614855681998209090748217)
  ·
    refine ⟨11711141761498656818061163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15614855681998209090748217 11711141761498656818061163)
    ·
      refine ⟨17566712642247985227091745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711141761498656818061163 17566712642247985227091745)
      ·
        refine ⟨13175034481685988920318809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17566712642247985227091745 13175034481685988920318809)
        ·
          refine ⟨9881275861264491690239107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13175034481685988920318809 9881275861264491690239107)
          ·
            refine ⟨14821913791896737535358661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881275861264491690239107 14821913791896737535358661)
            ·
              refine ⟨2779108835980638287879749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14821913791896737535358661 2779108835980638287879749)
              ·
                refine ⟨521082906746369678977453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2779108835980638287879749 521082906746369678977453)
                ·
                  refine ⟨195406090029888629616545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521082906746369678977453 195406090029888629616545)
                  ·
                    rfl

theorem cell20_428121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_428121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428121 prefixEnd_428121 := by exact prefixLift 428121
  have htrace : WordTrace (prefixWord ++ tailWord_428121) baseStart_428121 baseEnd_428121 := by
    simpa [prefixWord, tailWord_428121, baseEnd_428121] using wordTrace_append hprefix tailTrace_428121
  have hstable : (prefixWord ++ tailWord_428121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428121).length < 2 ^ (prefixWord ++ tailWord_428121).sum := by decide
  have hdescent : baseEnd_428121 < baseStart_428121 := by decide
  rcases family_descends (prefixWord ++ tailWord_428121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428124 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_428124 : Nat := 118140960795 + 428124 * 2 ^ 59
def prefixEnd_428124 : Nat := 4983230072969 + 3 ^ 40 * 428124 * 2
def baseEnd_428124 : Nat := 195407459311633952516533

theorem tailTrace_428124 : CollatzResearch.WordTrace tailWord_428124 prefixEnd_428124 195407459311633952516533 := by
  unfold tailWord_428124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807482550493670301553713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10409976733991560402071617 7807482550493670301553713)
  ·
    refine ⟨5855611912870252726165285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7807482550493670301553713 5855611912870252726165285)
    ·
      refine ⟨1097927233663172386155991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5855611912870252726165285 1097927233663172386155991)
      ·
        refine ⟨1646890850494758579233987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097927233663172386155991 1646890850494758579233987)
        ·
          refine ⟨2470336275742137868850981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646890850494758579233987 2470336275742137868850981)
          ·
            refine ⟨463188051701650850409559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2470336275742137868850981 463188051701650850409559)
            ·
              refine ⟨694782077552476275614339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463188051701650850409559 694782077552476275614339)
              ·
                refine ⟨1042173116328714413421509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694782077552476275614339 1042173116328714413421509)
                ·
                  refine ⟨195407459311633952516533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042173116328714413421509 195407459311633952516533)
                  ·
                    rfl

theorem cell20_428124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_428124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428124 prefixEnd_428124 := by exact prefixLift 428124
  have htrace : WordTrace (prefixWord ++ tailWord_428124) baseStart_428124 baseEnd_428124 := by
    simpa [prefixWord, tailWord_428124, baseEnd_428124] using wordTrace_append hprefix tailTrace_428124
  have hstable : (prefixWord ++ tailWord_428124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428124).length < 2 ^ (prefixWord ++ tailWord_428124).sum := by decide
  have hdescent : baseEnd_428124 < baseStart_428124 := by decide
  rcases family_descends (prefixWord ++ tailWord_428124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428186 : List Nat := [3, 1, 1, 5, 3, 1, 1, 5]
def baseStart_428186 : Nat := 118140960795 + 428186 * 2 ^ 59
def prefixEnd_428186 : Nat := 4983230072969 + 3 ^ 40 * 428186 * 2
def baseEnd_428186 : Nat := 65145252600345764149871

theorem tailTrace_428186 : CollatzResearch.WordTrace tailWord_428186 prefixEnd_428186 65145252600345764149871 := by
  unfold tailWord_428186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904306606690681297966103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10411484284508483461242941 3904306606690681297966103)
  ·
    refine ⟨5856459910036021946949155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3904306606690681297966103 5856459910036021946949155)
    ·
      refine ⟨8784689865054032920423733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856459910036021946949155 8784689865054032920423733)
      ·
        refine ⟨823564674848815586289725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8784689865054032920423733 823564674848815586289725)
        ·
          refine ⟨308836753068305844858647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 823564674848815586289725 308836753068305844858647)
          ·
            refine ⟨463255129602458767287971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308836753068305844858647 463255129602458767287971)
            ·
              refine ⟨694882694403688150931957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463255129602458767287971 694882694403688150931957)
              ·
                refine ⟨65145252600345764149871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694882694403688150931957 65145252600345764149871)
                ·
                  rfl

theorem cell20_428186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_428186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428186 prefixEnd_428186 := by exact prefixLift 428186
  have htrace : WordTrace (prefixWord ++ tailWord_428186) baseStart_428186 baseEnd_428186 := by
    simpa [prefixWord, tailWord_428186, baseEnd_428186] using wordTrace_append hprefix tailTrace_428186
  have hstable : (prefixWord ++ tailWord_428186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428186).length < 2 ^ (prefixWord ++ tailWord_428186).sum := by decide
  have hdescent : baseEnd_428186 < baseStart_428186 := by decide
  rcases family_descends (prefixWord ++ tailWord_428186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428197 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_428197 : Nat := 118140960795 + 428197 * 2 ^ 59
def prefixEnd_428197 : Nat := 4983230072969 + 3 ^ 40 * 428197 * 2
def baseEnd_428197 : Nat := 195440778500770143082901

theorem tailTrace_428197 : CollatzResearch.WordTrace tailWord_428197 prefixEnd_428197 195440778500770143082901 := by
  unfold tailWord_428197
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617627629722874070514845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10411751753148582713676563 15617627629722874070514845)
  ·
    refine ⟨5856610361146077776443067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15617627629722874070514845 5856610361146077776443067)
    ·
      refine ⟨8784915541719116664664601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856610361146077776443067 8784915541719116664664601)
      ·
        refine ⟨6588686656289337498498451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8784915541719116664664601 6588686656289337498498451)
        ·
          refine ⟨9883029984434006247747677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588686656289337498498451 9883029984434006247747677)
          ·
            refine ⟨3706136244162752342905379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9883029984434006247747677 3706136244162752342905379)
            ·
              refine ⟨5559204366244128514358069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706136244162752342905379 5559204366244128514358069)
              ·
                refine ⟨521175409335387048221069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5559204366244128514358069 521175409335387048221069)
                ·
                  refine ⟨195440778500770143082901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521175409335387048221069 195440778500770143082901)
                  ·
                    rfl

theorem cell20_428197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_428197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428197 prefixEnd_428197 := by exact prefixLift 428197
  have htrace : WordTrace (prefixWord ++ tailWord_428197) baseStart_428197 baseEnd_428197 := by
    simpa [prefixWord, tailWord_428197, baseEnd_428197] using wordTrace_append hprefix tailTrace_428197
  have hstable : (prefixWord ++ tailWord_428197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428197).length < 2 ^ (prefixWord ++ tailWord_428197).sum := by decide
  have hdescent : baseEnd_428197 < baseStart_428197 := by decide
  rcases family_descends (prefixWord ++ tailWord_428197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428228 : List Nat := [2, 3, 3, 1, 2, 2, 7]
def baseStart_428228 : Nat := 118140960795 + 428228 * 2 ^ 59
def prefixEnd_428228 : Nat := 4983230072969 + 3 ^ 40 * 428228 * 2
def baseEnd_428228 : Nat := 21717214193941312561049

theorem tailTrace_428228 : CollatzResearch.WordTrace tailWord_428228 prefixEnd_428228 21717214193941312561049 := by
  unfold tailWord_428228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809379146305283182446669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10412505528407044243262225 7809379146305283182446669)
  ·
    refine ⟨2928517179864481193417501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7809379146305283182446669 2928517179864481193417501)
    ·
      refine ⟨1098193942449180447531563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2928517179864481193417501 1098193942449180447531563)
      ·
        refine ⟨1647290913673770671297345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098193942449180447531563 1647290913673770671297345)
        ·
          refine ⟨1235468185255328003473009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647290913673770671297345 1235468185255328003473009)
          ·
            refine ⟨926601138941496002604757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235468185255328003473009 926601138941496002604757)
            ·
              refine ⟨21717214193941312561049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 926601138941496002604757 21717214193941312561049)
              ·
                rfl

theorem cell20_428228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_428228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428228 prefixEnd_428228 := by exact prefixLift 428228
  have htrace : WordTrace (prefixWord ++ tailWord_428228) baseStart_428228 baseEnd_428228 := by
    simpa [prefixWord, tailWord_428228, baseEnd_428228] using wordTrace_append hprefix tailTrace_428228
  have hstable : (prefixWord ++ tailWord_428228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428228).length < 2 ^ (prefixWord ++ tailWord_428228).sum := by decide
  have hdescent : baseEnd_428228 < baseStart_428228 := by decide
  rcases family_descends (prefixWord ++ tailWord_428228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428238 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_428238 : Nat := 118140960795 + 428238 * 2 ^ 59
def prefixEnd_428238 : Nat := 4983230072969 + 3 ^ 40 * 428238 * 2
def baseEnd_428238 : Nat := 195459492017956222716067

theorem tailTrace_428238 : CollatzResearch.WordTrace tailWord_428238 prefixEnd_428238 195459492017956222716067 := by
  unfold tailWord_428238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952390377821792259094671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10412748681716225381838245 1952390377821792259094671)
  ·
    refine ⟨2928585566732688388642007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952390377821792259094671 2928585566732688388642007)
    ·
      refine ⟨4392878350099032582963011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928585566732688388642007 4392878350099032582963011)
      ·
        refine ⟨6589317525148548874444517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392878350099032582963011 6589317525148548874444517)
        ·
          refine ⟨1235497035965352913958347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6589317525148548874444517 1235497035965352913958347)
          ·
            refine ⟨1853245553948029370937521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235497035965352913958347 1853245553948029370937521)
            ·
              refine ⟨1389934165461022028203141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853245553948029370937521 1389934165461022028203141)
              ·
                refine ⟨260612656023941630288089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1389934165461022028203141 260612656023941630288089)
                ·
                  refine ⟨195459492017956222716067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260612656023941630288089 195459492017956222716067)
                  ·
                    rfl

theorem cell20_428238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_428238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428238 prefixEnd_428238 := by exact prefixLift 428238
  have htrace : WordTrace (prefixWord ++ tailWord_428238) baseStart_428238 baseEnd_428238 := by
    simpa [prefixWord, tailWord_428238, baseEnd_428238] using wordTrace_append hprefix tailTrace_428238
  have hstable : (prefixWord ++ tailWord_428238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428238).length < 2 ^ (prefixWord ++ tailWord_428238).sum := by decide
  have hdescent : baseEnd_428238 < baseStart_428238 := by decide
  rcases family_descends (prefixWord ++ tailWord_428238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428258 : List Nat := [3, 3, 4, 1, 1, 2, 2, 4]
def baseStart_428258 : Nat := 118140960795 + 428258 * 2 ^ 59
def prefixEnd_428258 : Nat := 4983230072969 + 3 ^ 40 * 428258 * 2
def baseEnd_428258 : Nat := 65156206854308347349773

theorem tailTrace_428258 : CollatzResearch.WordTrace tailWord_428258 prefixEnd_428258 65156206854308347349773 := by
  unfold tailWord_428258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904963120625470372121357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10413234988334587658990285 3904963120625470372121357)
  ·
    refine ⟨1464361170234551389545509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3904963120625470372121357 1464361170234551389545509)
    ·
      refine ⟨274567719418978385539783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1464361170234551389545509 274567719418978385539783)
      ·
        refine ⟨411851579128467578309675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274567719418978385539783 411851579128467578309675)
        ·
          refine ⟨617777368692701367464513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411851579128467578309675 617777368692701367464513)
          ·
            refine ⟨463333026519526025598385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617777368692701367464513 463333026519526025598385)
            ·
              refine ⟨347499769889644519198789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463333026519526025598385 347499769889644519198789)
              ·
                refine ⟨65156206854308347349773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347499769889644519198789 65156206854308347349773)
                ·
                  rfl

theorem cell20_428258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_428258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428258 prefixEnd_428258 := by exact prefixLift 428258
  have htrace : WordTrace (prefixWord ++ tailWord_428258) baseStart_428258 baseEnd_428258 := by
    simpa [prefixWord, tailWord_428258, baseEnd_428258] using wordTrace_append hprefix tailTrace_428258
  have hstable : (prefixWord ++ tailWord_428258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428258).length < 2 ^ (prefixWord ++ tailWord_428258).sum := by decide
  have hdescent : baseEnd_428258 < baseStart_428258 := by decide
  rcases family_descends (prefixWord ++ tailWord_428258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428290 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_428290 : Nat := 118140960795 + 428290 * 2 ^ 59
def prefixEnd_428290 : Nat := 4983230072969 + 3 ^ 40 * 428290 * 2
def baseEnd_428290 : Nat := 195483226234875152982521

theorem tailTrace_428290 : CollatzResearch.WordTrace tailWord_428290 prefixEnd_428290 195483226234875152982521 := by
  unfold tailWord_428290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905254904596487738412581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10414013078923967302433549 3905254904596487738412581)
  ·
    refine ⟨732235294611841450952359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3905254904596487738412581 732235294611841450952359)
    ·
      refine ⟨1098352941917762176428539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732235294611841450952359 1098352941917762176428539)
      ·
        refine ⟨1647529412876643264642809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098352941917762176428539 1647529412876643264642809)
        ·
          refine ⟨1235647059657482448482107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647529412876643264642809 1235647059657482448482107)
          ·
            refine ⟨1853470589486223672723161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235647059657482448482107 1853470589486223672723161)
            ·
              refine ⟨1390102942114667754542371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853470589486223672723161 1390102942114667754542371)
              ·
                refine ⟨2085154413172001631813557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390102942114667754542371 2085154413172001631813557)
                ·
                  refine ⟨195483226234875152982521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2085154413172001631813557 195483226234875152982521)
                  ·
                    rfl

theorem cell20_428290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_428290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428290 prefixEnd_428290 := by exact prefixLift 428290
  have htrace : WordTrace (prefixWord ++ tailWord_428290) baseStart_428290 baseEnd_428290 := by
    simpa [prefixWord, tailWord_428290, baseEnd_428290] using wordTrace_append hprefix tailTrace_428290
  have hstable : (prefixWord ++ tailWord_428290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428290).length < 2 ^ (prefixWord ++ tailWord_428290).sum := by decide
  have hdescent : baseEnd_428290 < baseStart_428290 := by decide
  rcases family_descends (prefixWord ++ tailWord_428290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428297 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_428297 : Nat := 118140960795 + 428297 * 2 ^ 59
def prefixEnd_428297 : Nat := 4983230072969 + 3 ^ 40 * 428297 * 2
def baseEnd_428297 : Nat := 195486421225614239749159

theorem tailTrace_428297 : CollatzResearch.WordTrace tailWord_428297 prefixEnd_428297 195486421225614239749159 := by
  unfold tailWord_428297
  simp only [CollatzResearch.WordTrace]
  refine ⟨15621274929360591149155145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10414183286240394099436763 15621274929360591149155145)
  ·
    refine ⟨11715956197020443361866359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15621274929360591149155145 11715956197020443361866359)
    ·
      refine ⟨17573934295530665042799539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11715956197020443361866359 17573934295530665042799539)
      ·
        refine ⟨26360901443295997564199309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17573934295530665042799539 26360901443295997564199309)
        ·
          refine ⟨9885338041235999086574741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26360901443295997564199309 9885338041235999086574741)
          ·
            refine ⟨463375220682937457183191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9885338041235999086574741 463375220682937457183191)
            ·
              refine ⟨695062831024406185774787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463375220682937457183191 695062831024406185774787)
              ·
                refine ⟨1042594246536609278662181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695062831024406185774787 1042594246536609278662181)
                ·
                  refine ⟨195486421225614239749159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042594246536609278662181 195486421225614239749159)
                  ·
                    rfl

theorem cell20_428297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_428297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428297 prefixEnd_428297 := by exact prefixLift 428297
  have htrace : WordTrace (prefixWord ++ tailWord_428297) baseStart_428297 baseEnd_428297 := by
    simpa [prefixWord, tailWord_428297, baseEnd_428297] using wordTrace_append hprefix tailTrace_428297
  have hstable : (prefixWord ++ tailWord_428297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428297).length < 2 ^ (prefixWord ++ tailWord_428297).sum := by decide
  have hdescent : baseEnd_428297 < baseStart_428297 := by decide
  rcases family_descends (prefixWord ++ tailWord_428297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428332 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_428332 : Nat := 118140960795 + 428332 * 2 ^ 59
def prefixEnd_428332 : Nat := 4983230072969 + 3 ^ 40 * 428332 * 2
def baseEnd_428332 : Nat := 195502396179309673582349

theorem tailTrace_428332 : CollatzResearch.WordTrace tailWord_428332 prefixEnd_428332 195502396179309673582349 := by
  unfold tailWord_428332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811275742116896063339625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10415034322822528084452833 7811275742116896063339625)
  ·
    refine ⟨5858456806587672047504719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7811275742116896063339625 5858456806587672047504719)
    ·
      refine ⟨8787685209881508071257079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858456806587672047504719 8787685209881508071257079)
      ·
        refine ⟨13181527814822262106885619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787685209881508071257079 13181527814822262106885619)
        ·
          refine ⟨19772291722233393160328429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13181527814822262106885619 19772291722233393160328429)
          ·
            refine ⟨7414609395837522435123161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19772291722233393160328429 7414609395837522435123161)
            ·
              refine ⟨5560957046878141826342371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414609395837522435123161 5560957046878141826342371)
              ·
                refine ⟨8341435570317212739513557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560957046878141826342371 8341435570317212739513557)
                ·
                  refine ⟨195502396179309673582349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8341435570317212739513557 195502396179309673582349)
                  ·
                    rfl

theorem cell20_428332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_428332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428332 prefixEnd_428332 := by exact prefixLift 428332
  have htrace : WordTrace (prefixWord ++ tailWord_428332) baseStart_428332 baseEnd_428332 := by
    simpa [prefixWord, tailWord_428332, baseEnd_428332] using wordTrace_append hprefix tailTrace_428332
  have hstable : (prefixWord ++ tailWord_428332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428332).length < 2 ^ (prefixWord ++ tailWord_428332).sum := by decide
  have hdescent : baseEnd_428332 < baseStart_428332 := by decide
  rcases family_descends (prefixWord ++ tailWord_428332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428373 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_428373 : Nat := 118140960795 + 428373 * 2 ^ 59
def prefixEnd_428373 : Nat := 4983230072969 + 3 ^ 40 * 428373 * 2
def baseEnd_428373 : Nat := 195521109696495753215515

theorem tailTrace_428373 : CollatzResearch.WordTrace tailWord_428373 prefixEnd_428373 195521109696495753215515 := by
  unfold tailWord_428373
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624046877085256128921773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10416031251390170752614515 15624046877085256128921773)
  ·
    refine ⟨5859017578906971048345665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15624046877085256128921773 5859017578906971048345665)
    ·
      refine ⟨4394263184180228286259249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5859017578906971048345665 4394263184180228286259249)
      ·
        refine ⟨3295697388135171214694437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394263184180228286259249 3295697388135171214694437)
        ·
          refine ⟨617943260275344602755207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3295697388135171214694437 617943260275344602755207)
          ·
            refine ⟨926914890413016904132811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617943260275344602755207 926914890413016904132811)
            ·
              refine ⟨1390372335619525356199217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926914890413016904132811 1390372335619525356199217)
              ·
                refine ⟨1042779251714644017149413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390372335619525356199217 1042779251714644017149413)
                ·
                  refine ⟨195521109696495753215515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042779251714644017149413 195521109696495753215515)
                  ·
                    rfl

theorem cell20_428373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_428373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428373 prefixEnd_428373 := by exact prefixLift 428373
  have htrace : WordTrace (prefixWord ++ tailWord_428373) baseStart_428373 baseEnd_428373 := by
    simpa [prefixWord, tailWord_428373, baseEnd_428373] using wordTrace_append hprefix tailTrace_428373
  have hstable : (prefixWord ++ tailWord_428373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428373).length < 2 ^ (prefixWord ++ tailWord_428373).sum := by decide
  have hdescent : baseEnd_428373 < baseStart_428373 := by decide
  rcases family_descends (prefixWord ++ tailWord_428373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428382 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_428382 : Nat := 118140960795 + 428382 * 2 ^ 59
def prefixEnd_428382 : Nat := 4983230072969 + 3 ^ 40 * 428382 * 2
def baseEnd_428382 : Nat := 195525217541731721915479

theorem tailTrace_428382 : CollatzResearch.WordTrace tailWord_428382 prefixEnd_428382 195525217541731721915479 := by
  unfold tailWord_428382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953046891756581333249925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10416250089368433777332933 1953046891756581333249925)
  ·
    refine ⟨366196292204358999984361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1953046891756581333249925 366196292204358999984361)
    ·
      refine ⟨274647219153269249988271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366196292204358999984361 274647219153269249988271)
      ·
        refine ⟨411970828729903874982407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274647219153269249988271 411970828729903874982407)
        ·
          refine ⟨617956243094855812473611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411970828729903874982407 617956243094855812473611)
          ·
            refine ⟨926934364642283718710417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617956243094855812473611 926934364642283718710417)
            ·
              refine ⟨695200773481712789032813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926934364642283718710417 695200773481712789032813)
              ·
                refine ⟨260700290055642295887305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695200773481712789032813 260700290055642295887305)
                ·
                  refine ⟨195525217541731721915479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260700290055642295887305 195525217541731721915479)
                  ·
                    rfl

theorem cell20_428382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_428382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428382 prefixEnd_428382 := by exact prefixLift 428382
  have htrace : WordTrace (prefixWord ++ tailWord_428382) baseStart_428382 baseEnd_428382 := by
    simpa [prefixWord, tailWord_428382, baseEnd_428382] using wordTrace_append hprefix tailTrace_428382
  have hstable : (prefixWord ++ tailWord_428382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428382).length < 2 ^ (prefixWord ++ tailWord_428382).sum := by decide
  have hdescent : baseEnd_428382 < baseStart_428382 := by decide
  rcases family_descends (prefixWord ++ tailWord_428382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428411 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 2]
def baseStart_428411 : Nat := 118140960795 + 428411 * 2 ^ 59
def prefixEnd_428411 : Nat := 4983230072969 + 3 ^ 40 * 428411 * 2
def baseEnd_428411 : Nat := 195538453931936509948693

theorem tailTrace_428411 : CollatzResearch.WordTrace tailWord_428411 prefixEnd_428411 195538453931936509948693 := by
  unfold tailWord_428411
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625432850947588618805087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10416955233965059079203391 15625432850947588618805087)
  ·
    refine ⟨23438149276421382928207631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625432850947588618805087 23438149276421382928207631)
    ·
      refine ⟨35157223914632074392311447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438149276421382928207631 35157223914632074392311447)
      ·
        refine ⟨52735835871948111588467171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35157223914632074392311447 52735835871948111588467171)
        ·
          refine ⟨79103753807922167382700757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52735835871948111588467171 79103753807922167382700757)
          ·
            refine ⟨1853994229873175798032049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 79103753807922167382700757 1853994229873175798032049)
            ·
              refine ⟨1390495672404881848524037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853994229873175798032049 1390495672404881848524037)
              ·
                refine ⟨260717938575915346598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1390495672404881848524037 260717938575915346598257)
                ·
                  refine ⟨195538453931936509948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260717938575915346598257 195538453931936509948693)
                  ·
                    rfl

theorem cell20_428411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2].length) (baseStart_428411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428411 prefixEnd_428411 := by exact prefixLift 428411
  have htrace : WordTrace (prefixWord ++ tailWord_428411) baseStart_428411 baseEnd_428411 := by
    simpa [prefixWord, tailWord_428411, baseEnd_428411] using wordTrace_append hprefix tailTrace_428411
  have hstable : (prefixWord ++ tailWord_428411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428411).length < 2 ^ (prefixWord ++ tailWord_428411).sum := by decide
  have hdescent : baseEnd_428411 < baseStart_428411 := by decide
  rcases family_descends (prefixWord ++ tailWord_428411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428415 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_428415 : Nat := 118140960795 + 428415 * 2 ^ 59
def prefixEnd_428415 : Nat := 4983230072969 + 3 ^ 40 * 428415 * 2
def baseEnd_428415 : Nat := 195540279640930273815343

theorem tailTrace_428415 : CollatzResearch.WordTrace tailWord_428415 prefixEnd_428415 195540279640930273815343 := by
  unfold tailWord_428415
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625578742933097301950699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10417052495288731534633799 15625578742933097301950699)
  ·
    refine ⟨23438368114399645952926049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625578742933097301950699 23438368114399645952926049)
    ·
      refine ⟨17578776085799734464694537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23438368114399645952926049 17578776085799734464694537)
      ·
        refine ⟨13184082064349800848520903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17578776085799734464694537 13184082064349800848520903)
        ·
          refine ⟨19776123096524701272781355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184082064349800848520903 19776123096524701272781355)
          ·
            refine ⟨29664184644787051909172033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19776123096524701272781355 29664184644787051909172033)
            ·
              refine ⟨22248138483590288931879025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29664184644787051909172033 22248138483590288931879025)
              ·
                refine ⟨16686103862692716698909269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22248138483590288931879025 16686103862692716698909269)
                ·
                  refine ⟨195540279640930273815343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16686103862692716698909269 195540279640930273815343)
                  ·
                    rfl

theorem cell20_428415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_428415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428415 prefixEnd_428415 := by exact prefixLift 428415
  have htrace : WordTrace (prefixWord ++ tailWord_428415) baseStart_428415 baseEnd_428415 := by
    simpa [prefixWord, tailWord_428415, baseEnd_428415] using wordTrace_append hprefix tailTrace_428415
  have hstable : (prefixWord ++ tailWord_428415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428415).length < 2 ^ (prefixWord ++ tailWord_428415).sum := by decide
  have hdescent : baseEnd_428415 < baseStart_428415 := by decide
  rcases family_descends (prefixWord ++ tailWord_428415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428445 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 2]
def baseStart_428445 : Nat := 118140960795 + 428445 * 2 ^ 59
def prefixEnd_428445 : Nat := 4983230072969 + 3 ^ 40 * 428445 * 2
def baseEnd_428445 : Nat := 195553972458383502815221

theorem tailTrace_428445 : CollatzResearch.WordTrace tailWord_428445 prefixEnd_428445 195553972458383502815221 := by
  unfold tailWord_428445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15626672932824412425542789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10417781955216274950361859 15626672932824412425542789)
  ·
    refine ⟨2930001174904577329789273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15626672932824412425542789 2930001174904577329789273)
    ·
      refine ⟨2197500881178432997341955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2930001174904577329789273 2197500881178432997341955)
      ·
        refine ⟨3296251321767649496012933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197500881178432997341955 3296251321767649496012933)
        ·
          refine ⟨618047122831434280502425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3296251321767649496012933 618047122831434280502425)
          ·
            refine ⟨463535342123575710376819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618047122831434280502425 463535342123575710376819)
            ·
              refine ⟨695303013185363565565229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463535342123575710376819 695303013185363565565229)
              ·
                refine ⟨260738629944511337086961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695303013185363565565229 260738629944511337086961)
                ·
                  refine ⟨195553972458383502815221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260738629944511337086961 195553972458383502815221)
                  ·
                    rfl

theorem cell20_428445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_428445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428445 prefixEnd_428445 := by exact prefixLift 428445
  have htrace : WordTrace (prefixWord ++ tailWord_428445) baseStart_428445 baseEnd_428445 := by
    simpa [prefixWord, tailWord_428445, baseEnd_428445] using wordTrace_append hprefix tailTrace_428445
  have hstable : (prefixWord ++ tailWord_428445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428445).length < 2 ^ (prefixWord ++ tailWord_428445).sum := by decide
  have hdescent : baseEnd_428445 < baseStart_428445 := by decide
  rcases family_descends (prefixWord ++ tailWord_428445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428456 : List Nat := [2, 1, 6, 1, 1, 1, 8]
def baseStart_428456 : Nat := 118140960795 + 428456 * 2 ^ 59
def prefixEnd_428456 : Nat := 4983230072969 + 3 ^ 40 * 428456 * 2
def baseEnd_428456 : Nat := 21728777017568483716501

theorem tailTrace_428456 : CollatzResearch.WordTrace tailWord_428456 prefixEnd_428456 21728777017568483716501 := by
  unfold tailWord_428456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7813537067892280652096611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10418049423856374202795481 7813537067892280652096611)
  ·
    refine ⟨11720305601838420978144917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7813537067892280652096611 11720305601838420978144917)
    ·
      refine ⟨549389325086175983350543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11720305601838420978144917 549389325086175983350543)
      ·
        refine ⟨824083987629263975025815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549389325086175983350543 824083987629263975025815)
        ·
          refine ⟨1236125981443895962538723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824083987629263975025815 1236125981443895962538723)
          ·
            refine ⟨1854188972165843943808085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236125981443895962538723 1854188972165843943808085)
            ·
              refine ⟨21728777017568483716501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1854188972165843943808085 21728777017568483716501)
              ·
                rfl

theorem cell20_428456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_428456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428456 prefixEnd_428456 := by exact prefixLift 428456
  have htrace : WordTrace (prefixWord ++ tailWord_428456) baseStart_428456 baseEnd_428456 := by
    simpa [prefixWord, tailWord_428456, baseEnd_428456] using wordTrace_append hprefix tailTrace_428456
  have hstable : (prefixWord ++ tailWord_428456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428456).length < 2 ^ (prefixWord ++ tailWord_428456).sum := by decide
  have hdescent : baseEnd_428456 < baseStart_428456 := by decide
  rcases family_descends (prefixWord ++ tailWord_428456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428466 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_428466 : Nat := 118140960795 + 428466 * 2 ^ 59
def prefixEnd_428466 : Nat := 4983230072969 + 3 ^ 40 * 428466 * 2
def baseEnd_428466 : Nat := 195563557430600763115135

theorem tailTrace_428466 : CollatzResearch.WordTrace tailWord_428466 prefixEnd_428466 195563557430600763115135 := by
  unfold tailWord_428466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906859716437083253014313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10418292577165555341371501 3906859716437083253014313)
  ·
    refine ⟨2930144787327812439760735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3906859716437083253014313 2930144787327812439760735)
    ·
      refine ⟨4395217180991718659641103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930144787327812439760735 4395217180991718659641103)
      ·
        refine ⟨6592825771487577989461655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395217180991718659641103 6592825771487577989461655)
        ·
          refine ⟨9889238657231366984192483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592825771487577989461655 9889238657231366984192483)
          ·
            refine ⟨14833857985847050476288725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9889238657231366984192483 14833857985847050476288725)
            ·
              refine ⟨347668546543290245538017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14833857985847050476288725 347668546543290245538017)
              ·
                refine ⟨260751409907467684153513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347668546543290245538017 260751409907467684153513)
                ·
                  refine ⟨195563557430600763115135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260751409907467684153513 195563557430600763115135)
                  ·
                    rfl

theorem cell20_428466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_428466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428466 prefixEnd_428466 := by exact prefixLift 428466
  have htrace : WordTrace (prefixWord ++ tailWord_428466) baseStart_428466 baseEnd_428466 := by
    simpa [prefixWord, tailWord_428466, baseEnd_428466] using wordTrace_append hprefix tailTrace_428466
  have hstable : (prefixWord ++ tailWord_428466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428466).length < 2 ^ (prefixWord ++ tailWord_428466).sum := by decide
  have hdescent : baseEnd_428466 < baseStart_428466 := by decide
  rcases family_descends (prefixWord ++ tailWord_428466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428477 : List Nat := [1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_428477 : Nat := 118140960795 + 428477 * 2 ^ 59
def prefixEnd_428477 : Nat := 4983230072969 + 3 ^ 40 * 428477 * 2
def baseEnd_428477 : Nat := 65189526043444537916141

theorem tailTrace_428477 : CollatzResearch.WordTrace tailWord_428477 prefixEnd_428477 65189526043444537916141 := by
  unfold tailWord_428477
  simp only [CollatzResearch.WordTrace]
  refine ⟨15627840068708481890707685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10418560045805654593805123 15627840068708481890707685)
  ·
    refine ⟨2930220012882840354507691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15627840068708481890707685 2930220012882840354507691)
    ·
      refine ⟨4395330019324260531761537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930220012882840354507691 4395330019324260531761537)
      ·
        refine ⟨3296497514493195398821153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4395330019324260531761537 3296497514493195398821153)
        ·
          refine ⟨2472373135869896549115865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296497514493195398821153 2472373135869896549115865)
          ·
            refine ⟨1854279851902422411836899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472373135869896549115865 1854279851902422411836899)
            ·
              refine ⟨2781419777853633617755349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854279851902422411836899 2781419777853633617755349)
              ·
                refine ⟨65189526043444537916141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2781419777853633617755349 65189526043444537916141)
                ·
                  rfl

theorem cell20_428477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_428477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428477 prefixEnd_428477 := by exact prefixLift 428477
  have htrace : WordTrace (prefixWord ++ tailWord_428477) baseStart_428477 baseEnd_428477 := by
    simpa [prefixWord, tailWord_428477, baseEnd_428477] using wordTrace_append hprefix tailTrace_428477
  have hstable : (prefixWord ++ tailWord_428477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428477).length < 2 ^ (prefixWord ++ tailWord_428477).sum := by decide
  have hdescent : baseEnd_428477 < baseStart_428477 := by decide
  rcases family_descends (prefixWord ++ tailWord_428477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428491 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_428491 : Nat := 118140960795 + 428491 * 2 ^ 59
def prefixEnd_428491 : Nat := 4983230072969 + 3 ^ 40 * 428491 * 2
def baseEnd_428491 : Nat := 195574968111811787281699

theorem tailTrace_428491 : CollatzResearch.WordTrace tailWord_428491 prefixEnd_428491 195574968111811787281699 := by
  unfold tailWord_428491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628350690657762281717327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10418900460438508187811551 15628350690657762281717327)
  ·
    refine ⟨23442526035986643422575991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15628350690657762281717327 23442526035986643422575991)
    ·
      refine ⟨35163789053979965133863987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442526035986643422575991 35163789053979965133863987)
      ·
        refine ⟨52745683580969947700795981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35163789053979965133863987 52745683580969947700795981)
        ·
          refine ⟨19779631342863730387798493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52745683580969947700795981 19779631342863730387798493)
          ·
            refine ⟨7417361753573898895424435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19779631342863730387798493 7417361753573898895424435)
            ·
              refine ⟨11126042630360848343136653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417361753573898895424435 11126042630360848343136653)
              ·
                refine ⟨4172265986385318128676245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11126042630360848343136653 4172265986385318128676245)
                ·
                  refine ⟨195574968111811787281699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4172265986385318128676245 195574968111811787281699)
                  ·
                    rfl

theorem cell20_428491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_428491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428491 prefixEnd_428491 := by exact prefixLift 428491
  have htrace : WordTrace (prefixWord ++ tailWord_428491) baseStart_428491 baseEnd_428491 := by
    simpa [prefixWord, tailWord_428491, baseEnd_428491] using wordTrace_append hprefix tailTrace_428491
  have hstable : (prefixWord ++ tailWord_428491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428491).length < 2 ^ (prefixWord ++ tailWord_428491).sum := by decide
  have hdescent : baseEnd_428491 < baseStart_428491 := by decide
  rcases family_descends (prefixWord ++ tailWord_428491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428514 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_428514 : Nat := 118140960795 + 428514 * 2 ^ 59
def prefixEnd_428514 : Nat := 4983230072969 + 3 ^ 40 * 428514 * 2
def baseEnd_428514 : Nat := 195585465938525929514939

theorem tailTrace_428514 : CollatzResearch.WordTrace tailWord_428514 prefixEnd_428514 195585465938525929514939 := by
  unfold tailWord_428514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907297392393609302451149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10419459713049624806536397 3907297392393609302451149)
  ·
    refine ⟨1465236522147603488419181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3907297392393609302451149 1465236522147603488419181)
    ·
      refine ⟨549463695805351308157193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1465236522147603488419181 549463695805351308157193)
      ·
        refine ⟨412097771854013481117895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549463695805351308157193 412097771854013481117895)
        ·
          refine ⟨618146657781020221676843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412097771854013481117895 618146657781020221676843)
          ·
            refine ⟨927219986671530332515265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618146657781020221676843 927219986671530332515265)
            ·
              refine ⟨695414990003647749386449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927219986671530332515265 695414990003647749386449)
              ·
                refine ⟨521561242502735812039837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695414990003647749386449 521561242502735812039837)
                ·
                  refine ⟨195585465938525929514939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521561242502735812039837 195585465938525929514939)
                  ·
                    rfl

theorem cell20_428514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_428514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428514 prefixEnd_428514 := by exact prefixLift 428514
  have htrace : WordTrace (prefixWord ++ tailWord_428514) baseStart_428514 baseEnd_428514 := by
    simpa [prefixWord, tailWord_428514, baseEnd_428514] using wordTrace_append hprefix tailTrace_428514
  have hstable : (prefixWord ++ tailWord_428514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428514).length < 2 ^ (prefixWord ++ tailWord_428514).sum := by decide
  have hdescent : baseEnd_428514 < baseStart_428514 := by decide
  rcases family_descends (prefixWord ++ tailWord_428514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428515 : List Nat := [1, 1, 1, 6, 3, 8]
def baseStart_428515 : Nat := 118140960795 + 428515 * 2 ^ 59
def prefixEnd_428515 : Nat := 4983230072969 + 3 ^ 40 * 428515 * 2
def baseEnd_428515 : Nat := 7243923050584235943763

theorem tailTrace_428515 : CollatzResearch.WordTrace tailWord_428515 prefixEnd_428515 7243923050584235943763 := by
  unfold tailWord_428515
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629226042570814380590999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10419484028380542920393999 15629226042570814380590999)
  ·
    refine ⟨23443839063856221570886499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15629226042570814380590999 23443839063856221570886499)
    ·
      refine ⟨35165758595784332356329749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443839063856221570886499 35165758595784332356329749)
      ·
        refine ⟨1648394934177390579202957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35165758595784332356329749 1648394934177390579202957)
        ·
          refine ⟨618148100316521467201109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1648394934177390579202957 618148100316521467201109)
          ·
            refine ⟨7243923050584235943763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 618148100316521467201109 7243923050584235943763)
            ·
              rfl

theorem cell20_428515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 8].length) (baseStart_428515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428515 prefixEnd_428515 := by exact prefixLift 428515
  have htrace : WordTrace (prefixWord ++ tailWord_428515) baseStart_428515 baseEnd_428515 := by
    simpa [prefixWord, tailWord_428515, baseEnd_428515] using wordTrace_append hprefix tailTrace_428515
  have hstable : (prefixWord ++ tailWord_428515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428515).length < 2 ^ (prefixWord ++ tailWord_428515).sum := by decide
  have hdescent : baseEnd_428515 < baseStart_428515 := by decide
  rcases family_descends (prefixWord ++ tailWord_428515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428563 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 2]
def baseStart_428563 : Nat := 118140960795 + 428563 * 2 ^ 59
def prefixEnd_428563 : Nat := 4983230072969 + 3 ^ 40 * 428563 * 2
def baseEnd_428563 : Nat := 195607830873699536881405

theorem tailTrace_428563 : CollatzResearch.WordTrace tailWord_428563 prefixEnd_428563 195607830873699536881405 := by
  unfold tailWord_428563
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630976746396918578338343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10420651164264612385558895 15630976746396918578338343)
  ·
    refine ⟨23446465119595377867507515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630976746396918578338343 23446465119595377867507515)
    ·
      refine ⟨35169697679393066801261273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23446465119595377867507515 35169697679393066801261273)
      ·
        refine ⟨26377273259544800100945955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35169697679393066801261273 26377273259544800100945955)
        ·
          refine ⟨39565909889317200151418933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26377273259544800100945955 39565909889317200151418933)
          ·
            refine ⟨3709304052123487514195525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39565909889317200151418933 3709304052123487514195525)
            ·
              refine ⟨695494509773153908911661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3709304052123487514195525 695494509773153908911661)
              ·
                refine ⟨260810441164932715841873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695494509773153908911661 260810441164932715841873)
                ·
                  refine ⟨195607830873699536881405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260810441164932715841873 195607830873699536881405)
                  ·
                    rfl

theorem cell20_428563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2].length) (baseStart_428563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428563 prefixEnd_428563 := by exact prefixLift 428563
  have htrace : WordTrace (prefixWord ++ tailWord_428563) baseStart_428563 baseEnd_428563 := by
    simpa [prefixWord, tailWord_428563, baseEnd_428563] using wordTrace_append hprefix tailTrace_428563
  have hstable : (prefixWord ++ tailWord_428563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428563).length < 2 ^ (prefixWord ++ tailWord_428563).sum := by decide
  have hdescent : baseEnd_428563 < baseStart_428563 := by decide
  rcases family_descends (prefixWord ++ tailWord_428563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428580 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_428580 : Nat := 118140960795 + 428580 * 2 ^ 59
def prefixEnd_428580 : Nat := 4983230072969 + 3 ^ 40 * 428580 * 2
def baseEnd_428580 : Nat := 195615590136923033314669

theorem tailTrace_428580 : CollatzResearch.WordTrace tailWord_428580 prefixEnd_428580 195615590136923033314669 := by
  unfold tailWord_428580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815798393667665240853597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10421064524890220321138129 7815798393667665240853597)
  ·
    refine ⟨2930924397625374465320099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7815798393667665240853597 2930924397625374465320099)
    ·
      refine ⟨4396386596438061697980149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930924397625374465320099 4396386596438061697980149)
      ·
        refine ⟨412161243416068284185639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4396386596438061697980149 412161243416068284185639)
        ·
          refine ⟨618241865124102426278459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412161243416068284185639 618241865124102426278459)
          ·
            refine ⟨927362797686153639417689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618241865124102426278459 927362797686153639417689)
            ·
              refine ⟨695522098264615229563267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927362797686153639417689 695522098264615229563267)
              ·
                refine ⟨1043283147396922844344901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695522098264615229563267 1043283147396922844344901)
                ·
                  refine ⟨195615590136923033314669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043283147396922844344901 195615590136923033314669)
                  ·
                    rfl

theorem cell20_428580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_428580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428580 prefixEnd_428580 := by exact prefixLift 428580
  have htrace : WordTrace (prefixWord ++ tailWord_428580) baseStart_428580 baseEnd_428580 := by
    simpa [prefixWord, tailWord_428580, baseEnd_428580] using wordTrace_append hprefix tailTrace_428580
  have hstable : (prefixWord ++ tailWord_428580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428580).length < 2 ^ (prefixWord ++ tailWord_428580).sum := by decide
  have hdescent : baseEnd_428580 < baseStart_428580 := by decide
  rcases family_descends (prefixWord ++ tailWord_428580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428614 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_428614 : Nat := 118140960795 + 428614 * 2 ^ 59
def prefixEnd_428614 : Nat := 4983230072969 + 3 ^ 40 * 428614 * 2
def baseEnd_428614 : Nat := 195631108663370026181197

theorem tailTrace_428614 : CollatzResearch.WordTrace tailWord_428614 prefixEnd_428614 195631108663370026181197 := by
  unfold tailWord_428614
  simp only [CollatzResearch.WordTrace]
  refine ⟨488526152162879821513903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10421891246141436192296597 488526152162879821513903)
  ·
    refine ⟨732789228244319732270855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488526152162879821513903 732789228244319732270855)
    ·
      refine ⟨1099183842366479598406283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732789228244319732270855 1099183842366479598406283)
      ·
        refine ⟨1648775763549719397609425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099183842366479598406283 1648775763549719397609425)
        ·
          refine ⟨1236581822662289548207069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1648775763549719397609425 1236581822662289548207069)
          ·
            refine ⟨463718183498358580577651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236581822662289548207069 463718183498358580577651)
            ·
              refine ⟨695577275247537870866477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463718183498358580577651 695577275247537870866477)
              ·
                refine ⟨260841478217826701574929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695577275247537870866477 260841478217826701574929)
                ·
                  refine ⟨195631108663370026181197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260841478217826701574929 195631108663370026181197)
                  ·
                    rfl

theorem cell20_428614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_428614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428614 prefixEnd_428614 := by exact prefixLift 428614
  have htrace : WordTrace (prefixWord ++ tailWord_428614) baseStart_428614 baseEnd_428614 := by
    simpa [prefixWord, tailWord_428614, baseEnd_428614] using wordTrace_append hprefix tailTrace_428614
  have hstable : (prefixWord ++ tailWord_428614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428614).length < 2 ^ (prefixWord ++ tailWord_428614).sum := by decide
  have hdescent : baseEnd_428614 < baseStart_428614 := by decide
  rcases family_descends (prefixWord ++ tailWord_428614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428618 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_428618 : Nat := 118140960795 + 428618 * 2 ^ 59
def prefixEnd_428618 : Nat := 4983230072969 + 3 ^ 40 * 428618 * 2
def baseEnd_428618 : Nat := 195632934372363790047847

theorem tailTrace_428618 : CollatzResearch.WordTrace tailWord_428618 prefixEnd_428618 195632934372363790047847 := by
  unfold tailWord_428618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908245690299415742897627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10421988507465108647727005 3908245690299415742897627)
  ·
    refine ⟨5862368535449123614346441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3908245690299415742897627 5862368535449123614346441)
    ·
      refine ⟨4396776401586842710759831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5862368535449123614346441 4396776401586842710759831)
      ·
        refine ⟨6595164602380264066139747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396776401586842710759831 6595164602380264066139747)
        ·
          refine ⟨9892746903570396099209621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595164602380264066139747 9892746903570396099209621)
          ·
            refine ⟨463722511104862317150451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9892746903570396099209621 463722511104862317150451)
            ·
              refine ⟨695583766657293475725677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463722511104862317150451 695583766657293475725677)
              ·
                refine ⟨260843912496485053397129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695583766657293475725677 260843912496485053397129)
                ·
                  refine ⟨195632934372363790047847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260843912496485053397129 195632934372363790047847)
                  ·
                    rfl

theorem cell20_428618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_428618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428618 prefixEnd_428618 := by exact prefixLift 428618
  have htrace : WordTrace (prefixWord ++ tailWord_428618) baseStart_428618 baseEnd_428618 := by
    simpa [prefixWord, tailWord_428618, baseEnd_428618] using wordTrace_append hprefix tailTrace_428618
  have hstable : (prefixWord ++ tailWord_428618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428618).length < 2 ^ (prefixWord ++ tailWord_428618).sum := by decide
  have hdescent : baseEnd_428618 < baseStart_428618 := by decide
  rcases family_descends (prefixWord ++ tailWord_428618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428719 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_428719 : Nat := 118140960795 + 428719 * 2 ^ 59
def prefixEnd_428719 : Nat := 4983230072969 + 3 ^ 40 * 428719 * 2
def baseEnd_428719 : Nat := 195679033524456327680767

theorem tailTrace_428719 : CollatzResearch.WordTrace tailWord_428719 prefixEnd_428719 195679033524456327680767 := by
  unfold tailWord_428719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636666533831757221017211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10424444355887838147344807 15636666533831757221017211)
  ·
    refine ⟨23454999800747635831525817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15636666533831757221017211 23454999800747635831525817)
    ·
      refine ⟨17591249850560726873644363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23454999800747635831525817 17591249850560726873644363)
      ·
        refine ⟨26386874775841090310466545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17591249850560726873644363 26386874775841090310466545)
        ·
          refine ⟨19790156081880817732849909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26386874775841090310466545 19790156081880817732849909)
          ·
            refine ⟨1855327132676326662454679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19790156081880817732849909 1855327132676326662454679)
            ·
              refine ⟨2782990699014489993682019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855327132676326662454679 2782990699014489993682019)
              ·
                refine ⟨4174486048521734990523029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782990699014489993682019 4174486048521734990523029)
                ·
                  refine ⟨195679033524456327680767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4174486048521734990523029 195679033524456327680767)
                  ·
                    rfl

theorem cell20_428719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_428719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428719 prefixEnd_428719 := by exact prefixLift 428719
  have htrace : WordTrace (prefixWord ++ tailWord_428719) baseStart_428719 baseEnd_428719 := by
    simpa [prefixWord, tailWord_428719, baseEnd_428719] using wordTrace_append hprefix tailTrace_428719
  have hstable : (prefixWord ++ tailWord_428719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428719).length < 2 ^ (prefixWord ++ tailWord_428719).sum := by decide
  have hdescent : baseEnd_428719 < baseStart_428719 := by decide
  rcases family_descends (prefixWord ++ tailWord_428719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428746 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_428746 : Nat := 118140960795 + 428746 * 2 ^ 59
def prefixEnd_428746 : Nat := 4983230072969 + 3 ^ 40 * 428746 * 2
def baseEnd_428746 : Nat := 195691357060164233780657

theorem tailTrace_428746 : CollatzResearch.WordTrace tailWord_428746 prefixEnd_428746 195691357060164233780657 := by
  unfold tailWord_428746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909412826183485208062523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10425100869822627221500061 3909412826183485208062523)
  ·
    refine ⟨5864119239275227812093785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3909412826183485208062523 5864119239275227812093785)
    ·
      refine ⟨4398089429456420859070339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5864119239275227812093785 4398089429456420859070339)
      ·
        refine ⟨6597134144184631288605509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398089429456420859070339 6597134144184631288605509)
        ·
          refine ⟨1236962652034618366613533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6597134144184631288605509 1236962652034618366613533)
          ·
            refine ⟨463860994512981887480075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236962652034618366613533 463860994512981887480075)
            ·
              refine ⟨695791491769472831220113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463860994512981887480075 695791491769472831220113)
              ·
                refine ⟨521843618827104623415085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695791491769472831220113 521843618827104623415085)
                ·
                  refine ⟨195691357060164233780657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521843618827104623415085 195691357060164233780657)
                  ·
                    rfl

theorem cell20_428746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_428746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428746 prefixEnd_428746 := by exact prefixLift 428746
  have htrace : WordTrace (prefixWord ++ tailWord_428746) baseStart_428746 baseEnd_428746 := by
    simpa [prefixWord, tailWord_428746, baseEnd_428746] using wordTrace_append hprefix tailTrace_428746
  have hstable : (prefixWord ++ tailWord_428746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428746).length < 2 ^ (prefixWord ++ tailWord_428746).sum := by decide
  have hdescent : baseEnd_428746 < baseStart_428746 := by decide
  rcases family_descends (prefixWord ++ tailWord_428746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428781 : List Nat := [1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_428781 : Nat := 118140960795 + 428781 * 2 ^ 59
def prefixEnd_428781 : Nat := 4983230072969 + 3 ^ 40 * 428781 * 2
def baseEnd_428781 : Nat := 65235777337953222537949

theorem tailTrace_428781 : CollatzResearch.WordTrace tailWord_428781 prefixEnd_428781 65235777337953222537949 := by
  unfold tailWord_428781
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638927859607141809774197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10425951906404761206516131 15638927859607141809774197)
  ·
    refine ⟨1466149486838169544666331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15638927859607141809774197 1466149486838169544666331)
    ·
      refine ⟨2199224230257254316999497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466149486838169544666331 2199224230257254316999497)
      ·
        refine ⟨1649418172692940737749623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199224230257254316999497 1649418172692940737749623)
        ·
          refine ⟨2474127259039411106624435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649418172692940737749623 2474127259039411106624435)
          ·
            refine ⟨3711190888559116659936653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474127259039411106624435 3711190888559116659936653)
            ·
              refine ⟨1391696583209668747476245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3711190888559116659936653 1391696583209668747476245)
              ·
                refine ⟨65235777337953222537949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391696583209668747476245 65235777337953222537949)
                ·
                  rfl

theorem cell20_428781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_428781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428781 prefixEnd_428781 := by exact prefixLift 428781
  have htrace : WordTrace (prefixWord ++ tailWord_428781) baseStart_428781 baseEnd_428781 := by
    simpa [prefixWord, tailWord_428781, baseEnd_428781] using wordTrace_append hprefix tailTrace_428781
  have hstable : (prefixWord ++ tailWord_428781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428781).length < 2 ^ (prefixWord ++ tailWord_428781).sum := by decide
  have hdescent : baseEnd_428781 < baseStart_428781 := by decide
  rcases family_descends (prefixWord ++ tailWord_428781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428798 : List Nat := [4, 2, 2, 1, 2, 3, 6]
def baseStart_428798 : Nat := 118140960795 + 428798 * 2 ^ 59
def prefixEnd_428798 : Nat := 4983230072969 + 3 ^ 40 * 428798 * 2
def baseEnd_428798 : Nat := 21746121253009240449679

theorem tailTrace_428798 : CollatzResearch.WordTrace tailWord_428798 prefixEnd_428798 21746121253009240449679 := by
  unfold tailWord_428798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954943487568194214142881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10426365267030369142095365 1954943487568194214142881)
  ·
    refine ⟨1466207615676145660607161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954943487568194214142881 1466207615676145660607161)
    ·
      refine ⟨1099655711757109245455371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466207615676145660607161 1099655711757109245455371)
      ·
        refine ⟨1649483567635663868183057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099655711757109245455371 1649483567635663868183057)
        ·
          refine ⟨1237112675726747901137293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1649483567635663868183057 1237112675726747901137293)
          ·
            refine ⟨463917253397530462926485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1237112675726747901137293 463917253397530462926485)
            ·
              refine ⟨21746121253009240449679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 463917253397530462926485 21746121253009240449679)
              ·
                rfl

theorem cell20_428798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_428798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428798 prefixEnd_428798 := by exact prefixLift 428798
  have htrace : WordTrace (prefixWord ++ tailWord_428798) baseStart_428798 baseEnd_428798 := by
    simpa [prefixWord, tailWord_428798, baseEnd_428798] using wordTrace_append hprefix tailTrace_428798
  have hstable : (prefixWord ++ tailWord_428798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428798).length < 2 ^ (prefixWord ++ tailWord_428798).sum := by decide
  have hdescent : baseEnd_428798 < baseStart_428798 := by decide
  rcases family_descends (prefixWord ++ tailWord_428798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428808 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_428808 : Nat := 118140960795 + 428808 * 2 ^ 59
def prefixEnd_428808 : Nat := 4983230072969 + 3 ^ 40 * 428808 * 2
def baseEnd_428808 : Nat := 195719655549567573713737

theorem tailTrace_428808 : CollatzResearch.WordTrace tailWord_428808 prefixEnd_428808 195719655549567573713737 := by
  unfold tailWord_428808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819956315254662710503539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10426608420339550280671385 7819956315254662710503539)
  ·
    refine ⟨11729934472881994065755309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819956315254662710503539 11729934472881994065755309)
    ·
      refine ⟨4398725427330747774658241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11729934472881994065755309 4398725427330747774658241)
      ·
        refine ⟨3299044070498060830993681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4398725427330747774658241 3299044070498060830993681)
        ·
          refine ⟨2474283052873545623245261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299044070498060830993681 2474283052873545623245261)
          ·
            refine ⟨927856144827579608716973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2474283052873545623245261 927856144827579608716973)
            ·
              refine ⟨347946054310342353268865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927856144827579608716973 347946054310342353268865)
              ·
                refine ⟨260959540732756764951649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347946054310342353268865 260959540732756764951649)
                ·
                  refine ⟨195719655549567573713737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260959540732756764951649 195719655549567573713737)
                  ·
                    rfl

theorem cell20_428808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_428808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428808 prefixEnd_428808 := by exact prefixLift 428808
  have htrace : WordTrace (prefixWord ++ tailWord_428808) baseStart_428808 baseEnd_428808 := by
    simpa [prefixWord, tailWord_428808, baseEnd_428808] using wordTrace_append hprefix tailTrace_428808
  have hstable : (prefixWord ++ tailWord_428808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428808).length < 2 ^ (prefixWord ++ tailWord_428808).sum := by decide
  have hdescent : baseEnd_428808 < baseStart_428808 := by decide
  rcases family_descends (prefixWord ++ tailWord_428808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428818 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_428818 : Nat := 118140960795 + 428818 * 2 ^ 59
def prefixEnd_428818 : Nat := 4983230072969 + 3 ^ 40 * 428818 * 2
def baseEnd_428818 : Nat := 195724219822051983380363

theorem tailTrace_428818 : CollatzResearch.WordTrace tailWord_428818 prefixEnd_428818 195724219822051983380363 := by
  unfold tailWord_428818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910069340118274282217777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10426851573648731419247405 3910069340118274282217777)
  ·
    refine ⟨2932552005088705711663333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3910069340118274282217777 2932552005088705711663333)
    ·
      refine ⟨549853500954132320936875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2932552005088705711663333 549853500954132320936875)
      ·
        refine ⟨824780251431198481405313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549853500954132320936875 824780251431198481405313)
        ·
          refine ⟨618585188573398861053985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824780251431198481405313 618585188573398861053985)
          ·
            refine ⟨463938891430049145790489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618585188573398861053985 463938891430049145790489)
            ·
              refine ⟨347954168572536859342867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463938891430049145790489 347954168572536859342867)
              ·
                refine ⟨521931252858805289014301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347954168572536859342867 521931252858805289014301)
                ·
                  refine ⟨195724219822051983380363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521931252858805289014301 195724219822051983380363)
                  ·
                    rfl

theorem cell20_428818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_428818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428818 prefixEnd_428818 := by exact prefixLift 428818
  have htrace : WordTrace (prefixWord ++ tailWord_428818) baseStart_428818 baseEnd_428818 := by
    simpa [prefixWord, tailWord_428818, baseEnd_428818] using wordTrace_append hprefix tailTrace_428818
  have hstable : (prefixWord ++ tailWord_428818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428818).length < 2 ^ (prefixWord ++ tailWord_428818).sum := by decide
  have hdescent : baseEnd_428818 < baseStart_428818 := by decide
  rcases family_descends (prefixWord ++ tailWord_428818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428833 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_428833 : Nat := 118140960795 + 428833 * 2 ^ 59
def prefixEnd_428833 : Nat := 4983230072969 + 3 ^ 40 * 428833 * 2
def baseEnd_428833 : Nat := 195731066230778597880301

theorem tailTrace_428833 : CollatzResearch.WordTrace tailWord_428833 prefixEnd_428833 195731066230778597880301 := by
  unfold tailWord_428833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15640824455418754690667153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10427216303612503127111435 15640824455418754690667153)
  ·
    refine ⟨11730618341564066018000365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15640824455418754690667153 11730618341564066018000365)
    ·
      refine ⟨4398981878086524756750137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11730618341564066018000365 4398981878086524756750137)
      ·
        refine ⟨3299236408564893567562603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4398981878086524756750137 3299236408564893567562603)
        ·
          refine ⟨4948854612847340351343905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299236408564893567562603 4948854612847340351343905)
          ·
            refine ⟨3711640959635505263507929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948854612847340351343905 3711640959635505263507929)
            ·
              refine ⟨2783730719726628947630947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711640959635505263507929 2783730719726628947630947)
              ·
                refine ⟨4175596079589943421446421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783730719726628947630947 4175596079589943421446421)
                ·
                  refine ⟨195731066230778597880301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4175596079589943421446421 195731066230778597880301)
                  ·
                    rfl

theorem cell20_428833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_428833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428833 prefixEnd_428833 := by exact prefixLift 428833
  have htrace : WordTrace (prefixWord ++ tailWord_428833) baseStart_428833 baseEnd_428833 := by
    simpa [prefixWord, tailWord_428833, baseEnd_428833] using wordTrace_append hprefix tailTrace_428833
  have hstable : (prefixWord ++ tailWord_428833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428833).length < 2 ^ (prefixWord ++ tailWord_428833).sum := by decide
  have hdescent : baseEnd_428833 < baseStart_428833 := by decide
  rcases family_descends (prefixWord ++ tailWord_428833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428870 : List Nat := [6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_428870 : Nat := 118140960795 + 428870 * 2 ^ 59
def prefixEnd_428870 : Nat := 4983230072969 + 3 ^ 40 * 428870 * 2
def baseEnd_428870 : Nat := 65249318012990304548939

theorem tailTrace_428870 : CollatzResearch.WordTrace tailWord_428870 prefixEnd_428870 65249318012990304548939 := by
  unfold tailWord_428870
  simp only [CollatzResearch.WordTrace]
  refine ⟨488817936133897187805127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10428115970856473339842709 488817936133897187805127)
  ·
    refine ⟨733226904200845781707691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488817936133897187805127 733226904200845781707691)
    ·
      refine ⟨1099840356301268672561537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733226904200845781707691 1099840356301268672561537)
      ·
        refine ⟨824880267225951504421153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099840356301268672561537 824880267225951504421153)
        ·
          refine ⟨618660200419463628315865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824880267225951504421153 618660200419463628315865)
          ·
            refine ⟨463995150314597721236899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618660200419463628315865 463995150314597721236899)
            ·
              refine ⟨695992725471896581855349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463995150314597721236899 695992725471896581855349)
              ·
                refine ⟨65249318012990304548939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 695992725471896581855349 65249318012990304548939)
                ·
                  rfl

theorem cell20_428870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_428870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428870 prefixEnd_428870 := by exact prefixLift 428870
  have htrace : WordTrace (prefixWord ++ tailWord_428870) baseStart_428870 baseEnd_428870 := by
    simpa [prefixWord, tailWord_428870, baseEnd_428870] using wordTrace_append hprefix tailTrace_428870
  have hstable : (prefixWord ++ tailWord_428870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428870).length < 2 ^ (prefixWord ++ tailWord_428870).sum := by decide
  have hdescent : baseEnd_428870 < baseStart_428870 := by decide
  rcases family_descends (prefixWord ++ tailWord_428870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428871 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_428871 : Nat := 118140960795 + 428871 * 2 ^ 59
def prefixEnd_428871 : Nat := 4983230072969 + 3 ^ 40 * 428871 * 2
def baseEnd_428871 : Nat := 195748410466219354613479

theorem tailTrace_428871 : CollatzResearch.WordTrace tailWord_428871 prefixEnd_428871 195748410466219354613479 := by
  unfold tailWord_428871
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642210429281087180550467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10428140286187391453700311 15642210429281087180550467)
  ·
    refine ⟨23463315643921630770825701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15642210429281087180550467 23463315643921630770825701)
    ·
      refine ⟨4399371683235305769529819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23463315643921630770825701 4399371683235305769529819)
      ·
        refine ⟨6599057524852958654294729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399371683235305769529819 6599057524852958654294729)
        ·
          refine ⟨4949293143639718990721047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599057524852958654294729 4949293143639718990721047)
          ·
            refine ⟨7423939715459578486081571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949293143639718990721047 7423939715459578486081571)
            ·
              refine ⟨11135909573189367729122357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423939715459578486081571 11135909573189367729122357)
              ·
                refine ⟨1043991522486503224605221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11135909573189367729122357 1043991522486503224605221)
                ·
                  refine ⟨195748410466219354613479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043991522486503224605221 195748410466219354613479)
                  ·
                    rfl

theorem cell20_428871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_428871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428871 prefixEnd_428871 := by exact prefixLift 428871
  have htrace : WordTrace (prefixWord ++ tailWord_428871) baseStart_428871 baseEnd_428871 := by
    simpa [prefixWord, tailWord_428871, baseEnd_428871] using wordTrace_append hprefix tailTrace_428871
  have hstable : (prefixWord ++ tailWord_428871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428871).length < 2 ^ (prefixWord ++ tailWord_428871).sum := by decide
  have hdescent : baseEnd_428871 < baseStart_428871 := by decide
  rcases family_descends (prefixWord ++ tailWord_428871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428895 : List Nat := [1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_428895 : Nat := 118140960795 + 428895 * 2 ^ 59
def prefixEnd_428895 : Nat := 4983230072969 + 3 ^ 40 * 428895 * 2
def baseEnd_428895 : Nat := 65253121573393979271127

theorem tailTrace_428895 : CollatzResearch.WordTrace tailWord_428895 prefixEnd_428895 65253121573393979271127 := by
  unfold tailWord_428895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15643085781194139279424139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10428723854129426186282759 15643085781194139279424139)
  ·
    refine ⟨23464628671791208919136209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15643085781194139279424139 23464628671791208919136209)
    ·
      refine ⟨17598471503843406689352157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23464628671791208919136209 17598471503843406689352157)
      ·
        refine ⟨6599426813941277508507059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17598471503843406689352157 6599426813941277508507059)
        ·
          refine ⟨9899140220911916262760589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599426813941277508507059 9899140220911916262760589)
          ·
            refine ⟨3712177582841968598535221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9899140220911916262760589 3712177582841968598535221)
            ·
              refine ⟨348016648391434556112677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3712177582841968598535221 348016648391434556112677)
              ·
                refine ⟨65253121573393979271127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348016648391434556112677 65253121573393979271127)
                ·
                  rfl

theorem cell20_428895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_428895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428895 prefixEnd_428895 := by exact prefixLift 428895
  have htrace : WordTrace (prefixWord ++ tailWord_428895) baseStart_428895 baseEnd_428895 := by
    simpa [prefixWord, tailWord_428895, baseEnd_428895] using wordTrace_append hprefix tailTrace_428895
  have hstable : (prefixWord ++ tailWord_428895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428895).length < 2 ^ (prefixWord ++ tailWord_428895).sum := by decide
  have hdescent : baseEnd_428895 < baseStart_428895 := by decide
  rcases family_descends (prefixWord ++ tailWord_428895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428909 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_428909 : Nat := 118140960795 + 428909 * 2 ^ 59
def prefixEnd_428909 : Nat := 4983230072969 + 3 ^ 40 * 428909 * 2
def baseEnd_428909 : Nat := 195765754701660111346657

theorem tailTrace_428909 : CollatzResearch.WordTrace tailWord_428909 prefixEnd_428909 195765754701660111346657 := by
  unfold tailWord_428909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15643596403143419670433781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10429064268762279780289187 15643596403143419670433781)
  ·
    refine ⟨1466587162794695594103167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15643596403143419670433781 1466587162794695594103167)
    ·
      refine ⟨2199880744192043391154751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466587162794695594103167 2199880744192043391154751)
      ·
        refine ⟨3299821116288065086732127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199880744192043391154751 3299821116288065086732127)
        ·
          refine ⟨4949731674432097630098191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299821116288065086732127 4949731674432097630098191)
          ·
            refine ⟨7424597511648146445147287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949731674432097630098191 7424597511648146445147287)
            ·
              refine ⟨11136896267472219667720931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7424597511648146445147287 11136896267472219667720931)
              ·
                refine ⟨16705344401208329501581397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11136896267472219667720931 16705344401208329501581397)
                ·
                  refine ⟨195765754701660111346657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16705344401208329501581397 195765754701660111346657)
                  ·
                    rfl

theorem cell20_428909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_428909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428909 prefixEnd_428909 := by exact prefixLift 428909
  have htrace : WordTrace (prefixWord ++ tailWord_428909) baseStart_428909 baseEnd_428909 := by
    simpa [prefixWord, tailWord_428909, baseEnd_428909] using wordTrace_append hprefix tailTrace_428909
  have hstable : (prefixWord ++ tailWord_428909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428909).length < 2 ^ (prefixWord ++ tailWord_428909).sum := by decide
  have hdescent : baseEnd_428909 < baseStart_428909 := by decide
  rcases family_descends (prefixWord ++ tailWord_428909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428936 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_428936 : Nat := 118140960795 + 428936 * 2 ^ 59
def prefixEnd_428936 : Nat := 4983230072969 + 3 ^ 40 * 428936 * 2
def baseEnd_428936 : Nat := 195778078237368017446547

theorem tailTrace_428936 : CollatzResearch.WordTrace tailWord_428936 prefixEnd_428936 195778078237368017446547 := by
  unfold tailWord_428936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7822290587022801640833331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10429720782697068854444441 7822290587022801640833331)
  ·
    refine ⟨11733435880534202461249997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7822290587022801640833331 11733435880534202461249997)
    ·
      refine ⟨4400038455200325922968749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11733435880534202461249997 4400038455200325922968749)
      ·
        refine ⟨1650014420700122221113281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4400038455200325922968749 1650014420700122221113281)
        ·
          refine ⟨1237510815525091665834961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1650014420700122221113281 1237510815525091665834961)
          ·
            refine ⟨928133111643818749376221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237510815525091665834961 928133111643818749376221)
            ·
              refine ⟨348049916866432031016083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928133111643818749376221 348049916866432031016083)
              ·
                refine ⟨522074875299648046524125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348049916866432031016083 522074875299648046524125)
                ·
                  refine ⟨195778078237368017446547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522074875299648046524125 195778078237368017446547)
                  ·
                    rfl

theorem cell20_428936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_428936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428936 prefixEnd_428936 := by exact prefixLift 428936
  have htrace : WordTrace (prefixWord ++ tailWord_428936) baseStart_428936 baseEnd_428936 := by
    simpa [prefixWord, tailWord_428936, baseEnd_428936] using wordTrace_append hprefix tailTrace_428936
  have hstable : (prefixWord ++ tailWord_428936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428936).length < 2 ^ (prefixWord ++ tailWord_428936).sum := by decide
  have hdescent : baseEnd_428936 < baseStart_428936 := by decide
  rcases family_descends (prefixWord ++ tailWord_428936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428940 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_428940 : Nat := 118140960795 + 428940 * 2 ^ 59
def prefixEnd_428940 : Nat := 4983230072969 + 3 ^ 40 * 428940 * 2
def baseEnd_428940 : Nat := 195779903946361781313197

theorem tailTrace_428940 : CollatzResearch.WordTrace tailWord_428940 prefixEnd_428940 195779903946361781313197 := by
  unfold tailWord_428940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7822363533015555982406137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10429818044020741309874849 7822363533015555982406137)
  ·
    refine ⟨5866772649761666986804603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7822363533015555982406137 5866772649761666986804603)
    ·
      refine ⟨8800158974642500480206905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5866772649761666986804603 8800158974642500480206905)
      ·
        refine ⟨6600119230981875360155179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8800158974642500480206905 6600119230981875360155179)
        ·
          refine ⟨9900178846472813040232769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600119230981875360155179 9900178846472813040232769)
          ·
            refine ⟨7425134134854609780174577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9900178846472813040232769 7425134134854609780174577)
            ·
              refine ⟨5568850601140957335130933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425134134854609780174577 5568850601140957335130933)
              ·
                refine ⟨522079743856964750168525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5568850601140957335130933 522079743856964750168525)
                ·
                  refine ⟨195779903946361781313197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522079743856964750168525 195779903946361781313197)
                  ·
                    rfl

theorem cell20_428940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_428940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428940 prefixEnd_428940 := by exact prefixLift 428940
  have htrace : WordTrace (prefixWord ++ tailWord_428940) baseStart_428940 baseEnd_428940 := by
    simpa [prefixWord, tailWord_428940, baseEnd_428940] using wordTrace_append hprefix tailTrace_428940
  have hstable : (prefixWord ++ tailWord_428940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428940).length < 2 ^ (prefixWord ++ tailWord_428940).sum := by decide
  have hdescent : baseEnd_428940 < baseStart_428940 := by decide
  rcases family_descends (prefixWord ++ tailWord_428940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428946 : List Nat := [3, 2, 3, 2, 3, 1, 2, 4]
def baseStart_428946 : Nat := 118140960795 + 428946 * 2 ^ 59
def prefixEnd_428946 : Nat := 4983230072969 + 3 ^ 40 * 428946 * 2
def baseEnd_428946 : Nat := 65260880836617475704391

theorem tailTrace_428946 : CollatzResearch.WordTrace tailWord_428946 prefixEnd_428946 65260880836617475704391 := by
  unfold tailWord_428946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911236476002343747382673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10429963936006249993020461 3911236476002343747382673)
  ·
    refine ⟨2933427357001757810537005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3911236476002343747382673 2933427357001757810537005)
    ·
      refine ⟨1100035258875659178951377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2933427357001757810537005 1100035258875659178951377)
      ·
        refine ⟨825026444156744384213533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100035258875659178951377 825026444156744384213533)
        ·
          refine ⟨309384916558779144080075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 825026444156744384213533 309384916558779144080075)
          ·
            refine ⟨464077374838168716120113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309384916558779144080075 464077374838168716120113)
            ·
              refine ⟨348058031128626537090085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464077374838168716120113 348058031128626537090085)
              ·
                refine ⟨65260880836617475704391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348058031128626537090085 65260880836617475704391)
                ·
                  rfl

theorem cell20_428946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_428946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428946 prefixEnd_428946 := by exact prefixLift 428946
  have htrace : WordTrace (prefixWord ++ tailWord_428946) baseStart_428946 baseEnd_428946 := by
    simpa [prefixWord, tailWord_428946, baseEnd_428946] using wordTrace_append hprefix tailTrace_428946
  have hstable : (prefixWord ++ tailWord_428946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428946).length < 2 ^ (prefixWord ++ tailWord_428946).sum := by decide
  have hdescent : baseEnd_428946 < baseStart_428946 := by decide
  rcases family_descends (prefixWord ++ tailWord_428946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428992 : List Nat := [2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_428992 : Nat := 118140960795 + 428992 * 2 ^ 59
def prefixEnd_428992 : Nat := 4983230072969 + 3 ^ 40 * 428992 * 2
def baseEnd_428992 : Nat := 65267879387760237193217

theorem tailTrace_428992 : CollatzResearch.WordTrace tailWord_428992 prefixEnd_428992 65267879387760237193217 := by
  unfold tailWord_428992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823311830921362422852615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10431082441228483230470153 7823311830921362422852615)
  ·
    refine ⟨11734967746382043634278923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7823311830921362422852615 11734967746382043634278923)
    ·
      refine ⟨17602451619573065451418385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11734967746382043634278923 17602451619573065451418385)
      ·
        refine ⟨13201838714679799088563789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17602451619573065451418385 13201838714679799088563789)
        ·
          refine ⟨4950689518004924658211421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13201838714679799088563789 4950689518004924658211421)
          ·
            refine ⟨1856508569251846746829283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4950689518004924658211421 1856508569251846746829283)
            ·
              refine ⟨2784762853877770120243925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856508569251846746829283 2784762853877770120243925)
              ·
                refine ⟨65267879387760237193217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2784762853877770120243925 65267879387760237193217)
                ·
                  rfl

theorem cell20_428992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_428992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_428992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_428992 prefixEnd_428992 := by exact prefixLift 428992
  have htrace : WordTrace (prefixWord ++ tailWord_428992) baseStart_428992 baseEnd_428992 := by
    simpa [prefixWord, tailWord_428992, baseEnd_428992] using wordTrace_append hprefix tailTrace_428992
  have hstable : (prefixWord ++ tailWord_428992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428992).length < 2 ^ (prefixWord ++ tailWord_428992).sum := by decide
  have hdescent : baseEnd_428992 < baseStart_428992 := by decide
  rcases family_descends (prefixWord ++ tailWord_428992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429061 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_429061 : Nat := 118140960795 + 429061 * 2 ^ 59
def prefixEnd_429061 : Nat := 4983230072969 + 3 ^ 40 * 429061 * 2
def baseEnd_429061 : Nat := 195835131643423138279369

theorem tailTrace_429061 : CollatzResearch.WordTrace tailWord_429061 prefixEnd_429061 195835131643423138279369 := by
  unfold tailWord_429061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649140298592749629967037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10432760199061833086644691 15649140298592749629967037)
  ·
    refine ⟨5868427611972281111237639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15649140298592749629967037 5868427611972281111237639)
    ·
      refine ⟨8802641417958421666856459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5868427611972281111237639 8802641417958421666856459)
      ·
        refine ⟨13203962126937632500284689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8802641417958421666856459 13203962126937632500284689)
        ·
          refine ⟨9902971595203224375213517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13203962126937632500284689 9902971595203224375213517)
          ·
            refine ⟨3713614348201209140705069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9902971595203224375213517 3713614348201209140705069)
            ·
              refine ⟨1392605380575453427764401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3713614348201209140705069 1392605380575453427764401)
              ·
                refine ⟨1044454035431590070823301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392605380575453427764401 1044454035431590070823301)
                ·
                  refine ⟨195835131643423138279369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044454035431590070823301 195835131643423138279369)
                  ·
                    rfl

theorem cell20_429061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_429061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429061 prefixEnd_429061 := by exact prefixLift 429061
  have htrace : WordTrace (prefixWord ++ tailWord_429061) baseStart_429061 baseEnd_429061 := by
    simpa [prefixWord, tailWord_429061, baseEnd_429061] using wordTrace_append hprefix tailTrace_429061
  have hstable : (prefixWord ++ tailWord_429061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429061).length < 2 ^ (prefixWord ++ tailWord_429061).sum := by decide
  have hdescent : baseEnd_429061 < baseStart_429061 := by decide
  rcases family_descends (prefixWord ++ tailWord_429061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429075 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_429075 : Nat := 118140960795 + 429075 * 2 ^ 59
def prefixEnd_429075 : Nat := 4983230072969 + 3 ^ 40 * 429075 * 2
def baseEnd_429075 : Nat := 195841521624901311812645

theorem tailTrace_429075 : CollatzResearch.WordTrace tailWord_429075 prefixEnd_429075 195841521624901311812645 := by
  unfold tailWord_429075
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649650920542030020976679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433100613694686680651119 15649650920542030020976679)
  ·
    refine ⟨23474476380813045031465019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15649650920542030020976679 23474476380813045031465019)
    ·
      refine ⟨35211714571219567547197529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23474476380813045031465019 35211714571219567547197529)
      ·
        refine ⟨26408785928414675660398147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35211714571219567547197529 26408785928414675660398147)
        ·
          refine ⟨39613178892622013490597221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26408785928414675660398147 39613178892622013490597221)
          ·
            refine ⟨7427471042366627529486979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39613178892622013490597221 7427471042366627529486979)
            ·
              refine ⟨11141206563549941294230469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427471042366627529486979 11141206563549941294230469)
              ·
                refine ⟨2088976230665613992668213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11141206563549941294230469 2088976230665613992668213)
                ·
                  refine ⟨195841521624901311812645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088976230665613992668213 195841521624901311812645)
                  ·
                    rfl

theorem cell20_429075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_429075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429075 prefixEnd_429075 := by exact prefixLift 429075
  have htrace : WordTrace (prefixWord ++ tailWord_429075) baseStart_429075 baseEnd_429075 := by
    simpa [prefixWord, tailWord_429075, baseEnd_429075] using wordTrace_append hprefix tailTrace_429075
  have hstable : (prefixWord ++ tailWord_429075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429075).length < 2 ^ (prefixWord ++ tailWord_429075).sum := by decide
  have hdescent : baseEnd_429075 < baseStart_429075 := by decide
  rcases family_descends (prefixWord ++ tailWord_429075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429085 : List Nat := [1, 4, 2, 2, 3, 1, 7]
def baseStart_429085 : Nat := 118140960795 + 429085 * 2 ^ 59
def prefixEnd_429085 : Nat := 4983230072969 + 3 ^ 40 * 429085 * 2
def baseEnd_429085 : Nat := 21760676210820635719919

theorem tailTrace_429085 : CollatzResearch.WordTrace tailWord_429085 prefixEnd_429085 21760676210820635719919 := by
  unfold tailWord_429085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650015650505801728840709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433343767003867819227139 15650015650505801728840709)
  ·
    refine ⟨2934377934469837824157633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15650015650505801728840709 2934377934469837824157633)
    ·
      refine ⟨2200783450852378368118225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2934377934469837824157633 2200783450852378368118225)
      ·
        refine ⟨1650587588139283776088669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2200783450852378368118225 1650587588139283776088669)
        ·
          refine ⟨618970345552231416033251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1650587588139283776088669 618970345552231416033251)
          ·
            refine ⟨928455518328347124049877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618970345552231416033251 928455518328347124049877)
            ·
              refine ⟨21760676210820635719919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 928455518328347124049877 21760676210820635719919)
              ·
                rfl

theorem cell20_429085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_429085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429085 prefixEnd_429085 := by exact prefixLift 429085
  have htrace : WordTrace (prefixWord ++ tailWord_429085) baseStart_429085 baseEnd_429085 := by
    simpa [prefixWord, tailWord_429085, baseEnd_429085] using wordTrace_append hprefix tailTrace_429085
  have hstable : (prefixWord ++ tailWord_429085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429085).length < 2 ^ (prefixWord ++ tailWord_429085).sum := by decide
  have hdescent : baseEnd_429085 < baseStart_429085 := by decide
  rcases family_descends (prefixWord ++ tailWord_429085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429095 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_429095 : Nat := 118140960795 + 429095 * 2 ^ 59
def prefixEnd_429095 : Nat := 4983230072969 + 3 ^ 40 * 429095 * 2
def baseEnd_429095 : Nat := 195850650169870131145897

theorem tailTrace_429095 : CollatzResearch.WordTrace tailWord_429095 prefixEnd_429095 195850650169870131145897 := by
  unfold tailWord_429095
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650380380469573436704739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433586920313048957803159 15650380380469573436704739)
  ·
    refine ⟨23475570570704360155057109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650380380469573436704739 23475570570704360155057109)
    ·
      refine ⟨550208685250883441134151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23475570570704360155057109 550208685250883441134151)
      ·
        refine ⟨825313027876325161701227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550208685250883441134151 825313027876325161701227)
        ·
          refine ⟨1237969541814487742551841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825313027876325161701227 1237969541814487742551841)
          ·
            refine ⟨928477156360865806913881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237969541814487742551841 928477156360865806913881)
            ·
              refine ⟨696357867270649355185411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928477156360865806913881 696357867270649355185411)
              ·
                refine ⟨1044536800905974032778117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696357867270649355185411 1044536800905974032778117)
                ·
                  refine ⟨195850650169870131145897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044536800905974032778117 195850650169870131145897)
                  ·
                    rfl

theorem cell20_429095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_429095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429095 prefixEnd_429095 := by exact prefixLift 429095
  have htrace : WordTrace (prefixWord ++ tailWord_429095) baseStart_429095 baseEnd_429095 := by
    simpa [prefixWord, tailWord_429095, baseEnd_429095] using wordTrace_append hprefix tailTrace_429095
  have hstable : (prefixWord ++ tailWord_429095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429095).length < 2 ^ (prefixWord ++ tailWord_429095).sum := by decide
  have hdescent : baseEnd_429095 < baseStart_429095 := by decide
  rcases family_descends (prefixWord ++ tailWord_429095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429099 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_429099 : Nat := 118140960795 + 429099 * 2 ^ 59
def prefixEnd_429099 : Nat := 4983230072969 + 3 ^ 40 * 429099 * 2
def baseEnd_429099 : Nat := 195852475878863895012547

theorem tailTrace_429099 : CollatzResearch.WordTrace tailWord_429099 prefixEnd_429099 195852475878863895012547 := by
  unfold tailWord_429099
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650526272455082119850351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433684181636721413233567 15650526272455082119850351)
  ·
    refine ⟨23475789408682623179775527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650526272455082119850351 23475789408682623179775527)
    ·
      refine ⟨35213684113023934769663291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23475789408682623179775527 35213684113023934769663291)
      ·
        refine ⟨52820526169535902154494937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35213684113023934769663291 52820526169535902154494937)
        ·
          refine ⟨39615394627151926615871203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52820526169535902154494937 39615394627151926615871203)
          ·
            refine ⟨59423091940727889923806805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39615394627151926615871203 59423091940727889923806805)
            ·
              refine ⟨696364358680404960044611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 59423091940727889923806805 696364358680404960044611)
              ·
                refine ⟨1044546538020607440066917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696364358680404960044611 1044546538020607440066917)
                ·
                  refine ⟨195852475878863895012547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044546538020607440066917 195852475878863895012547)
                  ·
                    rfl

theorem cell20_429099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_429099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429099 prefixEnd_429099 := by exact prefixLift 429099
  have htrace : WordTrace (prefixWord ++ tailWord_429099) baseStart_429099 baseEnd_429099 := by
    simpa [prefixWord, tailWord_429099, baseEnd_429099] using wordTrace_append hprefix tailTrace_429099
  have hstable : (prefixWord ++ tailWord_429099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429099).length < 2 ^ (prefixWord ++ tailWord_429099).sum := by decide
  have hdescent : baseEnd_429099 < baseStart_429099 := by decide
  rcases family_descends (prefixWord ++ tailWord_429099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429106 : List Nat := [3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_429106 : Nat := 118140960795 + 429106 * 2 ^ 59
def prefixEnd_429106 : Nat := 4983230072969 + 3 ^ 40 * 429106 * 2
def baseEnd_429106 : Nat := 65285223623200993926395

theorem tailTrace_429106 : CollatzResearch.WordTrace tailWord_429106 prefixEnd_429106 65285223623200993926395 := by
  unfold tailWord_429106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912695395857430578838793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10433854388953148210236781 3912695395857430578838793)
  ·
    refine ⟨2934521546893072934129095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3912695395857430578838793 2934521546893072934129095)
    ·
      refine ⟨4401782320339609401193643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934521546893072934129095 4401782320339609401193643)
      ·
        refine ⟨6602673480509414101790465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401782320339609401193643 6602673480509414101790465)
        ·
          refine ⟨4952005110382060576342849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6602673480509414101790465 4952005110382060576342849)
          ·
            refine ⟨3714003832786545432257137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4952005110382060576342849 3714003832786545432257137)
            ·
              refine ⟨2785502874589909074192853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714003832786545432257137 2785502874589909074192853)
              ·
                refine ⟨65285223623200993926395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2785502874589909074192853 65285223623200993926395)
                ·
                  rfl

theorem cell20_429106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_429106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429106 prefixEnd_429106 := by exact prefixLift 429106
  have htrace : WordTrace (prefixWord ++ tailWord_429106) baseStart_429106 baseEnd_429106 := by
    simpa [prefixWord, tailWord_429106, baseEnd_429106] using wordTrace_append hprefix tailTrace_429106
  have hstable : (prefixWord ++ tailWord_429106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429106).length < 2 ^ (prefixWord ++ tailWord_429106).sum := by decide
  have hdescent : baseEnd_429106 < baseStart_429106 := by decide
  rcases family_descends (prefixWord ++ tailWord_429106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429150 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_429150 : Nat := 118140960795 + 429150 * 2 ^ 59
def prefixEnd_429150 : Nat := 4983230072969 + 3 ^ 40 * 429150 * 2
def baseEnd_429150 : Nat := 195875753668534384312339

theorem tailTrace_429150 : CollatzResearch.WordTrace tailWord_429150 prefixEnd_429150 195875753668534384312339 := by
  unfold tailWord_429150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956548299408789728744613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10434924263513545219971269 1956548299408789728744613)
  ·
    refine ⟨366852806139148074139615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1956548299408789728744613 366852806139148074139615)
    ·
      refine ⟨550279209208722111209423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366852806139148074139615 550279209208722111209423)
      ·
        refine ⟨825418813813083166814135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550279209208722111209423 825418813813083166814135)
        ·
          refine ⟨1238128220719624750221203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825418813813083166814135 1238128220719624750221203)
          ·
            refine ⟨1857192331079437125331805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238128220719624750221203 1857192331079437125331805)
            ·
              refine ⟨696447124154788921999427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1857192331079437125331805 696447124154788921999427)
              ·
                refine ⟨1044670686232183382999141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696447124154788921999427 1044670686232183382999141)
                ·
                  refine ⟨195875753668534384312339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044670686232183382999141 195875753668534384312339)
                  ·
                    rfl

theorem cell20_429150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_429150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429150 prefixEnd_429150 := by exact prefixLift 429150
  have htrace : WordTrace (prefixWord ++ tailWord_429150) baseStart_429150 baseEnd_429150 := by
    simpa [prefixWord, tailWord_429150, baseEnd_429150] using wordTrace_append hprefix tailTrace_429150
  have hstable : (prefixWord ++ tailWord_429150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429150).length < 2 ^ (prefixWord ++ tailWord_429150).sum := by decide
  have hdescent : baseEnd_429150 < baseStart_429150 := by decide
  rcases family_descends (prefixWord ++ tailWord_429150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429151 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_429151 : Nat := 118140960795 + 429151 * 2 ^ 59
def prefixEnd_429151 : Nat := 4983230072969 + 3 ^ 40 * 429151 * 2
def baseEnd_429151 : Nat := 195876210095782825279001

theorem tailTrace_429151 : CollatzResearch.WordTrace tailWord_429151 prefixEnd_429151 195876210095782825279001 := by
  unfold tailWord_429151
  simp only [CollatzResearch.WordTrace]
  refine ⟨15652422868266695000743307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10434948578844463333828871 15652422868266695000743307)
  ·
    refine ⟨23478634302400042501114961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15652422868266695000743307 23478634302400042501114961)
    ·
      refine ⟨17608975726800031875836221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23478634302400042501114961 17608975726800031875836221)
      ·
        refine ⟨6603365897550011953438583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17608975726800031875836221 6603365897550011953438583)
        ·
          refine ⟨9905048846325017930157875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603365897550011953438583 9905048846325017930157875)
          ·
            refine ⟨14857573269487526895236813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905048846325017930157875 14857573269487526895236813)
            ·
              refine ⟨5571589976057822585713805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14857573269487526895236813 5571589976057822585713805)
              ·
                refine ⟨2089346241021683469642677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571589976057822585713805 2089346241021683469642677)
                ·
                  refine ⟨195876210095782825279001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2089346241021683469642677 195876210095782825279001)
                  ·
                    rfl

theorem cell20_429151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_429151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429151 prefixEnd_429151 := by exact prefixLift 429151
  have htrace : WordTrace (prefixWord ++ tailWord_429151) baseStart_429151 baseEnd_429151 := by
    simpa [prefixWord, tailWord_429151, baseEnd_429151] using wordTrace_append hprefix tailTrace_429151
  have hstable : (prefixWord ++ tailWord_429151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429151).length < 2 ^ (prefixWord ++ tailWord_429151).sum := by decide
  have hdescent : baseEnd_429151 < baseStart_429151 := by decide
  rcases family_descends (prefixWord ++ tailWord_429151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429160 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_429160 : Nat := 118140960795 + 429160 * 2 ^ 59
def prefixEnd_429160 : Nat := 4983230072969 + 3 ^ 40 * 429160 * 2
def baseEnd_429160 : Nat := 195880317941018793978965

theorem tailTrace_429160 : CollatzResearch.WordTrace tailWord_429160 prefixEnd_429160 195880317941018793978965 := by
  unfold tailWord_429160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7826375562617044768910467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10435167416822726358547289 7826375562617044768910467)
  ·
    refine ⟨11739563343925567153365701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7826375562617044768910467 11739563343925567153365701)
    ·
      refine ⟨2201168126986043841256069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11739563343925567153365701 2201168126986043841256069)
      ·
        refine ⟨412719023809883220235513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2201168126986043841256069 412719023809883220235513)
        ·
          refine ⟨309539267857412415176635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412719023809883220235513 309539267857412415176635)
          ·
            refine ⟨464308901786118622764953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309539267857412415176635 464308901786118622764953)
            ·
              refine ⟨348231676339588967073715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464308901786118622764953 348231676339588967073715)
              ·
                refine ⟨522347514509383450610573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348231676339588967073715 522347514509383450610573)
                ·
                  refine ⟨195880317941018793978965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522347514509383450610573 195880317941018793978965)
                  ·
                    rfl

theorem cell20_429160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_429160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429160 prefixEnd_429160 := by exact prefixLift 429160
  have htrace : WordTrace (prefixWord ++ tailWord_429160) baseStart_429160 baseEnd_429160 := by
    simpa [prefixWord, tailWord_429160, baseEnd_429160] using wordTrace_append hprefix tailTrace_429160
  have hstable : (prefixWord ++ tailWord_429160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429160).length < 2 ^ (prefixWord ++ tailWord_429160).sum := by decide
  have hdescent : baseEnd_429160 < baseStart_429160 := by decide
  rcases family_descends (prefixWord ++ tailWord_429160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429168 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_429168 : Nat := 118140960795 + 429168 * 2 ^ 59
def prefixEnd_429168 : Nat := 4983230072969 + 3 ^ 40 * 429168 * 2
def baseEnd_429168 : Nat := 195883969359006321712265

theorem tailTrace_429168 : CollatzResearch.WordTrace tailWord_429168 prefixEnd_429168 195883969359006321712265 := by
  unfold tailWord_429168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7826521454602553452056079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10435361939470071269408105 7826521454602553452056079)
  ·
    refine ⟨11739782181903830178084119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7826521454602553452056079 11739782181903830178084119)
    ·
      refine ⟨17609673272855745267126179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11739782181903830178084119 17609673272855745267126179)
      ·
        refine ⟨26414509909283617900689269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17609673272855745267126179 26414509909283617900689269)
        ·
          refine ⟨2476360303995339178189619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26414509909283617900689269 2476360303995339178189619)
          ·
            refine ⟨3714540455993008767284429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476360303995339178189619 3714540455993008767284429)
            ·
              refine ⟨1392952670997378287731661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3714540455993008767284429 1392952670997378287731661)
              ·
                refine ⟨522357251624016857899373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1392952670997378287731661 522357251624016857899373)
                ·
                  refine ⟨195883969359006321712265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522357251624016857899373 195883969359006321712265)
                  ·
                    rfl

theorem cell20_429168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_429168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429168 prefixEnd_429168 := by exact prefixLift 429168
  have htrace : WordTrace (prefixWord ++ tailWord_429168) baseStart_429168 baseEnd_429168 := by
    simpa [prefixWord, tailWord_429168, baseEnd_429168] using wordTrace_append hprefix tailTrace_429168
  have hstable : (prefixWord ++ tailWord_429168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429168).length < 2 ^ (prefixWord ++ tailWord_429168).sum := by decide
  have hdescent : baseEnd_429168 < baseStart_429168 := by decide
  rcases family_descends (prefixWord ++ tailWord_429168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429213 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_429213 : Nat := 118140960795 + 429213 * 2 ^ 59
def prefixEnd_429213 : Nat := 4983230072969 + 3 ^ 40 * 429213 * 2
def baseEnd_429213 : Nat := 195904508585186165212081

theorem tailTrace_429213 : CollatzResearch.WordTrace tailWord_429213 prefixEnd_429213 195904508585186165212081 := by
  unfold tailWord_429213
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654684194042079589500293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10436456129361386393000195 15654684194042079589500293)
  ·
    refine ⟨2935253286382889923031305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15654684194042079589500293 2935253286382889923031305)
    ·
      refine ⟨2201439964787167442273479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2935253286382889923031305 2201439964787167442273479)
      ·
        refine ⟨3302159947180751163410219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201439964787167442273479 3302159947180751163410219)
        ·
          refine ⟨4953239920771126745115329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302159947180751163410219 4953239920771126745115329)
          ·
            refine ⟨3714929940578345058836497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4953239920771126745115329 3714929940578345058836497)
            ·
              refine ⟨2786197455433758794127373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714929940578345058836497 2786197455433758794127373)
              ·
                refine ⟨1044824045787659547797765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2786197455433758794127373 1044824045787659547797765)
                ·
                  refine ⟨195904508585186165212081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044824045787659547797765 195904508585186165212081)
                  ·
                    rfl

theorem cell20_429213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_429213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429213 prefixEnd_429213 := by exact prefixLift 429213
  have htrace : WordTrace (prefixWord ++ tailWord_429213) baseStart_429213 baseEnd_429213 := by
    simpa [prefixWord, tailWord_429213, baseEnd_429213] using wordTrace_append hprefix tailTrace_429213
  have hstable : (prefixWord ++ tailWord_429213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429213).length < 2 ^ (prefixWord ++ tailWord_429213).sum := by decide
  have hdescent : baseEnd_429213 < baseStart_429213 := by decide
  rcases family_descends (prefixWord ++ tailWord_429213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429223 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_429223 : Nat := 118140960795 + 429223 * 2 ^ 59
def prefixEnd_429223 : Nat := 4983230072969 + 3 ^ 40 * 429223 * 2
def baseEnd_429223 : Nat := 195909072857670574878707

theorem tailTrace_429223 : CollatzResearch.WordTrace tailWord_429223 prefixEnd_429223 195909072857670574878707 := by
  unfold tailWord_429223
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655048924005851297364323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10436699282670567531576215 15655048924005851297364323)
  ·
    refine ⟨23482573386008776946046485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15655048924005851297364323 23482573386008776946046485)
    ·
      refine ⟨1100745627469161419345929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23482573386008776946046485 1100745627469161419345929)
      ·
        refine ⟨825559220601871064509447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100745627469161419345929 825559220601871064509447)
        ·
          refine ⟨1238338830902806596764171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825559220601871064509447 1238338830902806596764171)
          ·
            refine ⟨1857508246354209895146257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238338830902806596764171 1857508246354209895146257)
            ·
              refine ⟨1393131184765657421359693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857508246354209895146257 1393131184765657421359693)
              ·
                refine ⟨522424194287121533009885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393131184765657421359693 522424194287121533009885)
                ·
                  refine ⟨195909072857670574878707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522424194287121533009885 195909072857670574878707)
                  ·
                    rfl

theorem cell20_429223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_429223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429223 prefixEnd_429223 := by exact prefixLift 429223
  have htrace : WordTrace (prefixWord ++ tailWord_429223) baseStart_429223 baseEnd_429223 := by
    simpa [prefixWord, tailWord_429223, baseEnd_429223] using wordTrace_append hprefix tailTrace_429223
  have hstable : (prefixWord ++ tailWord_429223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429223).length < 2 ^ (prefixWord ++ tailWord_429223).sum := by decide
  have hdescent : baseEnd_429223 < baseStart_429223 := by decide
  rcases family_descends (prefixWord ++ tailWord_429223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429258 : List Nat := [3, 1, 2, 1, 3, 3, 7]
def baseStart_429258 : Nat := 118140960795 + 429258 * 2 ^ 59
def prefixEnd_429258 : Nat := 4983230072969 + 3 ^ 40 * 429258 * 2
def baseEnd_429258 : Nat := 21769449756818445412433

theorem tailTrace_429258 : CollatzResearch.WordTrace tailWord_429258 prefixEnd_429258 21769449756818445412433 := by
  unfold tailWord_429258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914081369719763068722107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10437550319252701516592285 3914081369719763068722107)
  ·
    refine ⟨5871122054579644603083161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914081369719763068722107 5871122054579644603083161)
    ·
      refine ⟨4403341540934733452312371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5871122054579644603083161 4403341540934733452312371)
      ·
        refine ⟨6605012311402100178468557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403341540934733452312371 6605012311402100178468557)
        ·
          refine ⟨2476879616775787566925709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6605012311402100178468557 2476879616775787566925709)
          ·
            refine ⟨928829856290920337597141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2476879616775787566925709 928829856290920337597141)
            ·
              refine ⟨21769449756818445412433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 928829856290920337597141 21769449756818445412433)
              ·
                rfl

theorem cell20_429258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_429258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429258 prefixEnd_429258 := by exact prefixLift 429258
  have htrace : WordTrace (prefixWord ++ tailWord_429258) baseStart_429258 baseEnd_429258 := by
    simpa [prefixWord, tailWord_429258, baseEnd_429258] using wordTrace_append hprefix tailTrace_429258
  have hstable : (prefixWord ++ tailWord_429258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429258).length < 2 ^ (prefixWord ++ tailWord_429258).sum := by decide
  have hdescent : baseEnd_429258 < baseStart_429258 := by decide
  rcases family_descends (prefixWord ++ tailWord_429258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429323 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 2]
def baseStart_429323 : Nat := 118140960795 + 429323 * 2 ^ 59
def prefixEnd_429323 : Nat := 4983230072969 + 3 ^ 40 * 429323 * 2
def baseEnd_429323 : Nat := 195954715582514671544965

theorem tailTrace_429323 : CollatzResearch.WordTrace tailWord_429323 prefixEnd_429323 195954715582514671544965 := by
  unfold tailWord_429323
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658696223643568376004623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10439130815762378917336415 15658696223643568376004623)
  ·
    refine ⟨23488044335465352564006935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15658696223643568376004623 23488044335465352564006935)
    ·
      refine ⟨35232066503198028846010403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23488044335465352564006935 35232066503198028846010403)
      ·
        refine ⟨52848099754797043269015605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35232066503198028846010403 52848099754797043269015605)
        ·
          refine ⟨4954509352012222806470213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52848099754797043269015605 4954509352012222806470213)
          ·
            refine ⟨928970503502291776213165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4954509352012222806470213 928970503502291776213165)
            ·
              refine ⟨348363938813359416079937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928970503502291776213165 348363938813359416079937)
              ·
                refine ⟨261272954110019562059953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348363938813359416079937 261272954110019562059953)
                ·
                  refine ⟨195954715582514671544965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261272954110019562059953 195954715582514671544965)
                  ·
                    rfl

theorem cell20_429323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2].length) (baseStart_429323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429323 prefixEnd_429323 := by exact prefixLift 429323
  have htrace : WordTrace (prefixWord ++ tailWord_429323) baseStart_429323 baseEnd_429323 := by
    simpa [prefixWord, tailWord_429323, baseEnd_429323] using wordTrace_append hprefix tailTrace_429323
  have hstable : (prefixWord ++ tailWord_429323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429323).length < 2 ^ (prefixWord ++ tailWord_429323).sum := by decide
  have hdescent : baseEnd_429323 < baseStart_429323 := by decide
  rcases family_descends (prefixWord ++ tailWord_429323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429386 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_429386 : Nat := 118140960795 + 429386 * 2 ^ 59
def prefixEnd_429386 : Nat := 4983230072969 + 3 ^ 40 * 429386 * 2
def baseEnd_429386 : Nat := 195983470499166452444707

theorem tailTrace_429386 : CollatzResearch.WordTrace tailWord_429386 prefixEnd_429386 195983470499166452444707 := by
  unfold tailWord_429386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915248505603832533887003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10440662681610220090365341 3915248505603832533887003)
  ·
    refine ⟨5872872758405748800830505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915248505603832533887003 5872872758405748800830505)
    ·
      refine ⟨4404654568804311600622879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5872872758405748800830505 4404654568804311600622879)
      ·
        refine ⟨6606981853206467400934319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404654568804311600622879 6606981853206467400934319)
        ·
          refine ⟨9910472779809701101401479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606981853206467400934319 9910472779809701101401479)
          ·
            refine ⟨14865709169714551652102219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9910472779809701101401479 14865709169714551652102219)
            ·
              refine ⟨22298563754571827478153329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14865709169714551652102219 22298563754571827478153329)
              ·
                refine ⟨16723922815928870608614997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22298563754571827478153329 16723922815928870608614997)
                ·
                  refine ⟨195983470499166452444707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16723922815928870608614997 195983470499166452444707)
                  ·
                    rfl

theorem cell20_429386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_429386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429386 prefixEnd_429386 := by exact prefixLift 429386
  have htrace : WordTrace (prefixWord ++ tailWord_429386) baseStart_429386 baseEnd_429386 := by
    simpa [prefixWord, tailWord_429386, baseEnd_429386] using wordTrace_append hprefix tailTrace_429386
  have hstable : (prefixWord ++ tailWord_429386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429386).length < 2 ^ (prefixWord ++ tailWord_429386).sum := by decide
  have hdescent : baseEnd_429386 < baseStart_429386 := by decide
  rcases family_descends (prefixWord ++ tailWord_429386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429396 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_429396 : Nat := 118140960795 + 429396 * 2 ^ 59
def prefixEnd_429396 : Nat := 4983230072969 + 3 ^ 40 * 429396 * 2
def baseEnd_429396 : Nat := 195988034771650862111333

theorem tailTrace_429396 : CollatzResearch.WordTrace tailWord_429396 prefixEnd_429396 195988034771650862111333 := by
  unfold tailWord_429396
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830679376189550921706021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10440905834919401228941361 7830679376189550921706021)
  ·
    refine ⟨1468252383035540797819879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7830679376189550921706021 1468252383035540797819879)
    ·
      refine ⟨2202378574553311196729819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468252383035540797819879 2202378574553311196729819)
      ·
        refine ⟨3303567861829966795094729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2202378574553311196729819 3303567861829966795094729)
        ·
          refine ⟨2477675896372475096321047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3303567861829966795094729 2477675896372475096321047)
          ·
            refine ⟨3716513844558712644481571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477675896372475096321047 3716513844558712644481571)
            ·
              refine ⟨5574770766838068966722357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716513844558712644481571 5574770766838068966722357)
              ·
                refine ⟨522634759391068965630221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5574770766838068966722357 522634759391068965630221)
                ·
                  refine ⟨195988034771650862111333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522634759391068965630221 195988034771650862111333)
                  ·
                    rfl

theorem cell20_429396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_429396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429396 prefixEnd_429396 := by exact prefixLift 429396
  have htrace : WordTrace (prefixWord ++ tailWord_429396) baseStart_429396 baseEnd_429396 := by
    simpa [prefixWord, tailWord_429396, baseEnd_429396] using wordTrace_append hprefix tailTrace_429396
  have hstable : (prefixWord ++ tailWord_429396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429396).length < 2 ^ (prefixWord ++ tailWord_429396).sum := by decide
  have hdescent : baseEnd_429396 < baseStart_429396 := by decide
  rcases family_descends (prefixWord ++ tailWord_429396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429420 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_429420 : Nat := 118140960795 + 429420 * 2 ^ 59
def prefixEnd_429420 : Nat := 4983230072969 + 3 ^ 40 * 429420 * 2
def baseEnd_429420 : Nat := 195998989025613445311235

theorem tailTrace_429420 : CollatzResearch.WordTrace tailWord_429420 prefixEnd_429420 195998989025613445311235 := by
  unfold tailWord_429420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831117052146076971142857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10441489402861435961523809 7831117052146076971142857)
  ·
    refine ⟨5873337789109557728357143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7831117052146076971142857 5873337789109557728357143)
    ·
      refine ⟨8810006683664336592535715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873337789109557728357143 8810006683664336592535715)
      ·
        refine ⟨13215010025496504888803573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810006683664336592535715 13215010025496504888803573)
        ·
          refine ⟨1238907189890297333325335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13215010025496504888803573 1238907189890297333325335)
          ·
            refine ⟨1858360784835445999988003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238907189890297333325335 1858360784835445999988003)
            ·
              refine ⟨2787541177253168999982005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858360784835445999988003 2787541177253168999982005)
              ·
                refine ⟨261331985367484593748313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2787541177253168999982005 261331985367484593748313)
                ·
                  refine ⟨195998989025613445311235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261331985367484593748313 195998989025613445311235)
                  ·
                    rfl

theorem cell20_429420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_429420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429420 prefixEnd_429420 := by exact prefixLift 429420
  have htrace : WordTrace (prefixWord ++ tailWord_429420) baseStart_429420 baseEnd_429420 := by
    simpa [prefixWord, tailWord_429420, baseEnd_429420] using wordTrace_append hprefix tailTrace_429420
  have hstable : (prefixWord ++ tailWord_429420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429420).length < 2 ^ (prefixWord ++ tailWord_429420).sum := by decide
  have hdescent : baseEnd_429420 < baseStart_429420 := by decide
  rcases family_descends (prefixWord ++ tailWord_429420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429424 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_429424 : Nat := 118140960795 + 429424 * 2 ^ 59
def prefixEnd_429424 : Nat := 4983230072969 + 3 ^ 40 * 429424 * 2
def baseEnd_429424 : Nat := 196000814734607209177885

theorem tailTrace_429424 : CollatzResearch.WordTrace tailWord_429424 prefixEnd_429424 196000814734607209177885 := by
  unfold tailWord_429424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831189998138831312715663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10441586664185108416954217 7831189998138831312715663)
  ·
    refine ⟨11746784997208246969073495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7831189998138831312715663 11746784997208246969073495)
    ·
      refine ⟨17620177495812370453610243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11746784997208246969073495 17620177495812370453610243)
      ·
        refine ⟨26430266243718555680415365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17620177495812370453610243 26430266243718555680415365)
        ·
          refine ⟨4955674920697229190077881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26430266243718555680415365 4955674920697229190077881)
          ·
            refine ⟨3716756190522921892558411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955674920697229190077881 3716756190522921892558411)
            ·
              refine ⟨5575134285784382838837617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716756190522921892558411 5575134285784382838837617)
              ·
                refine ⟨4181350714338287129128213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575134285784382838837617 4181350714338287129128213)
                ·
                  refine ⟨196000814734607209177885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4181350714338287129128213 196000814734607209177885)
                  ·
                    rfl

theorem cell20_429424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_429424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429424 prefixEnd_429424 := by exact prefixLift 429424
  have htrace : WordTrace (prefixWord ++ tailWord_429424) baseStart_429424 baseEnd_429424 := by
    simpa [prefixWord, tailWord_429424, baseEnd_429424] using wordTrace_append hprefix tailTrace_429424
  have hstable : (prefixWord ++ tailWord_429424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429424).length < 2 ^ (prefixWord ++ tailWord_429424).sum := by decide
  have hdescent : baseEnd_429424 < baseStart_429424 := by decide
  rcases family_descends (prefixWord ++ tailWord_429424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429431 : List Nat := [1, 1, 3, 1, 1, 2, 11]
def baseStart_429431 : Nat := 118140960795 + 429431 * 2 ^ 59
def prefixEnd_429431 : Nat := 4983230072969 + 3 ^ 40 * 429431 * 2
def baseEnd_429431 : Nat := 21778223302816255104947

theorem tailTrace_429431 : CollatzResearch.WordTrace tailWord_429431 prefixEnd_429431 21778223302816255104947 := by
  unfold tailWord_429431
  simp only [CollatzResearch.WordTrace]
  refine ⟨15662635307252302820936147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10441756871501535213957431 15662635307252302820936147)
  ·
    refine ⟨23493952960878454231404221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15662635307252302820936147 23493952960878454231404221)
    ·
      refine ⟨8810232360329420336776583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23493952960878454231404221 8810232360329420336776583)
      ·
        refine ⟨13215348540494130505164875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810232360329420336776583 13215348540494130505164875)
        ·
          refine ⟨19823022810741195757747313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13215348540494130505164875 19823022810741195757747313)
          ·
            refine ⟨14867267108055896818310485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19823022810741195757747313 14867267108055896818310485)
            ·
              refine ⟨21778223302816255104947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14867267108055896818310485 21778223302816255104947)
              ·
                rfl

theorem cell20_429431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_429431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429431 prefixEnd_429431 := by exact prefixLift 429431
  have htrace : WordTrace (prefixWord ++ tailWord_429431) baseStart_429431 baseEnd_429431 := by
    simpa [prefixWord, tailWord_429431, baseEnd_429431] using wordTrace_append hprefix tailTrace_429431
  have hstable : (prefixWord ++ tailWord_429431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429431).length < 2 ^ (prefixWord ++ tailWord_429431).sum := by decide
  have hdescent : baseEnd_429431 < baseStart_429431 := by decide
  rcases family_descends (prefixWord ++ tailWord_429431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429465 : List Nat := [1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_429465 : Nat := 118140960795 + 429465 * 2 ^ 59
def prefixEnd_429465 : Nat := 4983230072969 + 3 ^ 40 * 429465 * 2
def baseEnd_429465 : Nat := 65339842750597762937017

theorem tailTrace_429465 : CollatzResearch.WordTrace tailWord_429465 prefixEnd_429465 65339842750597762937017 := by
  unfold tailWord_429465
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663875389129126627673849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10442583592752751085115899 15663875389129126627673849)
  ·
    refine ⟨11747906541846844970755387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15663875389129126627673849 11747906541846844970755387)
    ·
      refine ⟨17621859812770267456133081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11747906541846844970755387 17621859812770267456133081)
      ·
        refine ⟨13216394859577700592099811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17621859812770267456133081 13216394859577700592099811)
        ·
          refine ⟨19824592289366550888149717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13216394859577700592099811 19824592289366550888149717)
          ·
            refine ⟨464638881782028536441009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19824592289366550888149717 464638881782028536441009)
            ·
              refine ⟨348479161336521402330757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464638881782028536441009 348479161336521402330757)
              ·
                refine ⟨65339842750597762937017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348479161336521402330757 65339842750597762937017)
                ·
                  rfl

theorem cell20_429465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_429465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429465 prefixEnd_429465 := by exact prefixLift 429465
  have htrace : WordTrace (prefixWord ++ tailWord_429465) baseStart_429465 baseEnd_429465 := by
    simpa [prefixWord, tailWord_429465, baseEnd_429465] using wordTrace_append hprefix tailTrace_429465
  have hstable : (prefixWord ++ tailWord_429465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429465).length < 2 ^ (prefixWord ++ tailWord_429465).sum := by decide
  have hdescent : baseEnd_429465 < baseStart_429465 := by decide
  rcases family_descends (prefixWord ++ tailWord_429465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429507 : List Nat := [1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_429507 : Nat := 118140960795 + 429507 * 2 ^ 59
def prefixEnd_429507 : Nat := 4983230072969 + 3 ^ 40 * 429507 * 2
def baseEnd_429507 : Nat := 65346232732075936470293

theorem tailTrace_429507 : CollatzResearch.WordTrace tailWord_429507 prefixEnd_429507 65346232732075936470293 := by
  unfold tailWord_429507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15665407254976967800702775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10443604836651311867135183 15665407254976967800702775)
  ·
    refine ⟨23498110882465451701054163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15665407254976967800702775 23498110882465451701054163)
    ·
      refine ⟨35247166323698177551581245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23498110882465451701054163 35247166323698177551581245)
      ·
        refine ⟨13217687371386816581842967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35247166323698177551581245 13217687371386816581842967)
        ·
          refine ⟨19826531057080224872764451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217687371386816581842967 19826531057080224872764451)
          ·
            refine ⟨29739796585620337309146677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19826531057080224872764451 29739796585620337309146677)
            ·
              refine ⟨2788105929901906622732501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29739796585620337309146677 2788105929901906622732501)
              ·
                refine ⟨65346232732075936470293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2788105929901906622732501 65346232732075936470293)
                ·
                  rfl

theorem cell20_429507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_429507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429507 prefixEnd_429507 := by exact prefixLift 429507
  have htrace : WordTrace (prefixWord ++ tailWord_429507) baseStart_429507 baseEnd_429507 := by
    simpa [prefixWord, tailWord_429507, baseEnd_429507] using wordTrace_append hprefix tailTrace_429507
  have hstable : (prefixWord ++ tailWord_429507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429507).length < 2 ^ (prefixWord ++ tailWord_429507).sum := by decide
  have hdescent : baseEnd_429507 < baseStart_429507 := by decide
  rcases family_descends (prefixWord ++ tailWord_429507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429572 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_429572 : Nat := 118140960795 + 429572 * 2 ^ 59
def prefixEnd_429572 : Nat := 4983230072969 + 3 ^ 40 * 429572 * 2
def baseEnd_429572 : Nat := 196068365967376472243947

theorem tailTrace_429572 : CollatzResearch.WordTrace tailWord_429572 prefixEnd_429572 196068365967376472243947 := by
  unfold tailWord_429572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833888999870741950909485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10445185333160989267879313 7833888999870741950909485)
  ·
    refine ⟨2937708374951528231591057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7833888999870741950909485 2937708374951528231591057)
    ·
      refine ⟨2203281281213646173693293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2937708374951528231591057 2203281281213646173693293)
      ·
        refine ⟨826230480455117315134985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2203281281213646173693293 826230480455117315134985)
        ·
          refine ⟨619672860341337986351239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826230480455117315134985 619672860341337986351239)
          ·
            refine ⟨929509290512006979526859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619672860341337986351239 929509290512006979526859)
            ·
              refine ⟨1394263935768010469290289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929509290512006979526859 1394263935768010469290289)
              ·
                refine ⟨1045697951826007851967717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394263935768010469290289 1045697951826007851967717)
                ·
                  refine ⟨196068365967376472243947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045697951826007851967717 196068365967376472243947)
                  ·
                    rfl

theorem cell20_429572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_429572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429572 prefixEnd_429572 := by exact prefixLift 429572
  have htrace : WordTrace (prefixWord ++ tailWord_429572) baseStart_429572 baseEnd_429572 := by
    simpa [prefixWord, tailWord_429572, baseEnd_429572] using wordTrace_append hprefix tailTrace_429572
  have hstable : (prefixWord ++ tailWord_429572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429572).length < 2 ^ (prefixWord ++ tailWord_429572).sum := by decide
  have hdescent : baseEnd_429572 < baseStart_429572 := by decide
  rcases family_descends (prefixWord ++ tailWord_429572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429576 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_429576 : Nat := 118140960795 + 429576 * 2 ^ 59
def prefixEnd_429576 : Nat := 4983230072969 + 3 ^ 40 * 429576 * 2
def baseEnd_429576 : Nat := 196070191676370236110597

theorem tailTrace_429576 : CollatzResearch.WordTrace tailWord_429576 prefixEnd_429576 196070191676370236110597 := by
  unfold tailWord_429576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833961945863496292482291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10445282594484661723309721 7833961945863496292482291)
  ·
    refine ⟨11750942918795244438723437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833961945863496292482291 11750942918795244438723437)
    ·
      refine ⟨4406603594548216664521289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11750942918795244438723437 4406603594548216664521289)
      ·
        refine ⟨3304952695911162498390967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4406603594548216664521289 3304952695911162498390967)
        ·
          refine ⟨4957429043866743747586451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304952695911162498390967 4957429043866743747586451)
          ·
            refine ⟨7436143565800115621379677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957429043866743747586451 7436143565800115621379677)
            ·
              refine ⟨2788553837175043358017379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7436143565800115621379677 2788553837175043358017379)
              ·
                refine ⟨4182830755762565037026069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788553837175043358017379 4182830755762565037026069)
                ·
                  refine ⟨196070191676370236110597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4182830755762565037026069 196070191676370236110597)
                  ·
                    rfl

theorem cell20_429576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_429576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429576 prefixEnd_429576 := by exact prefixLift 429576
  have htrace : WordTrace (prefixWord ++ tailWord_429576) baseStart_429576 baseEnd_429576 := by
    simpa [prefixWord, tailWord_429576, baseEnd_429576] using wordTrace_append hprefix tailTrace_429576
  have hstable : (prefixWord ++ tailWord_429576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429576).length < 2 ^ (prefixWord ++ tailWord_429576).sum := by decide
  have hdescent : baseEnd_429576 < baseStart_429576 := by decide
  rcases family_descends (prefixWord ++ tailWord_429576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429579 : List Nat := [1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_429579 : Nat := 118140960795 + 429579 * 2 ^ 59
def prefixEnd_429579 : Nat := 4983230072969 + 3 ^ 40 * 429579 * 2
def baseEnd_429579 : Nat := 65357186986038519670195

theorem tailTrace_429579 : CollatzResearch.WordTrace tailWord_429579 prefixEnd_429579 65357186986038519670195 := by
  unfold tailWord_429579
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668033310716124097323791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10445355540477416064882527 15668033310716124097323791)
  ·
    refine ⟨23502049966074186145985687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15668033310716124097323791 23502049966074186145985687)
    ·
      refine ⟨35253074949111279218978531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23502049966074186145985687 35253074949111279218978531)
      ·
        refine ⟨52879612423666918828467797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35253074949111279218978531 52879612423666918828467797)
        ·
          refine ⟨619682958089846705021107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 52879612423666918828467797 619682958089846705021107)
          ·
            refine ⟨929524437134770057531661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619682958089846705021107 929524437134770057531661)
            ·
              refine ⟨348571663925538771574373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929524437134770057531661 348571663925538771574373)
              ·
                refine ⟨65357186986038519670195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348571663925538771574373 65357186986038519670195)
                ·
                  rfl

theorem cell20_429579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_429579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429579 prefixEnd_429579 := by exact prefixLift 429579
  have htrace : WordTrace (prefixWord ++ tailWord_429579) baseStart_429579 baseEnd_429579 := by
    simpa [prefixWord, tailWord_429579, baseEnd_429579] using wordTrace_append hprefix tailTrace_429579
  have hstable : (prefixWord ++ tailWord_429579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429579).length < 2 ^ (prefixWord ++ tailWord_429579).sum := by decide
  have hdescent : baseEnd_429579 < baseStart_429579 := by decide
  rcases family_descends (prefixWord ++ tailWord_429579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429600 : List Nat := [2, 1, 1, 6, 1, 2, 7]
def baseStart_429600 : Nat := 118140960795 + 429600 * 2 ^ 59
def prefixEnd_429600 : Nat := 4983230072969 + 3 ^ 40 * 429600 * 2
def baseEnd_429600 : Nat := 21786793992259202145611

theorem tailTrace_429600 : CollatzResearch.WordTrace tailWord_429600 prefixEnd_429600 21786793992259202145611 := by
  unfold tailWord_429600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7834399621820022341919127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10445866162426696455892169 7834399621820022341919127)
  ·
    refine ⟨11751599432730033512878691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7834399621820022341919127 11751599432730033512878691)
    ·
      refine ⟨17627399149095050269318037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11751599432730033512878691 17627399149095050269318037)
      ·
        refine ⟨826284335113830481374283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17627399149095050269318037 826284335113830481374283)
        ·
          refine ⟨1239426502670745722061425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826284335113830481374283 1239426502670745722061425)
          ·
            refine ⟨929569877003059291546069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239426502670745722061425 929569877003059291546069)
            ·
              refine ⟨21786793992259202145611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 929569877003059291546069 21786793992259202145611)
              ·
                rfl

theorem cell20_429600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_429600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429600 prefixEnd_429600 := by exact prefixLift 429600
  have htrace : WordTrace (prefixWord ++ tailWord_429600) baseStart_429600 baseEnd_429600 := by
    simpa [prefixWord, tailWord_429600, baseEnd_429600] using wordTrace_append hprefix tailTrace_429600
  have hstable : (prefixWord ++ tailWord_429600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429600).length < 2 ^ (prefixWord ++ tailWord_429600).sum := by decide
  have hdescent : baseEnd_429600 < baseStart_429600 := by decide
  rcases family_descends (prefixWord ++ tailWord_429600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429603 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_429603 : Nat := 118140960795 + 429603 * 2 ^ 59
def prefixEnd_429603 : Nat := 4983230072969 + 3 ^ 40 * 429603 * 2
def baseEnd_429603 : Nat := 196082515212078142210487

theorem tailTrace_429603 : CollatzResearch.WordTrace tailWord_429603 prefixEnd_429603 196082515212078142210487 := by
  unfold tailWord_429603
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668908662629176196197463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10445939108419450797464975 15668908662629176196197463)
  ·
    refine ⟨23503362993943764294296195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15668908662629176196197463 23503362993943764294296195)
    ·
      refine ⟨35255044490915646441444293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23503362993943764294296195 35255044490915646441444293)
      ·
        refine ⟨6610320842046683707770805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35255044490915646441444293 6610320842046683707770805)
        ·
          refine ⟨619717578941876597603513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6610320842046683707770805 619717578941876597603513)
          ·
            refine ⟨464788184206407448202635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619717578941876597603513 464788184206407448202635)
            ·
              refine ⟨697182276309611172303953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464788184206407448202635 697182276309611172303953)
              ·
                refine ⟨522886707232208379227965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697182276309611172303953 522886707232208379227965)
                ·
                  refine ⟨196082515212078142210487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 522886707232208379227965 196082515212078142210487)
                  ·
                    rfl

theorem cell20_429603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_429603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429603 prefixEnd_429603 := by exact prefixLift 429603
  have htrace : WordTrace (prefixWord ++ tailWord_429603) baseStart_429603 baseEnd_429603 := by
    simpa [prefixWord, tailWord_429603, baseEnd_429603] using wordTrace_append hprefix tailTrace_429603
  have hstable : (prefixWord ++ tailWord_429603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429603).length < 2 ^ (prefixWord ++ tailWord_429603).sum := by decide
  have hdescent : baseEnd_429603 < baseStart_429603 := by decide
  rcases family_descends (prefixWord ++ tailWord_429603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429610 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_429610 : Nat := 118140960795 + 429610 * 2 ^ 59
def prefixEnd_429610 : Nat := 4983230072969 + 3 ^ 40 * 429610 * 2
def baseEnd_429610 : Nat := 196085710202817228977125

theorem tailTrace_429610 : CollatzResearch.WordTrace tailWord_429610 prefixEnd_429610 196085710202817228977125 := by
  unfold tailWord_429610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917290993400954097925571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10446109315735877594468189 3917290993400954097925571)
  ·
    refine ⟨5875936490101431146888357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3917290993400954097925571 5875936490101431146888357)
    ·
      refine ⟨1101738091894018340041567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5875936490101431146888357 1101738091894018340041567)
      ·
        refine ⟨1652607137841027510062351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101738091894018340041567 1652607137841027510062351)
        ·
          refine ⟨2478910706761541265093527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652607137841027510062351 2478910706761541265093527)
          ·
            refine ⟨3718366060142311897640291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478910706761541265093527 3718366060142311897640291)
            ·
              refine ⟨5577549090213467846460437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718366060142311897640291 5577549090213467846460437)
              ·
                refine ⟨261447613603756305302833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5577549090213467846460437 261447613603756305302833)
                ·
                  refine ⟨196085710202817228977125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261447613603756305302833 196085710202817228977125)
                  ·
                    rfl

theorem cell20_429610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_429610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429610 prefixEnd_429610 := by exact prefixLift 429610
  have htrace : WordTrace (prefixWord ++ tailWord_429610) baseStart_429610 baseEnd_429610 := by
    simpa [prefixWord, tailWord_429610, baseEnd_429610] using wordTrace_append hprefix tailTrace_429610
  have hstable : (prefixWord ++ tailWord_429610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429610).length < 2 ^ (prefixWord ++ tailWord_429610).sum := by decide
  have hdescent : baseEnd_429610 < baseStart_429610 := by decide
  rcases family_descends (prefixWord ++ tailWord_429610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429661 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 2]
def baseStart_429661 : Nat := 118140960795 + 429661 * 2 ^ 59
def prefixEnd_429661 : Nat := 4983230072969 + 3 ^ 40 * 429661 * 2
def baseEnd_429661 : Nat := 196108987992487718276917

theorem tailTrace_429661 : CollatzResearch.WordTrace tailWord_429661 prefixEnd_429661 196108987992487718276917 := by
  unfold tailWord_429661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671024096419052101808837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10447349397612701401205891 15671024096419052101808837)
  ·
    refine ⟨2938317018078572269089157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15671024096419052101808837 2938317018078572269089157)
    ·
      refine ⟨550934440889732300454217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2938317018078572269089157 550934440889732300454217)
      ·
        refine ⟨413200830667299225340663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550934440889732300454217 413200830667299225340663)
        ·
          refine ⟨619801246000948838010995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413200830667299225340663 619801246000948838010995)
          ·
            refine ⟨929701869001423257016493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619801246000948838010995 929701869001423257016493)
            ·
              refine ⟨348638200875533721381185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929701869001423257016493 348638200875533721381185)
              ·
                refine ⟨261478650656650291035889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348638200875533721381185 261478650656650291035889)
                ·
                  refine ⟨196108987992487718276917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261478650656650291035889 196108987992487718276917)
                  ·
                    rfl

theorem cell20_429661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_429661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429661 prefixEnd_429661 := by exact prefixLift 429661
  have htrace : WordTrace (prefixWord ++ tailWord_429661) baseStart_429661 baseEnd_429661 := by
    simpa [prefixWord, tailWord_429661, baseEnd_429661] using wordTrace_append hprefix tailTrace_429661
  have hstable : (prefixWord ++ tailWord_429661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429661).length < 2 ^ (prefixWord ++ tailWord_429661).sum := by decide
  have hdescent : baseEnd_429661 < baseStart_429661 := by decide
  rcases family_descends (prefixWord ++ tailWord_429661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429669 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_429669 : Nat := 118140960795 + 429669 * 2 ^ 59
def prefixEnd_429669 : Nat := 4983230072969 + 3 ^ 40 * 429669 * 2
def baseEnd_429669 : Nat := 196112639410475246010217

theorem tailTrace_429669 : CollatzResearch.WordTrace tailWord_429669 prefixEnd_429669 196112639410475246010217 := by
  unfold tailWord_429669
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671315880390069468100061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10447543920260046312066707 15671315880390069468100061)
  ·
    refine ⟨5876743455146276050537523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15671315880390069468100061 5876743455146276050537523)
    ·
      refine ⟨8815115182719414075806285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5876743455146276050537523 8815115182719414075806285)
      ·
        refine ⟨3305668193519780278427357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8815115182719414075806285 3305668193519780278427357)
        ·
          refine ⟨1239625572569917604410259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3305668193519780278427357 1239625572569917604410259)
          ·
            refine ⟨1859438358854876406615389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239625572569917604410259 1859438358854876406615389)
            ·
              refine ⟨697289384570578652480771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859438358854876406615389 697289384570578652480771)
              ·
                refine ⟨1045934076855867978721157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697289384570578652480771 1045934076855867978721157)
                ·
                  refine ⟨196112639410475246010217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045934076855867978721157 196112639410475246010217)
                  ·
                    rfl

theorem cell20_429669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_429669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429669 prefixEnd_429669 := by exact prefixLift 429669
  have htrace : WordTrace (prefixWord ++ tailWord_429669) baseStart_429669 baseEnd_429669 := by
    simpa [prefixWord, tailWord_429669, baseEnd_429669] using wordTrace_append hprefix tailTrace_429669
  have hstable : (prefixWord ++ tailWord_429669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429669).length < 2 ^ (prefixWord ++ tailWord_429669).sum := by decide
  have hdescent : baseEnd_429669 < baseStart_429669 := by decide
  rcases family_descends (prefixWord ++ tailWord_429669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429707 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 2]
def baseStart_429707 : Nat := 118140960795 + 429707 * 2 ^ 59
def prefixEnd_429707 : Nat := 4983230072969 + 3 ^ 40 * 429707 * 2
def baseEnd_429707 : Nat := 196129983645916002743395

theorem tailTrace_429707 : CollatzResearch.WordTrace tailWord_429707 prefixEnd_429707 196129983645916002743395 := by
  unfold tailWord_429707
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672701854252401957983375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10448467902834934638655583 15672701854252401957983375)
  ·
    refine ⟨23509052781378602936975063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15672701854252401957983375 23509052781378602936975063)
    ·
      refine ⟨35263579172067904405462595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23509052781378602936975063 35263579172067904405462595)
      ·
        refine ⟨52895368758101856608193893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35263579172067904405462595 52895368758101856608193893)
        ·
          refine ⟨9917881642144098114036355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52895368758101856608193893 9917881642144098114036355)
          ·
            refine ⟨14876822463216147171054533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9917881642144098114036355 14876822463216147171054533)
            ·
              refine ⟨2789404211853027594572725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14876822463216147171054533 2789404211853027594572725)
              ·
                refine ⟨261506644861221336991193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2789404211853027594572725 261506644861221336991193)
                ·
                  refine ⟨196129983645916002743395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261506644861221336991193 196129983645916002743395)
                  ·
                    rfl

theorem cell20_429707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2].length) (baseStart_429707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429707 prefixEnd_429707 := by exact prefixLift 429707
  have htrace : WordTrace (prefixWord ++ tailWord_429707) baseStart_429707 baseEnd_429707 := by
    simpa [prefixWord, tailWord_429707, baseEnd_429707] using wordTrace_append hprefix tailTrace_429707
  have hstable : (prefixWord ++ tailWord_429707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429707).length < 2 ^ (prefixWord ++ tailWord_429707).sum := by decide
  have hdescent : baseEnd_429707 < baseStart_429707 := by decide
  rcases family_descends (prefixWord ++ tailWord_429707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429714 : List Nat := [3, 2, 3, 1, 3, 8]
def baseStart_429714 : Nat := 118140960795 + 429714 * 2 ^ 59
def prefixEnd_429714 : Nat := 4983230072969 + 3 ^ 40 * 429714 * 2
def baseEnd_429714 : Nat := 7264191801357595907779

theorem tailTrace_429714 : CollatzResearch.WordTrace tailWord_429714 prefixEnd_429714 7264191801357595907779 := by
  unfold tailWord_429714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918239291306760538372049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10448638110151361435658797 3918239291306760538372049)
  ·
    refine ⟨2938679468480070403779037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3918239291306760538372049 2938679468480070403779037)
    ·
      refine ⟨1102004800680026401417139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2938679468480070403779037 1102004800680026401417139)
      ·
        refine ⟨1653007201020039602125709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102004800680026401417139 1653007201020039602125709)
        ·
          refine ⟨619877700382514850797141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1653007201020039602125709 619877700382514850797141)
          ·
            refine ⟨7264191801357595907779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 619877700382514850797141 7264191801357595907779)
            ·
              rfl

theorem cell20_429714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 8].length) (baseStart_429714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429714 prefixEnd_429714 := by exact prefixLift 429714
  have htrace : WordTrace (prefixWord ++ tailWord_429714) baseStart_429714 baseEnd_429714 := by
    simpa [prefixWord, tailWord_429714, baseEnd_429714] using wordTrace_append hprefix tailTrace_429714
  have hstable : (prefixWord ++ tailWord_429714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429714).length < 2 ^ (prefixWord ++ tailWord_429714).sum := by decide
  have hdescent : baseEnd_429714 < baseStart_429714 := by decide
  rcases family_descends (prefixWord ++ tailWord_429714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429772 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_429772 : Nat := 118140960795 + 429772 * 2 ^ 59
def prefixEnd_429772 : Nat := 4983230072969 + 3 ^ 40 * 429772 * 2
def baseEnd_429772 : Nat := 196159651417064665576463

theorem tailTrace_429772 : CollatzResearch.WordTrace tailWord_429772 prefixEnd_429772 196159651417064665576463 := by
  unfold tailWord_429772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837536299508459029549785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10450048399344612039399713 7837536299508459029549785)
  ·
    refine ⟨5878152224631344272162339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7837536299508459029549785 5878152224631344272162339)
    ·
      refine ⟨8817228336947016408243509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5878152224631344272162339 8817228336947016408243509)
      ·
        refine ⟨826615156588782788272829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8817228336947016408243509 826615156588782788272829)
        ·
          refine ⟨309980683720793545602311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 826615156588782788272829 309980683720793545602311)
          ·
            refine ⟨464971025581190318403467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309980683720793545602311 464971025581190318403467)
            ·
              refine ⟨697456538371785477605201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464971025581190318403467 697456538371785477605201)
              ·
                refine ⟨523092403778839108203901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697456538371785477605201 523092403778839108203901)
                ·
                  refine ⟨196159651417064665576463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523092403778839108203901 196159651417064665576463)
                  ·
                    rfl

theorem cell20_429772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_429772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429772 prefixEnd_429772 := by exact prefixLift 429772
  have htrace : WordTrace (prefixWord ++ tailWord_429772) baseStart_429772 baseEnd_429772 := by
    simpa [prefixWord, tailWord_429772, baseEnd_429772] using wordTrace_append hprefix tailTrace_429772
  have hstable : (prefixWord ++ tailWord_429772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429772).length < 2 ^ (prefixWord ++ tailWord_429772).sum := by decide
  have hdescent : baseEnd_429772 < baseStart_429772 := by decide
  rcases family_descends (prefixWord ++ tailWord_429772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429783 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 2]
def baseStart_429783 : Nat := 118140960795 + 429783 * 2 ^ 59
def prefixEnd_429783 : Nat := 4983230072969 + 3 ^ 40 * 429783 * 2
def baseEnd_429783 : Nat := 196164672116797516209751

theorem tailTrace_429783 : CollatzResearch.WordTrace tailWord_429783 prefixEnd_429783 196164672116797516209751 := by
  unfold tailWord_429783
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675473801977066937750003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10450315867984711291833335 15675473801977066937750003)
  ·
    refine ⟨23513210702965600406625005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15675473801977066937750003 23513210702965600406625005)
    ·
      refine ⟨8817454013612100152484377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23513210702965600406625005 8817454013612100152484377)
      ·
        refine ⟨6613090510209075114363283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8817454013612100152484377 6613090510209075114363283)
        ·
          refine ⟨9919635765313612671544925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613090510209075114363283 9919635765313612671544925)
          ·
            refine ⟨3719863411992604751829347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9919635765313612671544925 3719863411992604751829347)
            ·
              refine ⟨5579795117988907127744021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719863411992604751829347 5579795117988907127744021)
              ·
                refine ⟨261552896155730021613001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5579795117988907127744021 261552896155730021613001)
                ·
                  refine ⟨196164672116797516209751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261552896155730021613001 196164672116797516209751)
                  ·
                    rfl

theorem cell20_429783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 2].length) (baseStart_429783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429783 prefixEnd_429783 := by exact prefixLift 429783
  have htrace : WordTrace (prefixWord ++ tailWord_429783) baseStart_429783 baseEnd_429783 := by
    simpa [prefixWord, tailWord_429783, baseEnd_429783] using wordTrace_append hprefix tailTrace_429783
  have hstable : (prefixWord ++ tailWord_429783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429783).length < 2 ^ (prefixWord ++ tailWord_429783).sum := by decide
  have hdescent : baseEnd_429783 < baseStart_429783 := by decide
  rcases family_descends (prefixWord ++ tailWord_429783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429793 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 3]
def baseStart_429793 : Nat := 118140960795 + 429793 * 2 ^ 59
def prefixEnd_429793 : Nat := 4983230072969 + 3 ^ 40 * 429793 * 2
def baseEnd_429793 : Nat := 196169236389281925876377

theorem tailTrace_429793 : CollatzResearch.WordTrace tailWord_429793 prefixEnd_429793 196169236389281925876377 := by
  unfold tailWord_429793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675838531940838645614033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10450559021293892430409355 15675838531940838645614033)
  ·
    refine ⟨11756878898955628984210525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15675838531940838645614033 11756878898955628984210525)
    ·
      refine ⟨4408829587108360869078947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11756878898955628984210525 4408829587108360869078947)
      ·
        refine ⟨6613244380662541303618421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408829587108360869078947 6613244380662541303618421)
        ·
          refine ⟨619991660687113247214227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6613244380662541303618421 619991660687113247214227)
          ·
            refine ⟨929987491030669870821341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619991660687113247214227 929987491030669870821341)
            ·
              refine ⟨348745309136501201558003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929987491030669870821341 348745309136501201558003)
              ·
                refine ⟨523117963704751802337005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348745309136501201558003 523117963704751802337005)
                ·
                  refine ⟨196169236389281925876377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523117963704751802337005 196169236389281925876377)
                  ·
                    rfl

theorem cell20_429793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_429793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429793 prefixEnd_429793 := by exact prefixLift 429793
  have htrace : WordTrace (prefixWord ++ tailWord_429793) baseStart_429793 baseEnd_429793 := by
    simpa [prefixWord, tailWord_429793, baseEnd_429793] using wordTrace_append hprefix tailTrace_429793
  have hstable : (prefixWord ++ tailWord_429793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429793).length < 2 ^ (prefixWord ++ tailWord_429793).sum := by decide
  have hdescent : baseEnd_429793 < baseStart_429793 := by decide
  rcases family_descends (prefixWord ++ tailWord_429793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429804 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_429804 : Nat := 118140960795 + 429804 * 2 ^ 59
def prefixEnd_429804 : Nat := 4983230072969 + 3 ^ 40 * 429804 * 2
def baseEnd_429804 : Nat := 196174257089014776509665

theorem tailTrace_429804 : CollatzResearch.WordTrace tailWord_429804 prefixEnd_429804 196174257089014776509665 := by
  unfold tailWord_429804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838119867450493762132233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10450826489933991682842977 7838119867450493762132233)
  ·
    refine ⟨5878589900587870321599175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7838119867450493762132233 5878589900587870321599175)
    ·
      refine ⟨8817884850881805482398763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5878589900587870321599175 8817884850881805482398763)
      ·
        refine ⟨13226827276322708223598145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8817884850881805482398763 13226827276322708223598145)
        ·
          refine ⟨9920120457242031167698609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13226827276322708223598145 9920120457242031167698609)
          ·
            refine ⟨7440090342931523375773957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9920120457242031167698609 7440090342931523375773957)
            ·
              refine ⟨1395016939299660632957617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7440090342931523375773957 1395016939299660632957617)
              ·
                refine ⟨1046262704474745474718213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395016939299660632957617 1046262704474745474718213)
                ·
                  refine ⟨196174257089014776509665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046262704474745474718213 196174257089014776509665)
                  ·
                    rfl

theorem cell20_429804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_429804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429804 prefixEnd_429804 := by exact prefixLift 429804
  have htrace : WordTrace (prefixWord ++ tailWord_429804) baseStart_429804 baseEnd_429804 := by
    simpa [prefixWord, tailWord_429804, baseEnd_429804] using wordTrace_append hprefix tailTrace_429804
  have hstable : (prefixWord ++ tailWord_429804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429804).length < 2 ^ (prefixWord ++ tailWord_429804).sum := by decide
  have hdescent : baseEnd_429804 < baseStart_429804 := by decide
  rcases family_descends (prefixWord ++ tailWord_429804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429821 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 2]
def baseStart_429821 : Nat := 118140960795 + 429821 * 2 ^ 59
def prefixEnd_429821 : Nat := 4983230072969 + 3 ^ 40 * 429821 * 2
def baseEnd_429821 : Nat := 196182016352238272942929

theorem tailTrace_429821 : CollatzResearch.WordTrace tailWord_429821 prefixEnd_429821 196182016352238272942929 := by
  unfold tailWord_429821
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676859775839399427633317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10451239850559599618422211 15676859775839399427633317)
  ·
    refine ⟨2939411207969887392681247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15676859775839399427633317 2939411207969887392681247)
    ·
      refine ⟨4409116811954831089021871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939411207969887392681247 4409116811954831089021871)
      ·
        refine ⟨6613675217932246633532807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409116811954831089021871 6613675217932246633532807)
        ·
          refine ⟨9920512826898369950299211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613675217932246633532807 9920512826898369950299211)
          ·
            refine ⟨14880769240347554925448817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920512826898369950299211 14880769240347554925448817)
            ·
              refine ⟨11160576930260666194086613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14880769240347554925448817 11160576930260666194086613)
              ·
                refine ⟨261576021802984363923905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11160576930260666194086613 261576021802984363923905)
                ·
                  refine ⟨196182016352238272942929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261576021802984363923905 196182016352238272942929)
                  ·
                    rfl

theorem cell20_429821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_429821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429821 prefixEnd_429821 := by exact prefixLift 429821
  have htrace : WordTrace (prefixWord ++ tailWord_429821) baseStart_429821 baseEnd_429821 := by
    simpa [prefixWord, tailWord_429821, baseEnd_429821] using wordTrace_append hprefix tailTrace_429821
  have hstable : (prefixWord ++ tailWord_429821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429821).length < 2 ^ (prefixWord ++ tailWord_429821).sum := by decide
  have hdescent : baseEnd_429821 < baseStart_429821 := by decide
  rcases family_descends (prefixWord ++ tailWord_429821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429828 : List Nat := [2, 3, 2, 2, 1, 4, 6]
def baseStart_429828 : Nat := 118140960795 + 429828 * 2 ^ 59
def prefixEnd_429828 : Nat := 4983230072969 + 3 ^ 40 * 429828 * 2
def baseEnd_429828 : Nat := 21798356815886373301063

theorem tailTrace_429828 : CollatzResearch.WordTrace tailWord_429828 prefixEnd_429828 21798356815886373301063 := by
  unfold tailWord_429828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838557543407019811569069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10451410057876026415425425 7838557543407019811569069)
  ·
    refine ⟨2939459078777632429338401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7838557543407019811569069 2939459078777632429338401)
    ·
      refine ⟨2204594309083224322003801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2939459078777632429338401 2204594309083224322003801)
      ·
        refine ⟨1653445731812418241502851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2204594309083224322003801 1653445731812418241502851)
        ·
          refine ⟨2480168597718627362254277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653445731812418241502851 2480168597718627362254277)
          ·
            refine ⟨465031612072242630422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2480168597718627362254277 465031612072242630422677)
            ·
              refine ⟨21798356815886373301063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 465031612072242630422677 21798356815886373301063)
              ·
                rfl

theorem cell20_429828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_429828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429828 prefixEnd_429828 := by exact prefixLift 429828
  have htrace : WordTrace (prefixWord ++ tailWord_429828) baseStart_429828 baseEnd_429828 := by
    simpa [prefixWord, tailWord_429828, baseEnd_429828] using wordTrace_append hprefix tailTrace_429828
  have hstable : (prefixWord ++ tailWord_429828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429828).length < 2 ^ (prefixWord ++ tailWord_429828).sum := by decide
  have hdescent : baseEnd_429828 < baseStart_429828 := by decide
  rcases family_descends (prefixWord ++ tailWord_429828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429830 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_429830 : Nat := 118140960795 + 429830 * 2 ^ 59
def prefixEnd_429830 : Nat := 4983230072969 + 3 ^ 40 * 429830 * 2
def baseEnd_429830 : Nat := 196186124197474241642893

theorem tailTrace_429830 : CollatzResearch.WordTrace tailWord_429830 prefixEnd_429830 196186124197474241642893 := by
  unfold tailWord_429830
  simp only [CollatzResearch.WordTrace]
  refine ⟨489912126025212311397217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10451458688537862643140629 489912126025212311397217)
  ·
    refine ⟨367434094518909233547913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 489912126025212311397217 367434094518909233547913)
    ·
      refine ⟨275575570889181925160935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367434094518909233547913 275575570889181925160935)
      ·
        refine ⟨413363356333772887741403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275575570889181925160935 413363356333772887741403)
        ·
          refine ⟨620045034500659331612105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413363356333772887741403 620045034500659331612105)
          ·
            refine ⟨465033775875494498709079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620045034500659331612105 465033775875494498709079)
            ·
              refine ⟨697550663813241748063619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465033775875494498709079 697550663813241748063619)
              ·
                refine ⟨1046325995719862622095429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697550663813241748063619 1046325995719862622095429)
                ·
                  refine ⟨196186124197474241642893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046325995719862622095429 196186124197474241642893)
                  ·
                    rfl

theorem cell20_429830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_429830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429830 prefixEnd_429830 := by exact prefixLift 429830
  have htrace : WordTrace (prefixWord ++ tailWord_429830) baseStart_429830 baseEnd_429830 := by
    simpa [prefixWord, tailWord_429830, baseEnd_429830] using wordTrace_append hprefix tailTrace_429830
  have hstable : (prefixWord ++ tailWord_429830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429830).length < 2 ^ (prefixWord ++ tailWord_429830).sum := by decide
  have hdescent : baseEnd_429830 < baseStart_429830 := by decide
  rcases family_descends (prefixWord ++ tailWord_429830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429844 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_429844 : Nat := 118140960795 + 429844 * 2 ^ 59
def prefixEnd_429844 : Nat := 4983230072969 + 3 ^ 40 * 429844 * 2
def baseEnd_429844 : Nat := 196192514178952415176169

theorem tailTrace_429844 : CollatzResearch.WordTrace tailWord_429844 prefixEnd_429844 196192514178952415176169 := by
  unfold tailWord_429844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838849327378037177860293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10451799103170716237147057 7838849327378037177860293)
  ·
    refine ⟨1469784248883381970848805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7838849327378037177860293 1469784248883381970848805)
    ·
      refine ⟨275584546665634119534151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1469784248883381970848805 275584546665634119534151)
      ·
        refine ⟨413376819998451179301227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275584546665634119534151 413376819998451179301227)
        ·
          refine ⟨620065229997676768951841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413376819998451179301227 620065229997676768951841)
          ·
            refine ⟨465048922498257576713881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620065229997676768951841 465048922498257576713881)
            ·
              refine ⟨348786691873693182535411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465048922498257576713881 348786691873693182535411)
              ·
                refine ⟨523180037810539773803117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348786691873693182535411 523180037810539773803117)
                ·
                  refine ⟨196192514178952415176169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523180037810539773803117 196192514178952415176169)
                  ·
                    rfl

theorem cell20_429844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_429844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429844 prefixEnd_429844 := by exact prefixLift 429844
  have htrace : WordTrace (prefixWord ++ tailWord_429844) baseStart_429844 baseEnd_429844 := by
    simpa [prefixWord, tailWord_429844, baseEnd_429844] using wordTrace_append hprefix tailTrace_429844
  have hstable : (prefixWord ++ tailWord_429844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429844).length < 2 ^ (prefixWord ++ tailWord_429844).sum := by decide
  have hdescent : baseEnd_429844 < baseStart_429844 := by decide
  rcases family_descends (prefixWord ++ tailWord_429844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429887 : List Nat := [1, 1, 2, 2, 6, 8]
def baseStart_429887 : Nat := 118140960795 + 429887 * 2 ^ 59
def prefixEnd_429887 : Nat := 4983230072969 + 3 ^ 40 * 429887 * 2
def baseEnd_429887 : Nat := 7267116316690199138617

theorem tailTrace_429887 : CollatzResearch.WordTrace tailWord_429887 prefixEnd_429887 7267116316690199138617 := by
  unfold tailWord_429887
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679266993600292699535915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10452844662400195133023943 15679266993600292699535915)
  ·
    refine ⟨23518900490400439049303873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15679266993600292699535915 23518900490400439049303873)
    ·
      refine ⟨17639175367800329286977905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23518900490400439049303873 17639175367800329286977905)
      ·
        refine ⟨13229381525850246965233429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17639175367800329286977905 13229381525850246965233429)
        ·
          refine ⟨620127259024230326495317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13229381525850246965233429 620127259024230326495317)
          ·
            refine ⟨7267116316690199138617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 620127259024230326495317 7267116316690199138617)
            ·
              rfl

theorem cell20_429887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 8].length) (baseStart_429887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429887 prefixEnd_429887 := by exact prefixLift 429887
  have htrace : WordTrace (prefixWord ++ tailWord_429887) baseStart_429887 baseEnd_429887 := by
    simpa [prefixWord, tailWord_429887, baseEnd_429887] using wordTrace_append hprefix tailTrace_429887
  have hstable : (prefixWord ++ tailWord_429887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429887).length < 2 ^ (prefixWord ++ tailWord_429887).sum := by decide
  have hdescent : baseEnd_429887 < baseStart_429887 := by decide
  rcases family_descends (prefixWord ++ tailWord_429887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429897 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 2]
def baseStart_429897 : Nat := 118140960795 + 429897 * 2 ^ 59
def prefixEnd_429897 : Nat := 4983230072969 + 3 ^ 40 * 429897 * 2
def baseEnd_429897 : Nat := 196216704823119786409285

theorem tailTrace_429897 : CollatzResearch.WordTrace tailWord_429897 prefixEnd_429897 196216704823119786409285 := by
  unfold tailWord_429897
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679631723564064407399945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10453087815709376271599963 15679631723564064407399945)
  ·
    refine ⟨11759723792673048305549959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15679631723564064407399945 11759723792673048305549959)
    ·
      refine ⟨17639585689009572458324939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11759723792673048305549959 17639585689009572458324939)
      ·
        refine ⟨26459378533514358687487409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17639585689009572458324939 26459378533514358687487409)
        ·
          refine ⟨19844533900135769015615557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26459378533514358687487409 19844533900135769015615557)
          ·
            refine ⟨3720850106275456690427917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19844533900135769015615557 3720850106275456690427917)
            ·
              refine ⟨1395318789853296258910469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720850106275456690427917 1395318789853296258910469)
              ·
                refine ⟨261622273097493048545713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1395318789853296258910469 261622273097493048545713)
                ·
                  refine ⟨196216704823119786409285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261622273097493048545713 196216704823119786409285)
                  ·
                    rfl

theorem cell20_429897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_429897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429897 prefixEnd_429897 := by exact prefixLift 429897
  have htrace : WordTrace (prefixWord ++ tailWord_429897) baseStart_429897 baseEnd_429897 := by
    simpa [prefixWord, tailWord_429897, baseEnd_429897] using wordTrace_append hprefix tailTrace_429897
  have hstable : (prefixWord ++ tailWord_429897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429897).length < 2 ^ (prefixWord ++ tailWord_429897).sum := by decide
  have hdescent : baseEnd_429897 < baseStart_429897 := by decide
  rcases family_descends (prefixWord ++ tailWord_429897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429939 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_429939 : Nat := 118140960795 + 429939 * 2 ^ 59
def prefixEnd_429939 : Nat := 4983230072969 + 3 ^ 40 * 429939 * 2
def baseEnd_429939 : Nat := 196235874767554307009113

theorem tailTrace_429939 : CollatzResearch.WordTrace tailWord_429939 prefixEnd_429939 196235874767554307009113 := by
  unfold tailWord_429939
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681163589411905580428871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10454109059607937053619247 15681163589411905580428871)
  ·
    refine ⟨23521745384117858370643307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15681163589411905580428871 23521745384117858370643307)
    ·
      refine ⟨35282618076176787555964961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23521745384117858370643307 35282618076176787555964961)
      ·
        refine ⟨26461963557132590666973721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35282618076176787555964961 26461963557132590666973721)
        ·
          refine ⟨19846472667849443000230291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26461963557132590666973721 19846472667849443000230291)
          ·
            refine ⟨29769709001774164500345437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19846472667849443000230291 29769709001774164500345437)
            ·
              refine ⟨11163640875665311687629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29769709001774164500345437 11163640875665311687629539)
              ·
                refine ⟨16745461313497967531444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163640875665311687629539 16745461313497967531444309)
                ·
                  refine ⟨196235874767554307009113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16745461313497967531444309 196235874767554307009113)
                  ·
                    rfl

theorem cell20_429939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_429939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429939 prefixEnd_429939 := by exact prefixLift 429939
  have htrace : WordTrace (prefixWord ++ tailWord_429939) baseStart_429939 baseEnd_429939 := by
    simpa [prefixWord, tailWord_429939, baseEnd_429939] using wordTrace_append hprefix tailTrace_429939
  have hstable : (prefixWord ++ tailWord_429939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429939).length < 2 ^ (prefixWord ++ tailWord_429939).sum := by decide
  have hdescent : baseEnd_429939 < baseStart_429939 := by decide
  rcases family_descends (prefixWord ++ tailWord_429939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429956 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_429956 : Nat := 118140960795 + 429956 * 2 ^ 59
def prefixEnd_429956 : Nat := 4983230072969 + 3 ^ 40 * 429956 * 2
def baseEnd_429956 : Nat := 196243634030777803442377

theorem tailTrace_429956 : CollatzResearch.WordTrace tailWord_429956 prefixEnd_429956 196243634030777803442377 := by
  unfold tailWord_429956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7840891815175158741898861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10454522420233544989198481 7840891815175158741898861)
  ·
    refine ⟨2940334430690684528212073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7840891815175158741898861 2940334430690684528212073)
    ·
      refine ⟨2205250823018013396159055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2940334430690684528212073 2205250823018013396159055)
      ·
        refine ⟨3307876234527020094238583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205250823018013396159055 3307876234527020094238583)
        ·
          refine ⟨4961814351790530141357875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307876234527020094238583 4961814351790530141357875)
          ·
            refine ⟨7442721527685795212036813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961814351790530141357875 7442721527685795212036813)
            ·
              refine ⟨2791020572882173204513805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7442721527685795212036813 2791020572882173204513805)
              ·
                refine ⟨1046632714830814951692677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791020572882173204513805 1046632714830814951692677)
                ·
                  refine ⟨196243634030777803442377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046632714830814951692677 196243634030777803442377)
                  ·
                    rfl

theorem cell20_429956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_429956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429956 prefixEnd_429956 := by exact prefixLift 429956
  have htrace : WordTrace (prefixWord ++ tailWord_429956) baseStart_429956 baseEnd_429956 := by
    simpa [prefixWord, tailWord_429956, baseEnd_429956] using wordTrace_append hprefix tailTrace_429956
  have hstable : (prefixWord ++ tailWord_429956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429956).length < 2 ^ (prefixWord ++ tailWord_429956).sum := by decide
  have hdescent : baseEnd_429956 < baseStart_429956 := by decide
  rcases family_descends (prefixWord ++ tailWord_429956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429976 : List Nat := [2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_429976 : Nat := 118140960795 + 429976 * 2 ^ 59
def prefixEnd_429976 : Nat := 4983230072969 + 3 ^ 40 * 429976 * 2
def baseEnd_429976 : Nat := 65417587525248874258543

theorem tailTrace_429976 : CollatzResearch.WordTrace tailWord_429976 prefixEnd_429976 65417587525248874258543 := by
  unfold tailWord_429976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841256545138930449762891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10455008726851907266350521 7841256545138930449762891)
  ·
    refine ⟨11761884817708395674644337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7841256545138930449762891 11761884817708395674644337)
    ·
      refine ⟨8821413613281296755983253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761884817708395674644337 8821413613281296755983253)
      ·
        refine ⟨413503763122560785436715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8821413613281296755983253 413503763122560785436715)
        ·
          refine ⟨620255644683841178155073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413503763122560785436715 620255644683841178155073)
          ·
            refine ⟨465191733512880883616305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620255644683841178155073 465191733512880883616305)
            ·
              refine ⟨348893800134660662712229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465191733512880883616305 348893800134660662712229)
              ·
                refine ⟨65417587525248874258543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348893800134660662712229 65417587525248874258543)
                ·
                  rfl

theorem cell20_429976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_429976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429976 prefixEnd_429976 := by exact prefixLift 429976
  have htrace : WordTrace (prefixWord ++ tailWord_429976) baseStart_429976 baseEnd_429976 := by
    simpa [prefixWord, tailWord_429976, baseEnd_429976] using wordTrace_append hprefix tailTrace_429976
  have hstable : (prefixWord ++ tailWord_429976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429976).length < 2 ^ (prefixWord ++ tailWord_429976).sum := by decide
  have hdescent : baseEnd_429976 < baseStart_429976 := by decide
  rcases family_descends (prefixWord ++ tailWord_429976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429980 : List Nat := [2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_429980 : Nat := 118140960795 + 429980 * 2 ^ 59
def prefixEnd_429980 : Nat := 4983230072969 + 3 ^ 40 * 429980 * 2
def baseEnd_429980 : Nat := 65418196094913462214093

theorem tailTrace_429980 : CollatzResearch.WordTrace tailWord_429980 prefixEnd_429980 65418196094913462214093 := by
  unfold tailWord_429980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841329491131684791335697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10455105988175579721780929 7841329491131684791335697)
  ·
    refine ⟨5880997118348763593501773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7841329491131684791335697 5880997118348763593501773)
    ·
      refine ⟨2205373919380786347563165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5880997118348763593501773 2205373919380786347563165)
      ·
        refine ⟨827015219767794880336187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2205373919380786347563165 827015219767794880336187)
        ·
          refine ⟨1240522829651692320504281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827015219767794880336187 1240522829651692320504281)
          ·
            refine ⟨930392122238769240378211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240522829651692320504281 930392122238769240378211)
            ·
              refine ⟨1395588183358153860567317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930392122238769240378211 1395588183358153860567317)
              ·
                refine ⟨65418196094913462214093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1395588183358153860567317 65418196094913462214093)
                ·
                  rfl

theorem cell20_429980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_429980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429980 prefixEnd_429980 := by exact prefixLift 429980
  have htrace : WordTrace (prefixWord ++ tailWord_429980) baseStart_429980 baseEnd_429980 := by
    simpa [prefixWord, tailWord_429980, baseEnd_429980] using wordTrace_append hprefix tailTrace_429980
  have hstable : (prefixWord ++ tailWord_429980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429980).length < 2 ^ (prefixWord ++ tailWord_429980).sum := by decide
  have hdescent : baseEnd_429980 < baseStart_429980 := by decide
  rcases family_descends (prefixWord ++ tailWord_429980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429986 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_429986 : Nat := 118140960795 + 429986 * 2 ^ 59
def prefixEnd_429986 : Nat := 4983230072969 + 3 ^ 40 * 429986 * 2
def baseEnd_429986 : Nat := 196257326848231032442255

theorem tailTrace_429986 : CollatzResearch.WordTrace tailWord_429986 prefixEnd_429986 196257326848231032442255 := by
  unfold tailWord_429986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920719455060408151847453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10455251880161088404926541 3920719455060408151847453)
  ·
    refine ⟨1470269795647653056942795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3920719455060408151847453 1470269795647653056942795)
    ·
      refine ⟨2205404693471479585414193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470269795647653056942795 2205404693471479585414193)
      ·
        refine ⟨1654053520103609689060645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2205404693471479585414193 1654053520103609689060645)
        ·
          refine ⟨310135035019426816698871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1654053520103609689060645 310135035019426816698871)
          ·
            refine ⟨465202552529140225048307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310135035019426816698871 465202552529140225048307)
            ·
              refine ⟨697803828793710337572461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465202552529140225048307 697803828793710337572461)
              ·
                refine ⟨261676435797641376589673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697803828793710337572461 261676435797641376589673)
                ·
                  refine ⟨196257326848231032442255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261676435797641376589673 196257326848231032442255)
                  ·
                    rfl

theorem cell20_429986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_429986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_429986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_429986 prefixEnd_429986 := by exact prefixLift 429986
  have htrace : WordTrace (prefixWord ++ tailWord_429986) baseStart_429986 baseEnd_429986 := by
    simpa [prefixWord, tailWord_429986, baseEnd_429986] using wordTrace_append hprefix tailTrace_429986
  have hstable : (prefixWord ++ tailWord_429986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429986).length < 2 ^ (prefixWord ++ tailWord_429986).sum := by decide
  have hdescent : baseEnd_429986 < baseStart_429986 := by decide
  rcases family_descends (prefixWord ++ tailWord_429986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430001 : List Nat := [1, 2, 2, 4, 2, 1, 8]
def baseStart_430001 : Nat := 118140960795 + 430001 * 2 ^ 59
def prefixEnd_430001 : Nat := 4983230072969 + 3 ^ 40 * 430001 * 2
def baseEnd_430001 : Nat := 21807130361884182993577

theorem tailTrace_430001 : CollatzResearch.WordTrace tailWord_430001 prefixEnd_430001 21807130361884182993577 := by
  unfold tailWord_430001
  simp only [CollatzResearch.WordTrace]
  refine ⟨15683424915187290169185857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10455616610124860112790571 15683424915187290169185857)
  ·
    refine ⟨11762568686390467626889393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15683424915187290169185857 11762568686390467626889393)
    ·
      refine ⟨8821926514792850720167045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11762568686390467626889393 8821926514792850720167045)
      ·
        refine ⟨1654111221523659510031321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8821926514792850720167045 1654111221523659510031321)
        ·
          refine ⟨1240583416142744632523491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654111221523659510031321 1240583416142744632523491)
          ·
            refine ⟨1860875124214116948785237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240583416142744632523491 1860875124214116948785237)
            ·
              refine ⟨21807130361884182993577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1860875124214116948785237 21807130361884182993577)
              ·
                rfl

theorem cell20_430001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_430001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430001 prefixEnd_430001 := by exact prefixLift 430001
  have htrace : WordTrace (prefixWord ++ tailWord_430001) baseStart_430001 baseEnd_430001 := by
    simpa [prefixWord, tailWord_430001, baseEnd_430001] using wordTrace_append hprefix tailTrace_430001
  have hstable : (prefixWord ++ tailWord_430001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430001).length < 2 ^ (prefixWord ++ tailWord_430001).sum := by decide
  have hdescent : baseEnd_430001 < baseStart_430001 := by decide
  rcases family_descends (prefixWord ++ tailWord_430001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430008 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_430008 : Nat := 118140960795 + 430008 * 2 ^ 59
def prefixEnd_430008 : Nat := 4983230072969 + 3 ^ 40 * 430008 * 2
def baseEnd_430008 : Nat := 196267368247696733708831

theorem tailTrace_430008 : CollatzResearch.WordTrace tailWord_430008 prefixEnd_430008 196267368247696733708831 := by
  unfold tailWord_430008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841840113080965182345339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10455786817441286909793785 7841840113080965182345339)
  ·
    refine ⟨11762760169621447773518009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7841840113080965182345339 11762760169621447773518009)
    ·
      refine ⟨8822070127216085830138507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11762760169621447773518009 8822070127216085830138507)
      ·
        refine ⟨13233105190824128745207761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822070127216085830138507 13233105190824128745207761)
        ·
          refine ⟨9924828893118096558905821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13233105190824128745207761 9924828893118096558905821)
          ·
            refine ⟨3721810834919286209589683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9924828893118096558905821 3721810834919286209589683)
            ·
              refine ⟨5582716252378929314384525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721810834919286209589683 5582716252378929314384525)
              ·
                refine ⟨2093518594642098492894197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5582716252378929314384525 2093518594642098492894197)
                ·
                  refine ⟨196267368247696733708831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2093518594642098492894197 196267368247696733708831)
                  ·
                    rfl

theorem cell20_430008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_430008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430008 prefixEnd_430008 := by exact prefixLift 430008
  have htrace : WordTrace (prefixWord ++ tailWord_430008) baseStart_430008 baseEnd_430008 := by
    simpa [prefixWord, tailWord_430008, baseEnd_430008] using wordTrace_append hprefix tailTrace_430008
  have hstable : (prefixWord ++ tailWord_430008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430008).length < 2 ^ (prefixWord ++ tailWord_430008).sum := by decide
  have hdescent : baseEnd_430008 < baseStart_430008 := by decide
  rcases family_descends (prefixWord ++ tailWord_430008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430063 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_430063 : Nat := 118140960795 + 430063 * 2 ^ 59
def prefixEnd_430063 : Nat := 4983230072969 + 3 ^ 40 * 430063 * 2
def baseEnd_430063 : Nat := 196292471746360986875273

theorem tailTrace_430063 : CollatzResearch.WordTrace tailWord_430063 prefixEnd_430063 196292471746360986875273 := by
  unfold tailWord_430063
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685686240962674757942843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10457124160641783171961895 15685686240962674757942843)
  ·
    refine ⟨23528529361444012136914265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15685686240962674757942843 23528529361444012136914265)
    ·
      refine ⟨17646397021083009102685699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23528529361444012136914265 17646397021083009102685699)
      ·
        refine ⟨26469595531624513654028549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17646397021083009102685699 26469595531624513654028549)
        ·
          refine ⟨4963049162179596310130353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26469595531624513654028549 4963049162179596310130353)
          ·
            refine ⟨3722286871634697232597765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963049162179596310130353 3722286871634697232597765)
            ·
              refine ⟨697928788431505731112081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3722286871634697232597765 697928788431505731112081)
              ·
                refine ⟨523446591323629298334061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697928788431505731112081 523446591323629298334061)
                ·
                  refine ⟨196292471746360986875273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523446591323629298334061 196292471746360986875273)
                  ·
                    rfl

theorem cell20_430063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_430063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430063 prefixEnd_430063 := by exact prefixLift 430063
  have htrace : WordTrace (prefixWord ++ tailWord_430063) baseStart_430063 baseEnd_430063 := by
    simpa [prefixWord, tailWord_430063, baseEnd_430063] using wordTrace_append hprefix tailTrace_430063
  have hstable : (prefixWord ++ tailWord_430063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430063).length < 2 ^ (prefixWord ++ tailWord_430063).sum := by decide
  have hdescent : baseEnd_430063 < baseStart_430063 := by decide
  rcases family_descends (prefixWord ++ tailWord_430063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430077 : List Nat := [1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_430077 : Nat := 118140960795 + 430077 * 2 ^ 59
def prefixEnd_430077 : Nat := 4983230072969 + 3 ^ 40 * 430077 * 2
def baseEnd_430077 : Nat := 65432953909279720136183

theorem tailTrace_430077 : CollatzResearch.WordTrace tailWord_430077 prefixEnd_430077 65432953909279720136183 := by
  unfold tailWord_430077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15686196862911955148952485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10457464575274636765968323 15686196862911955148952485)
  ·
    refine ⟨2941161911795991590428591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15686196862911955148952485 2941161911795991590428591)
    ·
      refine ⟨4411742867693987385642887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941161911795991590428591 4411742867693987385642887)
      ·
        refine ⟨6617614301540981078464331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411742867693987385642887 6617614301540981078464331)
        ·
          refine ⟨9926421452311471617696497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617614301540981078464331 9926421452311471617696497)
          ·
            refine ⟨7444816089233603713272373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9926421452311471617696497 7444816089233603713272373)
            ·
              refine ⟨697951508365650348119285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7444816089233603713272373 697951508365650348119285)
              ·
                refine ⟨65432953909279720136183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 697951508365650348119285 65432953909279720136183)
                ·
                  rfl

theorem cell20_430077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_430077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430077 prefixEnd_430077 := by exact prefixLift 430077
  have htrace : WordTrace (prefixWord ++ tailWord_430077) baseStart_430077 baseEnd_430077 := by
    simpa [prefixWord, tailWord_430077, baseEnd_430077] using wordTrace_append hprefix tailTrace_430077
  have hstable : (prefixWord ++ tailWord_430077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430077).length < 2 ^ (prefixWord ++ tailWord_430077).sum := by decide
  have hdescent : baseEnd_430077 < baseStart_430077 := by decide
  rcases family_descends (prefixWord ++ tailWord_430077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430086 : List Nat := [6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_430086 : Nat := 118140960795 + 430086 * 2 ^ 59
def prefixEnd_430086 : Nat := 4983230072969 + 3 ^ 40 * 430086 * 2
def baseEnd_430086 : Nat := 65434323191025043036171

theorem tailTrace_430086 : CollatzResearch.WordTrace tailWord_430086 prefixEnd_430086 65434323191025043036171 := by
  unfold tailWord_430086
  simp only [CollatzResearch.WordTrace]
  refine ⟨490203909996229677688441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10457683413252899790686741 490203909996229677688441)
  ·
    refine ⟨367652932497172258266331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 490203909996229677688441 367652932497172258266331)
    ·
      refine ⟨551479398745758387399497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367652932497172258266331 551479398745758387399497)
      ·
        refine ⟨413609549059318790549623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551479398745758387399497 413609549059318790549623)
        ·
          refine ⟨620414323588978185824435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413609549059318790549623 620414323588978185824435)
          ·
            refine ⟨930621485383467278736653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620414323588978185824435 930621485383467278736653)
            ·
              refine ⟨348983057018800229526245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 930621485383467278736653 348983057018800229526245)
              ·
                refine ⟨65434323191025043036171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348983057018800229526245 65434323191025043036171)
                ·
                  rfl

theorem cell20_430086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_430086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430086 prefixEnd_430086 := by exact prefixLift 430086
  have htrace : WordTrace (prefixWord ++ tailWord_430086) baseStart_430086 baseEnd_430086 := by
    simpa [prefixWord, tailWord_430086, baseEnd_430086] using wordTrace_append hprefix tailTrace_430086
  have hstable : (prefixWord ++ tailWord_430086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430086).length < 2 ^ (prefixWord ++ tailWord_430086).sum := by decide
  have hdescent : baseEnd_430086 < baseStart_430086 := by decide
  rcases family_descends (prefixWord ++ tailWord_430086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430094 : List Nat := [4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_430094 : Nat := 118140960795 + 430094 * 2 ^ 59
def prefixEnd_430094 : Nat := 4983230072969 + 3 ^ 40 * 430094 * 2
def baseEnd_430094 : Nat := 65435540330354218947271

theorem tailTrace_430094 : CollatzResearch.WordTrace tailWord_430094 prefixEnd_430094 65435540330354218947271 := by
  unfold tailWord_430094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960852112981295881540167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10457877935900244701547557 1960852112981295881540167)
  ·
    refine ⟨2941278169471943822310251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960852112981295881540167 2941278169471943822310251)
    ·
      refine ⟨4411917254207915733465377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941278169471943822310251 4411917254207915733465377)
      ·
        refine ⟨3308937940655936800099033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411917254207915733465377 3308937940655936800099033)
        ·
          refine ⟨2481703455491952600074275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308937940655936800099033 2481703455491952600074275)
          ·
            refine ⟨3722555183237928900111413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481703455491952600074275 3722555183237928900111413)
            ·
              refine ⟨348989548428555834385445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3722555183237928900111413 348989548428555834385445)
              ·
                refine ⟨65435540330354218947271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348989548428555834385445 65435540330354218947271)
                ·
                  rfl

theorem cell20_430094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_430094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430094 prefixEnd_430094 := by exact prefixLift 430094
  have htrace : WordTrace (prefixWord ++ tailWord_430094) baseStart_430094 baseEnd_430094 := by
    simpa [prefixWord, tailWord_430094, baseEnd_430094] using wordTrace_append hprefix tailTrace_430094
  have hstable : (prefixWord ++ tailWord_430094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430094).length < 2 ^ (prefixWord ++ tailWord_430094).sum := by decide
  have hdescent : baseEnd_430094 < baseStart_430094 := by decide
  rcases family_descends (prefixWord ++ tailWord_430094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430100 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_430100 : Nat := 118140960795 + 430100 * 2 ^ 59
def prefixEnd_430100 : Nat := 4983230072969 + 3 ^ 40 * 430100 * 2
def baseEnd_430100 : Nat := 196309359554553302641789

theorem tailTrace_430100 : CollatzResearch.WordTrace tailWord_430100 prefixEnd_430100 196309359554553302641789 := by
  unfold tailWord_430100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843517870914315038519877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10458023827885753384693169 7843517870914315038519877)
  ·
    refine ⟨1470659600796434069722477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7843517870914315038519877 1470659600796434069722477)
    ·
      refine ⟨551497350298662776145929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1470659600796434069722477 551497350298662776145929)
      ·
        refine ⟨413623012723997082109447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551497350298662776145929 413623012723997082109447)
        ·
          refine ⟨620434519085995623164171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413623012723997082109447 620434519085995623164171)
          ·
            refine ⟨930651778628993434746257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620434519085995623164171 930651778628993434746257)
            ·
              refine ⟨697988833971745076059693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930651778628993434746257 697988833971745076059693)
              ·
                refine ⟨261745812739404403522385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697988833971745076059693 261745812739404403522385)
                ·
                  refine ⟨196309359554553302641789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261745812739404403522385 196309359554553302641789)
                  ·
                    rfl

theorem cell20_430100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_430100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430100 prefixEnd_430100 := by exact prefixLift 430100
  have htrace : WordTrace (prefixWord ++ tailWord_430100) baseStart_430100 baseEnd_430100 := by
    simpa [prefixWord, tailWord_430100, baseEnd_430100] using wordTrace_append hprefix tailTrace_430100
  have hstable : (prefixWord ++ tailWord_430100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430100).length < 2 ^ (prefixWord ++ tailWord_430100).sum := by decide
  have hdescent : baseEnd_430100 < baseStart_430100 := by decide
  rcases family_descends (prefixWord ++ tailWord_430100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430167 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_430167 : Nat := 118140960795 + 430167 * 2 ^ 59
def prefixEnd_430167 : Nat := 4983230072969 + 3 ^ 40 * 430167 * 2
def baseEnd_430167 : Nat := 196339940180198847408181

theorem tailTrace_430167 : CollatzResearch.WordTrace tailWord_430167 prefixEnd_430167 196339940180198847408181 := by
  unfold tailWord_430167
  simp only [CollatzResearch.WordTrace]
  refine ⟨15689479432585900519728755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10459652955057267013152503 15689479432585900519728755)
  ·
    refine ⟨23534219148878850779593133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15689479432585900519728755 23534219148878850779593133)
    ·
      refine ⟨8825332180829569042347425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23534219148878850779593133 8825332180829569042347425)
      ·
        refine ⟨6618999135622176781760569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8825332180829569042347425 6618999135622176781760569)
        ·
          refine ⟨4964249351716632586320427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6618999135622176781760569 4964249351716632586320427)
          ·
            refine ⟨7446374027574948879480641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964249351716632586320427 7446374027574948879480641)
            ·
              refine ⟨5584780520681211659610481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7446374027574948879480641 5584780520681211659610481)
              ·
                refine ⟨4188585390510908744707861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5584780520681211659610481 4188585390510908744707861)
                ·
                  refine ⟨196339940180198847408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4188585390510908744707861 196339940180198847408181)
                  ·
                    rfl

theorem cell20_430167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_430167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430167 prefixEnd_430167 := by exact prefixLift 430167
  have htrace : WordTrace (prefixWord ++ tailWord_430167) baseStart_430167 baseEnd_430167 := by
    simpa [prefixWord, tailWord_430167, baseEnd_430167] using wordTrace_append hprefix tailTrace_430167
  have hstable : (prefixWord ++ tailWord_430167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430167).length < 2 ^ (prefixWord ++ tailWord_430167).sum := by decide
  have hdescent : baseEnd_430167 < baseStart_430167 := by decide
  rcases family_descends (prefixWord ++ tailWord_430167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430191 : List Nat := [1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_430191 : Nat := 118140960795 + 430191 * 2 ^ 59
def prefixEnd_430191 : Nat := 4983230072969 + 3 ^ 40 * 430191 * 2
def baseEnd_430191 : Nat := 65450298144720476869361

theorem tailTrace_430191 : CollatzResearch.WordTrace tailWord_430191 prefixEnd_430191 65450298144720476869361 := by
  unfold tailWord_430191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15690354784498952618602427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10460236522999301745734951 15690354784498952618602427)
  ·
    refine ⟨23535532176748428927903641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15690354784498952618602427 23535532176748428927903641)
    ·
      refine ⟨17651649132561321695927731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23535532176748428927903641 17651649132561321695927731)
      ·
        refine ⟨26477473698841982543891597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17651649132561321695927731 26477473698841982543891597)
        ·
          refine ⟨9929052637065743453959349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26477473698841982543891597 9929052637065743453959349)
          ·
            refine ⟨930848684724913448808689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9929052637065743453959349 930848684724913448808689)
            ·
              refine ⟨698136513543685086606517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930848684724913448808689 698136513543685086606517)
              ·
                refine ⟨65450298144720476869361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 698136513543685086606517 65450298144720476869361)
                ·
                  rfl

theorem cell20_430191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_430191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430191 prefixEnd_430191 := by exact prefixLift 430191
  have htrace : WordTrace (prefixWord ++ tailWord_430191) baseStart_430191 baseEnd_430191 := by
    simpa [prefixWord, tailWord_430191, baseEnd_430191] using wordTrace_append hprefix tailTrace_430191
  have hstable : (prefixWord ++ tailWord_430191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430191).length < 2 ^ (prefixWord ++ tailWord_430191).sum := by decide
  have hdescent : baseEnd_430191 < baseStart_430191 := by decide
  rcases family_descends (prefixWord ++ tailWord_430191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430194 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_430194 : Nat := 118140960795 + 430194 * 2 ^ 59
def prefixEnd_430194 : Nat := 4983230072969 + 3 ^ 40 * 430194 * 2
def baseEnd_430194 : Nat := 196352263715906753508071

theorem tailTrace_430194 : CollatzResearch.WordTrace tailWord_430194 prefixEnd_430194 196352263715906753508071 := by
  unfold tailWord_430194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922616050872021032740409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10460309468992056087307757 3922616050872021032740409)
  ·
    refine ⟨2941962038154015774555307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3922616050872021032740409 2941962038154015774555307)
    ·
      refine ⟨4412943057231023661832961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941962038154015774555307 4412943057231023661832961)
      ·
        refine ⟨3309707292923267746374721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4412943057231023661832961 3309707292923267746374721)
        ·
          refine ⟨2482280469692450809781041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3309707292923267746374721 2482280469692450809781041)
          ·
            refine ⟨1861710352269338107335781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482280469692450809781041 1861710352269338107335781)
            ·
              refine ⟨349070691050500895125459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1861710352269338107335781 349070691050500895125459)
              ·
                refine ⟨523606036575751342688189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349070691050500895125459 523606036575751342688189)
                ·
                  refine ⟨196352263715906753508071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523606036575751342688189 196352263715906753508071)
                  ·
                    rfl

theorem cell20_430194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_430194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430194 prefixEnd_430194 := by exact prefixLift 430194
  have htrace : WordTrace (prefixWord ++ tailWord_430194) baseStart_430194 baseEnd_430194 := by
    simpa [prefixWord, tailWord_430194, baseEnd_430194] using wordTrace_append hprefix tailTrace_430194
  have hstable : (prefixWord ++ tailWord_430194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430194).length < 2 ^ (prefixWord ++ tailWord_430194).sum := by decide
  have hdescent : baseEnd_430194 < baseStart_430194 := by decide
  rcases family_descends (prefixWord ++ tailWord_430194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430232 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_430232 : Nat := 118140960795 + 430232 * 2 ^ 59
def prefixEnd_430232 : Nat := 4983230072969 + 3 ^ 40 * 430232 * 2
def baseEnd_430232 : Nat := 196369607951347510241249

theorem tailTrace_430232 : CollatzResearch.WordTrace tailWord_430232 prefixEnd_430232 196369607951347510241249 := by
  unfold tailWord_430232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845925088675208310422475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10461233451566944413896633 7845925088675208310422475)
  ·
    refine ⟨11768887633012812465633713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7845925088675208310422475 11768887633012812465633713)
    ·
      refine ⟨8826665724759609349225285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11768887633012812465633713 8826665724759609349225285)
      ·
        refine ⟨1654999823392426752979741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8826665724759609349225285 1654999823392426752979741)
        ·
          refine ⟨620624933772160032367403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1654999823392426752979741 620624933772160032367403)
          ·
            refine ⟨930937400658240048551105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620624933772160032367403 930937400658240048551105)
            ·
              refine ⟨698203050493680036413329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930937400658240048551105 698203050493680036413329)
              ·
                refine ⟨523652287870260027309997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698203050493680036413329 523652287870260027309997)
                ·
                  refine ⟨196369607951347510241249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523652287870260027309997 196369607951347510241249)
                  ·
                    rfl

theorem cell20_430232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_430232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430232 prefixEnd_430232 := by exact prefixLift 430232
  have htrace : WordTrace (prefixWord ++ tailWord_430232) baseStart_430232 baseEnd_430232 := by
    simpa [prefixWord, tailWord_430232, baseEnd_430232] using wordTrace_append hprefix tailTrace_430232
  have hstable : (prefixWord ++ tailWord_430232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430232).length < 2 ^ (prefixWord ++ tailWord_430232).sum := by decide
  have hdescent : baseEnd_430232 < baseStart_430232 := by decide
  rcases family_descends (prefixWord ++ tailWord_430232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430267 : List Nat := [1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_430267 : Nat := 118140960795 + 430267 * 2 ^ 59
def prefixEnd_430267 : Nat := 4983230072969 + 3 ^ 40 * 430267 * 2
def baseEnd_430267 : Nat := 65461860968347648024813

theorem tailTrace_430267 : CollatzResearch.WordTrace tailWord_430267 prefixEnd_430267 65461860968347648024813 := by
  unfold tailWord_430267
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693126732223617598369055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10462084488149078398912703 15693126732223617598369055)
  ·
    refine ⟨23539690098335426397553583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15693126732223617598369055 23539690098335426397553583)
    ·
      refine ⟨35309535147503139596330375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23539690098335426397553583 35309535147503139596330375)
      ·
        refine ⟨52964302721254709394495563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35309535147503139596330375 52964302721254709394495563)
        ·
          refine ⟨79446454081882064091743345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52964302721254709394495563 79446454081882064091743345)
          ·
            refine ⟨59584840561411548068807509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79446454081882064091743345 59584840561411548068807509)
            ·
              refine ⟨349129925164520789465669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 59584840561411548068807509 349129925164520789465669)
              ·
                refine ⟨65461860968347648024813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349129925164520789465669 65461860968347648024813)
                ·
                  rfl

theorem cell20_430267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_430267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430267 prefixEnd_430267 := by exact prefixLift 430267
  have htrace : WordTrace (prefixWord ++ tailWord_430267) baseStart_430267 baseEnd_430267 := by
    simpa [prefixWord, tailWord_430267, baseEnd_430267] using wordTrace_append hprefix tailTrace_430267
  have hstable : (prefixWord ++ tailWord_430267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430267).length < 2 ^ (prefixWord ++ tailWord_430267).sum := by decide
  have hdescent : baseEnd_430267 < baseStart_430267 := by decide
  rcases family_descends (prefixWord ++ tailWord_430267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430273 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 2]
def baseStart_430273 : Nat := 118140960795 + 430273 * 2 ^ 59
def prefixEnd_430273 : Nat := 4983230072969 + 3 ^ 40 * 430273 * 2
def baseEnd_430273 : Nat := 196388321468533589874415

theorem tailTrace_430273 : CollatzResearch.WordTrace tailWord_430273 prefixEnd_430273 196388321468533589874415 := by
  unfold tailWord_430273
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693345570201880623087473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10462230380134587082058315 15693345570201880623087473)
  ·
    refine ⟨11770009177651410467315605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15693345570201880623087473 11770009177651410467315605)
    ·
      refine ⟨551719180202409865655419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11770009177651410467315605 551719180202409865655419)
      ·
        refine ⟨827578770303614798483129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551719180202409865655419 827578770303614798483129)
        ·
          refine ⟨620684077727711098862347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827578770303614798483129 620684077727711098862347)
          ·
            refine ⟨931026116591566648293521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620684077727711098862347 931026116591566648293521)
            ·
              refine ⟨698269587443674986220141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931026116591566648293521 698269587443674986220141)
              ·
                refine ⟨261851095291378119832553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698269587443674986220141 261851095291378119832553)
                ·
                  refine ⟨196388321468533589874415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261851095291378119832553 196388321468533589874415)
                  ·
                    rfl

theorem cell20_430273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_430273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430273 prefixEnd_430273 := by exact prefixLift 430273
  have htrace : WordTrace (prefixWord ++ tailWord_430273) baseStart_430273 baseEnd_430273 := by
    simpa [prefixWord, tailWord_430273, baseEnd_430273] using wordTrace_append hprefix tailTrace_430273
  have hstable : (prefixWord ++ tailWord_430273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430273).length < 2 ^ (prefixWord ++ tailWord_430273).sum := by decide
  have hdescent : baseEnd_430273 < baseStart_430273 := by decide
  rcases family_descends (prefixWord ++ tailWord_430273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430284 : List Nat := [2, 2, 1, 6, 1, 1, 7]
def baseStart_430284 : Nat := 118140960795 + 430284 * 2 ^ 59
def prefixEnd_430284 : Nat := 4983230072969 + 3 ^ 40 * 430284 * 2
def baseEnd_430284 : Nat := 21821482463140715611967

theorem tailTrace_430284 : CollatzResearch.WordTrace tailWord_430284 prefixEnd_430284 21821482463140715611967 := by
  unfold tailWord_430284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846873386581014750868953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10462497848774686334491937 7846873386581014750868953)
  ·
    refine ⟨5885155039935761063151715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7846873386581014750868953 5885155039935761063151715)
    ·
      refine ⟨8827732559903641594727573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5885155039935761063151715 8827732559903641594727573)
      ·
        refine ⟨413799963745483199752855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8827732559903641594727573 413799963745483199752855)
        ·
          refine ⟨620699945618224799629283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413799963745483199752855 620699945618224799629283)
          ·
            refine ⟨931049918427337199443925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620699945618224799629283 931049918427337199443925)
            ·
              refine ⟨21821482463140715611967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 931049918427337199443925 21821482463140715611967)
              ·
                rfl

theorem cell20_430284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_430284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430284 prefixEnd_430284 := by exact prefixLift 430284
  have htrace : WordTrace (prefixWord ++ tailWord_430284) baseStart_430284 baseEnd_430284 := by
    simpa [prefixWord, tailWord_430284, baseEnd_430284] using wordTrace_append hprefix tailTrace_430284
  have hstable : (prefixWord ++ tailWord_430284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430284).length < 2 ^ (prefixWord ++ tailWord_430284).sum := by decide
  have hdescent : baseEnd_430284 < baseStart_430284 := by decide
  rcases family_descends (prefixWord ++ tailWord_430284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430294 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_430294 : Nat := 118140960795 + 430294 * 2 ^ 59
def prefixEnd_430294 : Nat := 4983230072969 + 3 ^ 40 * 430294 * 2
def baseEnd_430294 : Nat := 196397906440750850174329

theorem tailTrace_430294 : CollatzResearch.WordTrace tailWord_430294 prefixEnd_430294 196397906440750850174329 := by
  unfold tailWord_430294
  simp only [CollatzResearch.WordTrace]
  refine ⟨980881968945362575600121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10462741002083867473067957 980881968945362575600121)
  ·
    refine ⟨735661476709021931700091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 980881968945362575600121 735661476709021931700091)
    ·
      refine ⟨1103492215063532897550137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735661476709021931700091 1103492215063532897550137)
      ·
        refine ⟨827619161297649673162603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103492215063532897550137 827619161297649673162603)
        ·
          refine ⟨1241428741946474509743905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827619161297649673162603 1241428741946474509743905)
          ·
            refine ⟨931071556459855882307929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241428741946474509743905 931071556459855882307929)
            ·
              refine ⟨698303667344891911730947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931071556459855882307929 698303667344891911730947)
              ·
                refine ⟨1047455501017337867596421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698303667344891911730947 1047455501017337867596421)
                ·
                  refine ⟨196397906440750850174329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047455501017337867596421 196397906440750850174329)
                  ·
                    rfl

theorem cell20_430294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_430294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430294 prefixEnd_430294 := by exact prefixLift 430294
  have htrace : WordTrace (prefixWord ++ tailWord_430294) baseStart_430294 baseEnd_430294 := by
    simpa [prefixWord, tailWord_430294, baseEnd_430294] using wordTrace_append hprefix tailTrace_430294
  have hstable : (prefixWord ++ tailWord_430294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430294).length < 2 ^ (prefixWord ++ tailWord_430294).sum := by decide
  have hdescent : baseEnd_430294 < baseStart_430294 := by decide
  rcases family_descends (prefixWord ++ tailWord_430294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430322 : List Nat := [3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_430322 : Nat := 118140960795 + 430322 * 2 ^ 59
def prefixEnd_430322 : Nat := 4983230072969 + 3 ^ 40 * 430322 * 2
def baseEnd_430322 : Nat := 65470228801235732413627

theorem tailTrace_430322 : CollatzResearch.WordTrace tailWord_430322 prefixEnd_430322 65470228801235732413627 := by
  unfold tailWord_430322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923783186756090497905305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10463421831349574661080813 3923783186756090497905305)
  ·
    refine ⟨2942837390067067873428979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3923783186756090497905305 2942837390067067873428979)
    ·
      refine ⟨4414256085100601810143469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942837390067067873428979 4414256085100601810143469)
      ·
        refine ⟨1655346031912725678803801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4414256085100601810143469 1655346031912725678803801)
        ·
          refine ⟨1241509523934544259102851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655346031912725678803801 1241509523934544259102851)
          ·
            refine ⟨1862264285901816388654277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241509523934544259102851 1862264285901816388654277)
            ·
              refine ⟨349174553606590572872677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1862264285901816388654277 349174553606590572872677)
              ·
                refine ⟨65470228801235732413627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349174553606590572872677 65470228801235732413627)
                ·
                  rfl

theorem cell20_430322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_430322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430322 prefixEnd_430322 := by exact prefixLift 430322
  have htrace : WordTrace (prefixWord ++ tailWord_430322) baseStart_430322 baseEnd_430322 := by
    simpa [prefixWord, tailWord_430322, baseEnd_430322] using wordTrace_append hprefix tailTrace_430322
  have hstable : (prefixWord ++ tailWord_430322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430322).length < 2 ^ (prefixWord ++ tailWord_430322).sum := by decide
  have hdescent : baseEnd_430322 < baseStart_430322 := by decide
  rcases family_descends (prefixWord ++ tailWord_430322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430332 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_430332 : Nat := 118140960795 + 430332 * 2 ^ 59
def prefixEnd_430332 : Nat := 4983230072969 + 3 ^ 40 * 430332 * 2
def baseEnd_430332 : Nat := 196415250676191606907507

theorem tailTrace_430332 : CollatzResearch.WordTrace tailWord_430332 prefixEnd_430332 196415250676191606907507 := by
  unfold tailWord_430332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847748738494066849742625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10463664984658755799656833 7847748738494066849742625)
  ·
    refine ⟨5885811553870550137306969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7847748738494066849742625 5885811553870550137306969)
    ·
      refine ⟨4414358665402912602980227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5885811553870550137306969 4414358665402912602980227)
      ·
        refine ⟨6621537998104368904470341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414358665402912602980227 6621537998104368904470341)
        ·
          refine ⟨1241538374644569169588189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6621537998104368904470341 1241538374644569169588189)
          ·
            refine ⟨465576890491713438595571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1241538374644569169588189 465576890491713438595571)
            ·
              refine ⟨698365335737570157893357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465576890491713438595571 698365335737570157893357)
              ·
                refine ⟨261887000901588809210009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698365335737570157893357 261887000901588809210009)
                ·
                  refine ⟨196415250676191606907507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261887000901588809210009 196415250676191606907507)
                  ·
                    rfl

theorem cell20_430332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_430332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430332 prefixEnd_430332 := by exact prefixLift 430332
  have htrace : WordTrace (prefixWord ++ tailWord_430332) baseStart_430332 baseEnd_430332 := by
    simpa [prefixWord, tailWord_430332, baseEnd_430332] using wordTrace_append hprefix tailTrace_430332
  have hstable : (prefixWord ++ tailWord_430332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430332).length < 2 ^ (prefixWord ++ tailWord_430332).sum := by decide
  have hdescent : baseEnd_430332 < baseStart_430332 := by decide
  rcases family_descends (prefixWord ++ tailWord_430332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430350 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_430350 : Nat := 118140960795 + 430350 * 2 ^ 59
def prefixEnd_430350 : Nat := 4983230072969 + 3 ^ 40 * 430350 * 2
def baseEnd_430350 : Nat := 196423466366663544307433

theorem tailTrace_430350 : CollatzResearch.WordTrace tailWord_430350 prefixEnd_430350 196423466366663544307433 := by
  unfold tailWord_430350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962019248865365346705063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10464102660615281849093669 1962019248865365346705063)
  ·
    refine ⟨2943028873298048020057595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962019248865365346705063 2943028873298048020057595)
    ·
      refine ⟨4414543309947072030086393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943028873298048020057595 4414543309947072030086393)
      ·
        refine ⟨3310907482460304022564795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4414543309947072030086393 3310907482460304022564795)
        ·
          refine ⟨4966361223690456033847193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310907482460304022564795 4966361223690456033847193)
          ·
            refine ⟨3724770917767842025385395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966361223690456033847193 3724770917767842025385395)
            ·
              refine ⟨5587156376651763038078093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724770917767842025385395 5587156376651763038078093)
              ·
                refine ⟨2095183641244411139279285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587156376651763038078093 2095183641244411139279285)
                ·
                  refine ⟨196423466366663544307433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095183641244411139279285 196423466366663544307433)
                  ·
                    rfl

theorem cell20_430350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_430350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430350 prefixEnd_430350 := by exact prefixLift 430350
  have htrace : WordTrace (prefixWord ++ tailWord_430350) baseStart_430350 baseEnd_430350 := by
    simpa [prefixWord, tailWord_430350, baseEnd_430350] using wordTrace_append hprefix tailTrace_430350
  have hstable : (prefixWord ++ tailWord_430350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430350).length < 2 ^ (prefixWord ++ tailWord_430350).sum := by decide
  have hdescent : baseEnd_430350 < baseStart_430350 := by decide
  rcases family_descends (prefixWord ++ tailWord_430350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430367 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_430367 : Nat := 118140960795 + 430367 * 2 ^ 59
def prefixEnd_430367 : Nat := 4983230072969 + 3 ^ 40 * 430367 * 2
def baseEnd_430367 : Nat := 196431225629887040740697

theorem tailTrace_430367 : CollatzResearch.WordTrace tailWord_430367 prefixEnd_430367 196431225629887040740697 := by
  unfold tailWord_430367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696774031861334677009355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10464516021240889784672903 15696774031861334677009355)
  ·
    refine ⟨23545161047792002015514033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15696774031861334677009355 23545161047792002015514033)
    ·
      refine ⟨17658870785844001511635525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23545161047792002015514033 17658870785844001511635525)
      ·
        refine ⟨3311038272345750283431661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17658870785844001511635525 3311038272345750283431661)
        ·
          refine ⟨1241639352129656356286873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3311038272345750283431661 1241639352129656356286873)
          ·
            refine ⟨931229514097242267215155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241639352129656356286873 931229514097242267215155)
            ·
              refine ⟨1396844271145863400822733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931229514097242267215155 1396844271145863400822733)
              ·
                refine ⟨523816601679698775308525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396844271145863400822733 523816601679698775308525)
                ·
                  refine ⟨196431225629887040740697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523816601679698775308525 196431225629887040740697)
                  ·
                    rfl

theorem cell20_430367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_430367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430367 prefixEnd_430367 := by exact prefixLift 430367
  have htrace : WordTrace (prefixWord ++ tailWord_430367) baseStart_430367 baseEnd_430367 := by
    simpa [prefixWord, tailWord_430367, baseEnd_430367] using wordTrace_append hprefix tailTrace_430367
  have hstable : (prefixWord ++ tailWord_430367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430367).length < 2 ^ (prefixWord ++ tailWord_430367).sum := by decide
  have hdescent : baseEnd_430367 < baseStart_430367 := by decide
  rcases family_descends (prefixWord ++ tailWord_430367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430404 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_430404 : Nat := 118140960795 + 430404 * 2 ^ 59
def prefixEnd_430404 : Nat := 4983230072969 + 3 ^ 40 * 430404 * 2
def baseEnd_430404 : Nat := 196448113438079356507213

theorem tailTrace_430404 : CollatzResearch.WordTrace tailWord_430404 prefixEnd_430404 196448113438079356507213 := by
  unfold tailWord_430404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849061766363644998053133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10465415688484859997404177 7849061766363644998053133)
  ·
    refine ⟨2943398162386366874269925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7849061766363644998053133 2943398162386366874269925)
    ·
      refine ⟨551887155447443788925611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2943398162386366874269925 551887155447443788925611)
      ·
        refine ⟨827830733171165683388417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551887155447443788925611 827830733171165683388417)
        ·
          refine ⟨620873049878374262541313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827830733171165683388417 620873049878374262541313)
          ·
            refine ⟨465654787408780696905985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620873049878374262541313 465654787408780696905985)
            ·
              refine ⟨349241090556585522679489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465654787408780696905985 349241090556585522679489)
              ·
                refine ⟨261930817917439142009617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349241090556585522679489 261930817917439142009617)
                ·
                  refine ⟨196448113438079356507213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261930817917439142009617 196448113438079356507213)
                  ·
                    rfl

theorem cell20_430404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_430404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430404 prefixEnd_430404 := by exact prefixLift 430404
  have htrace : WordTrace (prefixWord ++ tailWord_430404) baseStart_430404 baseEnd_430404 := by
    simpa [prefixWord, tailWord_430404, baseEnd_430404] using wordTrace_append hprefix tailTrace_430404
  have hstable : (prefixWord ++ tailWord_430404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430404).length < 2 ^ (prefixWord ++ tailWord_430404).sum := by decide
  have hdescent : baseEnd_430404 < baseStart_430404 := by decide
  rcases family_descends (prefixWord ++ tailWord_430404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430488 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_430488 : Nat := 118140960795 + 430488 * 2 ^ 59
def prefixEnd_430488 : Nat := 4983230072969 + 3 ^ 40 * 430488 * 2
def baseEnd_430488 : Nat := 196486453326948397706869

theorem tailTrace_430488 : CollatzResearch.WordTrace tailWord_430488 prefixEnd_430488 196486453326948397706869 := by
  unfold tailWord_430488
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850593632211486171082059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10467458176281981561442745 7850593632211486171082059)
  ·
    refine ⟨11775890448317229256623089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850593632211486171082059 11775890448317229256623089)
    ·
      refine ⟨8831917836237921942467317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11775890448317229256623089 8831917836237921942467317)
      ·
        refine ⟨827992297147305182106311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8831917836237921942467317 827992297147305182106311)
        ·
          refine ⟨1241988445720957773159467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827992297147305182106311 1241988445720957773159467)
          ·
            refine ⟨1862982668581436659739201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241988445720957773159467 1862982668581436659739201)
            ·
              refine ⟨1397237001436077494804401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862982668581436659739201 1397237001436077494804401)
              ·
                refine ⟨1047927751077058121103301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397237001436077494804401 1047927751077058121103301)
                ·
                  refine ⟨196486453326948397706869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047927751077058121103301 196486453326948397706869)
                  ·
                    rfl

theorem cell20_430488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_430488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430488 prefixEnd_430488 := by exact prefixLift 430488
  have htrace : WordTrace (prefixWord ++ tailWord_430488) baseStart_430488 baseEnd_430488 := by
    simpa [prefixWord, tailWord_430488, baseEnd_430488] using wordTrace_append hprefix tailTrace_430488
  have hstable : (prefixWord ++ tailWord_430488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430488).length < 2 ^ (prefixWord ++ tailWord_430488).sum := by decide
  have hdescent : baseEnd_430488 < baseStart_430488 := by decide
  rcases family_descends (prefixWord ++ tailWord_430488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430526 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_430526 : Nat := 118140960795 + 430526 * 2 ^ 59
def prefixEnd_430526 : Nat := 4983230072969 + 3 ^ 40 * 430526 * 2
def baseEnd_430526 : Nat := 196503797562389154440047

theorem tailTrace_430526 : CollatzResearch.WordTrace tailWord_430526 prefixEnd_430526 196503797562389154440047 := by
  unfold tailWord_430526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962821654785663104005929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10468382158856869888031621 1962821654785663104005929)
  ·
    refine ⟨1472116241089247328004447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1962821654785663104005929 1472116241089247328004447)
    ·
      refine ⟨2208174361633870992006671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472116241089247328004447 2208174361633870992006671)
      ·
        refine ⟨3312261542450806488010007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208174361633870992006671 3312261542450806488010007)
        ·
          refine ⟨4968392313676209732015011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312261542450806488010007 4968392313676209732015011)
          ·
            refine ⟨7452588470514314598022517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968392313676209732015011 7452588470514314598022517)
            ·
              refine ⟨698680169110716993564611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7452588470514314598022517 698680169110716993564611)
              ·
                refine ⟨1048020253666075490346917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698680169110716993564611 1048020253666075490346917)
                ·
                  refine ⟨196503797562389154440047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048020253666075490346917 196503797562389154440047)
                  ·
                    rfl

theorem cell20_430526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_430526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430526 prefixEnd_430526 := by exact prefixLift 430526
  have htrace : WordTrace (prefixWord ++ tailWord_430526) baseStart_430526 baseEnd_430526 := by
    simpa [prefixWord, tailWord_430526, baseEnd_430526] using wordTrace_append hprefix tailTrace_430526
  have hstable : (prefixWord ++ tailWord_430526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430526).length < 2 ^ (prefixWord ++ tailWord_430526).sum := by decide
  have hdescent : baseEnd_430526 < baseStart_430526 := by decide
  rcases family_descends (prefixWord ++ tailWord_430526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430532 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_430532 : Nat := 118140960795 + 430532 * 2 ^ 59
def prefixEnd_430532 : Nat := 4983230072969 + 3 ^ 40 * 430532 * 2
def baseEnd_430532 : Nat := 196506536125879800240023

theorem tailTrace_430532 : CollatzResearch.WordTrace tailWord_430532 prefixEnd_430532 196506536125879800240023 := by
  unfold tailWord_430532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851396038131783928382925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10468528050842378571177233 7851396038131783928382925)
  ·
    refine ⟨2944273514299418973143597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7851396038131783928382925 2944273514299418973143597)
    ·
      refine ⟨1104102567862282114928849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2944273514299418973143597 1104102567862282114928849)
      ·
        refine ⟨828076925896711586196637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104102567862282114928849 828076925896711586196637)
        ·
          refine ⟨310528847211266844823739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828076925896711586196637 310528847211266844823739)
          ·
            refine ⟨465793270816900267235609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310528847211266844823739 465793270816900267235609)
            ·
              refine ⟨349344953112675200426707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465793270816900267235609 349344953112675200426707)
              ·
                refine ⟨524017429669012800640061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349344953112675200426707 524017429669012800640061)
                ·
                  refine ⟨196506536125879800240023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524017429669012800640061 196506536125879800240023)
                  ·
                    rfl

theorem cell20_430532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_430532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430532 prefixEnd_430532 := by exact prefixLift 430532
  have htrace : WordTrace (prefixWord ++ tailWord_430532) baseStart_430532 baseEnd_430532 := by
    simpa [prefixWord, tailWord_430532, baseEnd_430532] using wordTrace_append hprefix tailTrace_430532
  have hstable : (prefixWord ++ tailWord_430532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430532).length < 2 ^ (prefixWord ++ tailWord_430532).sum := by decide
  have hdescent : baseEnd_430532 < baseStart_430532 := by decide
  rcases family_descends (prefixWord ++ tailWord_430532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430536 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_430536 : Nat := 118140960795 + 430536 * 2 ^ 59
def prefixEnd_430536 : Nat := 4983230072969 + 3 ^ 40 * 430536 * 2
def baseEnd_430536 : Nat := 196508361834873564106673

theorem tailTrace_430536 : CollatzResearch.WordTrace tailWord_430536 prefixEnd_430536 196508361834873564106673 := by
  unfold tailWord_430536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851468984124538269955731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10468625312166051026607641 7851468984124538269955731)
  ·
    refine ⟨11777203476186807404933597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7851468984124538269955731 11777203476186807404933597)
    ·
      refine ⟨4416451303570052776850099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11777203476186807404933597 4416451303570052776850099)
      ·
        refine ⟨6624676955355079165275149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416451303570052776850099 6624676955355079165275149)
        ·
          refine ⟨2484253858258154686978181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6624676955355079165275149 2484253858258154686978181)
          ·
            refine ⟨465797598423404003808409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2484253858258154686978181 465797598423404003808409)
            ·
              refine ⟨349348198817553002856307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465797598423404003808409 349348198817553002856307)
              ·
                refine ⟨524022298226329504284461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349348198817553002856307 524022298226329504284461)
                ·
                  refine ⟨196508361834873564106673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524022298226329504284461 196508361834873564106673)
                  ·
                    rfl

theorem cell20_430536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_430536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430536 prefixEnd_430536 := by exact prefixLift 430536
  have htrace : WordTrace (prefixWord ++ tailWord_430536) baseStart_430536 baseEnd_430536 := by
    simpa [prefixWord, tailWord_430536, baseEnd_430536] using wordTrace_append hprefix tailTrace_430536
  have hstable : (prefixWord ++ tailWord_430536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430536).length < 2 ^ (prefixWord ++ tailWord_430536).sum := by decide
  have hdescent : baseEnd_430536 < baseStart_430536 := by decide
  rcases family_descends (prefixWord ++ tailWord_430536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430554 : List Nat := [3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_430554 : Nat := 118140960795 + 430554 * 2 ^ 59
def prefixEnd_430554 : Nat := 4983230072969 + 3 ^ 40 * 430554 * 2
def baseEnd_430554 : Nat := 65505525841781833835533

theorem tailTrace_430554 : CollatzResearch.WordTrace tailWord_430554 prefixEnd_430554 65505525841781833835533 := by
  unfold tailWord_430554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925898620545966403516679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10469062988122577076044477 3925898620545966403516679)
  ·
    refine ⟨5888847930818949605275019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3925898620545966403516679 5888847930818949605275019)
    ·
      refine ⟨8833271896228424407912529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5888847930818949605275019 8833271896228424407912529)
      ·
        refine ⟨6624953922171318305934397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8833271896228424407912529 6624953922171318305934397)
        ·
          refine ⟨2484357720814244364725399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6624953922171318305934397 2484357720814244364725399)
          ·
            refine ⟨3726536581221366547088099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484357720814244364725399 3726536581221366547088099)
            ·
              refine ⟨5589804871832049820632149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726536581221366547088099 5589804871832049820632149)
              ·
                refine ⟨65505525841781833835533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5589804871832049820632149 65505525841781833835533)
                ·
                  rfl

theorem cell20_430554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_430554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430554 prefixEnd_430554 := by exact prefixLift 430554
  have htrace : WordTrace (prefixWord ++ tailWord_430554) baseStart_430554 baseEnd_430554 := by
    simpa [prefixWord, tailWord_430554, baseEnd_430554] using wordTrace_append hprefix tailTrace_430554
  have hstable : (prefixWord ++ tailWord_430554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430554).length < 2 ^ (prefixWord ++ tailWord_430554).sum := by decide
  have hdescent : baseEnd_430554 < baseStart_430554 := by decide
  rcases family_descends (prefixWord ++ tailWord_430554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430598 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_430598 : Nat := 118140960795 + 430598 * 2 ^ 59
def prefixEnd_430598 : Nat := 4983230072969 + 3 ^ 40 * 430598 * 2
def baseEnd_430598 : Nat := 196536660324276904039753

theorem tailTrace_430598 : CollatzResearch.WordTrace tailWord_430598 prefixEnd_430598 196536660324276904039753 := by
  unfold tailWord_430598
  simp only [CollatzResearch.WordTrace]
  refine ⟨490787477938264410270889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10470132862682974085778965 490787477938264410270889)
  ·
    refine ⟨368090608453698307703167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 490787477938264410270889 368090608453698307703167)
    ·
      refine ⟨552135912680547461554751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368090608453698307703167 552135912680547461554751)
      ·
        refine ⟨828203869020821192332127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552135912680547461554751 828203869020821192332127)
        ·
          refine ⟨1242305803531231788498191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828203869020821192332127 1242305803531231788498191)
          ·
            refine ⟨1863458705296847682747287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242305803531231788498191 1863458705296847682747287)
            ·
              refine ⟨2795188057945271524120931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863458705296847682747287 2795188057945271524120931)
              ·
                refine ⟨4192782086917907286181397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795188057945271524120931 4192782086917907286181397)
                ·
                  refine ⟨196536660324276904039753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4192782086917907286181397 196536660324276904039753)
                  ·
                    rfl

theorem cell20_430598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_430598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430598 prefixEnd_430598 := by exact prefixLift 430598
  have htrace : WordTrace (prefixWord ++ tailWord_430598) baseStart_430598 baseEnd_430598 := by
    simpa [prefixWord, tailWord_430598, baseEnd_430598] using wordTrace_append hprefix tailTrace_430598
  have hstable : (prefixWord ++ tailWord_430598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430598).length < 2 ^ (prefixWord ++ tailWord_430598).sum := by decide
  have hdescent : baseEnd_430598 < baseStart_430598 := by decide
  rcases family_descends (prefixWord ++ tailWord_430598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430640 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_430640 : Nat := 118140960795 + 430640 * 2 ^ 59
def prefixEnd_430640 : Nat := 4983230072969 + 3 ^ 40 * 430640 * 2
def baseEnd_430640 : Nat := 196555830268711424639581

theorem tailTrace_430640 : CollatzResearch.WordTrace tailWord_430640 prefixEnd_430640 196555830268711424639581 := by
  unfold tailWord_430640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853365579936151150848687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10471154106581534867798249 7853365579936151150848687)
  ·
    refine ⟨11780048369904226726273031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853365579936151150848687 11780048369904226726273031)
    ·
      refine ⟨17670072554856340089409547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11780048369904226726273031 17670072554856340089409547)
      ·
        refine ⟨26505108832284510134114321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17670072554856340089409547 26505108832284510134114321)
        ·
          refine ⟨19878831624213382600585741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26505108832284510134114321 19878831624213382600585741)
          ·
            refine ⟨7454561859080018475219653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19878831624213382600585741 7454561859080018475219653)
            ·
              refine ⟨1397730348577503464103685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7454561859080018475219653 1397730348577503464103685)
              ·
                refine ⟨262074440358281899519441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1397730348577503464103685 262074440358281899519441)
                ·
                  refine ⟨196555830268711424639581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262074440358281899519441 196555830268711424639581)
                  ·
                    rfl

theorem cell20_430640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_430640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430640 prefixEnd_430640 := by exact prefixLift 430640
  have htrace : WordTrace (prefixWord ++ tailWord_430640) baseStart_430640 baseEnd_430640 := by
    simpa [prefixWord, tailWord_430640, baseEnd_430640] using wordTrace_append hprefix tailTrace_430640
  have hstable : (prefixWord ++ tailWord_430640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430640).length < 2 ^ (prefixWord ++ tailWord_430640).sum := by decide
  have hdescent : baseEnd_430640 < baseStart_430640 := by decide
  rcases family_descends (prefixWord ++ tailWord_430640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430661 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_430661 : Nat := 118140960795 + 430661 * 2 ^ 59
def prefixEnd_430661 : Nat := 4983230072969 + 3 ^ 40 * 430661 * 2
def baseEnd_430661 : Nat := 196565415240928684939495

theorem tailTrace_430661 : CollatzResearch.WordTrace tailWord_430661 prefixEnd_430661 196565415240928684939495 := by
  unfold tailWord_430661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707497092796222888211837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10471664728530815258807891 15707497092796222888211837)
  ·
    refine ⟨5890311409798583583079439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15707497092796222888211837 5890311409798583583079439)
    ·
      refine ⟨8835467114697875374619159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890311409798583583079439 8835467114697875374619159)
      ·
        refine ⟨13253200672046813061928739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835467114697875374619159 13253200672046813061928739)
        ·
          refine ⟨19879801008070219592893109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13253200672046813061928739 19879801008070219592893109)
          ·
            refine ⟨1863731344506583086833729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19879801008070219592893109 1863731344506583086833729)
            ·
              refine ⟨1397798508379937315125297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863731344506583086833729 1397798508379937315125297)
              ·
                refine ⟨1048348881284952986343973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397798508379937315125297 1048348881284952986343973)
                ·
                  refine ⟨196565415240928684939495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048348881284952986343973 196565415240928684939495)
                  ·
                    rfl

theorem cell20_430661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_430661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430661 prefixEnd_430661 := by exact prefixLift 430661
  have htrace : WordTrace (prefixWord ++ tailWord_430661) baseStart_430661 baseEnd_430661 := by
    simpa [prefixWord, tailWord_430661, baseEnd_430661] using wordTrace_append hprefix tailTrace_430661
  have hstable : (prefixWord ++ tailWord_430661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430661).length < 2 ^ (prefixWord ++ tailWord_430661).sum := by decide
  have hdescent : baseEnd_430661 < baseStart_430661 := by decide
  rcases family_descends (prefixWord ++ tailWord_430661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430668 : List Nat := [2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_430668 : Nat := 118140960795 + 430668 * 2 ^ 59
def prefixEnd_430668 : Nat := 4983230072969 + 3 ^ 40 * 430668 * 2
def baseEnd_430668 : Nat := 65522870077222590568711

theorem tailTrace_430668 : CollatzResearch.WordTrace tailWord_430668 prefixEnd_430668 65522870077222590568711 := by
  unfold tailWord_430668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853876201885431541858329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10471834935847242055811105 7853876201885431541858329)
  ·
    refine ⟨5890407151414073656393747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7853876201885431541858329 5890407151414073656393747)
    ·
      refine ⟨8835610727121110484590621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890407151414073656393747 8835610727121110484590621)
      ·
        refine ⟨3313354022670416431721483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8835610727121110484590621 3313354022670416431721483)
        ·
          refine ⟨4970031034005624647582225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313354022670416431721483 4970031034005624647582225)
          ·
            refine ⟨3727523275504218485686669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970031034005624647582225 3727523275504218485686669)
            ·
              refine ⟨1397821228314081932132501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3727523275504218485686669 1397821228314081932132501)
              ·
                refine ⟨65522870077222590568711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1397821228314081932132501 65522870077222590568711)
                ·
                  rfl

theorem cell20_430668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_430668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430668 prefixEnd_430668 := by exact prefixLift 430668
  have htrace : WordTrace (prefixWord ++ tailWord_430668) baseStart_430668 baseEnd_430668 := by
    simpa [prefixWord, tailWord_430668, baseEnd_430668] using wordTrace_append hprefix tailTrace_430668
  have hstable : (prefixWord ++ tailWord_430668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430668).length < 2 ^ (prefixWord ++ tailWord_430668).sum := by decide
  have hdescent : baseEnd_430668 < baseStart_430668 := by decide
  rcases family_descends (prefixWord ++ tailWord_430668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430692 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_430692 : Nat := 118140960795 + 430692 * 2 ^ 59
def prefixEnd_430692 : Nat := 4983230072969 + 3 ^ 40 * 430692 * 2
def baseEnd_430692 : Nat := 196579564485630354906035

theorem tailTrace_430692 : CollatzResearch.WordTrace tailWord_430692 prefixEnd_430692 196579564485630354906035 := by
  unfold tailWord_430692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854313877841957591295165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10472418503789276788393553 7854313877841957591295165)
  ·
    refine ⟨2945367704190734096735687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7854313877841957591295165 2945367704190734096735687)
    ·
      refine ⟨4418051556286101145103531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945367704190734096735687 4418051556286101145103531)
      ·
        refine ⟨6627077334429151717655297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418051556286101145103531 6627077334429151717655297)
        ·
          refine ⟨4970308000821863788241473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6627077334429151717655297 4970308000821863788241473)
          ·
            refine ⟨3727731000616397841181105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970308000821863788241473 3727731000616397841181105)
            ·
              refine ⟨2795798250462298380885829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727731000616397841181105 2795798250462298380885829)
              ·
                refine ⟨524212171961680946416093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2795798250462298380885829 524212171961680946416093)
                ·
                  refine ⟨196579564485630354906035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524212171961680946416093 196579564485630354906035)
                  ·
                    rfl

theorem cell20_430692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_430692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430692 prefixEnd_430692 := by exact prefixLift 430692
  have htrace : WordTrace (prefixWord ++ tailWord_430692) baseStart_430692 baseEnd_430692 := by
    simpa [prefixWord, tailWord_430692, baseEnd_430692] using wordTrace_append hprefix tailTrace_430692
  have hstable : (prefixWord ++ tailWord_430692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430692).length < 2 ^ (prefixWord ++ tailWord_430692).sum := by decide
  have hdescent : baseEnd_430692 < baseStart_430692 := by decide
  rcases family_descends (prefixWord ++ tailWord_430692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430746 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_430746 : Nat := 118140960795 + 430746 * 2 ^ 59
def prefixEnd_430746 : Nat := 4983230072969 + 3 ^ 40 * 430746 * 2
def baseEnd_430746 : Nat := 196604211557046167105815

theorem tailTrace_430746 : CollatzResearch.WordTrace tailWord_430746 prefixEnd_430746 196604211557046167105815 := by
  unfold tailWord_430746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927649324372070601264023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10473731531658854936704061 3927649324372070601264023)
  ·
    refine ⟨5891473986558105901896035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3927649324372070601264023 5891473986558105901896035)
    ·
      refine ⟨8837210979837158852844053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891473986558105901896035 8837210979837158852844053)
      ·
        refine ⟨414244264679866821227065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8837210979837158852844053 414244264679866821227065)
        ·
          refine ⟨310683198509900115920299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414244264679866821227065 310683198509900115920299)
          ·
            refine ⟨466024797764850173880449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310683198509900115920299 466024797764850173880449)
            ·
              refine ⟨349518598323637630410337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466024797764850173880449 349518598323637630410337)
              ·
                refine ⟨262138948742728222807753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349518598323637630410337 262138948742728222807753)
                ·
                  refine ⟨196604211557046167105815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262138948742728222807753 196604211557046167105815)
                  ·
                    rfl

theorem cell20_430746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_430746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430746 prefixEnd_430746 := by exact prefixLift 430746
  have htrace : WordTrace (prefixWord ++ tailWord_430746) baseStart_430746 baseEnd_430746 := by
    simpa [prefixWord, tailWord_430746, baseEnd_430746] using wordTrace_append hprefix tailTrace_430746
  have hstable : (prefixWord ++ tailWord_430746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430746).length < 2 ^ (prefixWord ++ tailWord_430746).sum := by decide
  have hdescent : baseEnd_430746 < baseStart_430746 := by decide
  rcases family_descends (prefixWord ++ tailWord_430746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430792 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_430792 : Nat := 118140960795 + 430792 * 2 ^ 59
def prefixEnd_430792 : Nat := 4983230072969 + 3 ^ 40 * 430792 * 2
def baseEnd_430792 : Nat := 196625207210474451572293

theorem tailTrace_430792 : CollatzResearch.WordTrace tailWord_430792 prefixEnd_430792 196625207210474451572293 := by
  unfold tailWord_430792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7856137527660816130615315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10474850036881088174153753 7856137527660816130615315)
  ·
    refine ⟨11784206291491224195922973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7856137527660816130615315 11784206291491224195922973)
    ·
      refine ⟨4419077359309209073471115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11784206291491224195922973 4419077359309209073471115)
      ·
        refine ⟨6628616038963813610206673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419077359309209073471115 6628616038963813610206673)
        ·
          refine ⟨4971462029222860207655005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6628616038963813610206673 4971462029222860207655005)
          ·
            refine ⟨1864298260958572577870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4971462029222860207655005 1864298260958572577870627)
            ·
              refine ⟨2796447391437858866805941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864298260958572577870627 2796447391437858866805941)
              ·
                refine ⟨262166942947299268763057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2796447391437858866805941 262166942947299268763057)
                ·
                  refine ⟨196625207210474451572293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262166942947299268763057 196625207210474451572293)
                  ·
                    rfl

theorem cell20_430792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_430792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430792 prefixEnd_430792 := by exact prefixLift 430792
  have htrace : WordTrace (prefixWord ++ tailWord_430792) baseStart_430792 baseEnd_430792 := by
    simpa [prefixWord, tailWord_430792, baseEnd_430792] using wordTrace_append hprefix tailTrace_430792
  have hstable : (prefixWord ++ tailWord_430792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430792).length < 2 ^ (prefixWord ++ tailWord_430792).sum := by decide
  have hdescent : baseEnd_430792 < baseStart_430792 := by decide
  rcases family_descends (prefixWord ++ tailWord_430792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430802 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_430802 : Nat := 118140960795 + 430802 * 2 ^ 59
def prefixEnd_430802 : Nat := 4983230072969 + 3 ^ 40 * 430802 * 2
def baseEnd_430802 : Nat := 196629771482958861238919

theorem tailTrace_430802 : CollatzResearch.WordTrace tailWord_430802 prefixEnd_430802 196629771482958861238919 := by
  unfold tailWord_430802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928159946321350992273665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10475093190190269312729773 3928159946321350992273665)
  ·
    refine ⟨2946119959741013244205249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3928159946321350992273665 2946119959741013244205249)
    ·
      refine ⟨2209589969805759933153937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2946119959741013244205249 2209589969805759933153937)
      ·
        refine ⟨1657192477354319949865453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2209589969805759933153937 1657192477354319949865453)
        ·
          refine ⟨621447179007869981199545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1657192477354319949865453 621447179007869981199545)
          ·
            refine ⟨466085384255902485899659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621447179007869981199545 466085384255902485899659)
            ·
              refine ⟨699128076383853728849489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466085384255902485899659 699128076383853728849489)
              ·
                refine ⟨524346057287890296637117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699128076383853728849489 524346057287890296637117)
                ·
                  refine ⟨196629771482958861238919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524346057287890296637117 196629771482958861238919)
                  ·
                    rfl

theorem cell20_430802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_430802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430802 prefixEnd_430802 := by exact prefixLift 430802
  have htrace : WordTrace (prefixWord ++ tailWord_430802) baseStart_430802 baseEnd_430802 := by
    simpa [prefixWord, tailWord_430802, baseEnd_430802] using wordTrace_append hprefix tailTrace_430802
  have hstable : (prefixWord ++ tailWord_430802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430802).length < 2 ^ (prefixWord ++ tailWord_430802).sum := by decide
  have hdescent : baseEnd_430802 < baseStart_430802 := by decide
  rcases family_descends (prefixWord ++ tailWord_430802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430865 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_430865 : Nat := 118140960795 + 430865 * 2 ^ 59
def prefixEnd_430865 : Nat := 4983230072969 + 3 ^ 40 * 430865 * 2
def baseEnd_430865 : Nat := 196658526399610642138661

theorem tailTrace_430865 : CollatzResearch.WordTrace tailWord_430865 prefixEnd_430865 196658526399610642138661 := by
  unfold tailWord_430865
  simp only [CollatzResearch.WordTrace]
  refine ⟨15714937584057165728638049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10476625056038110485758699 15714937584057165728638049)
  ·
    refine ⟨11786203188042874296478537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15714937584057165728638049 11786203188042874296478537)
    ·
      refine ⟨8839652391032155722358903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786203188042874296478537 8839652391032155722358903)
      ·
        refine ⟨13259478586548233583538355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839652391032155722358903 13259478586548233583538355)
        ·
          refine ⟨19889217879822350375307533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13259478586548233583538355 19889217879822350375307533)
          ·
            refine ⟨7458456704933381390740325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19889217879822350375307533 7458456704933381390740325)
            ·
              refine ⟨1398460632175009010763811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7458456704933381390740325 1398460632175009010763811)
              ·
                refine ⟨2097690948262513516145717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398460632175009010763811 2097690948262513516145717)
                ·
                  refine ⟨196658526399610642138661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097690948262513516145717 196658526399610642138661)
                  ·
                    rfl

theorem cell20_430865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_430865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430865 prefixEnd_430865 := by exact prefixLift 430865
  have htrace : WordTrace (prefixWord ++ tailWord_430865) baseStart_430865 baseEnd_430865 := by
    simpa [prefixWord, tailWord_430865, baseEnd_430865] using wordTrace_append hprefix tailTrace_430865
  have hstable : (prefixWord ++ tailWord_430865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430865).length < 2 ^ (prefixWord ++ tailWord_430865).sum := by decide
  have hdescent : baseEnd_430865 < baseStart_430865 := by decide
  rcases family_descends (prefixWord ++ tailWord_430865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430913 : List Nat := [1, 2, 5, 3, 1, 8]
def baseStart_430913 : Nat := 118140960795 + 430913 * 2 ^ 59
def prefixEnd_430913 : Nat := 4983230072969 + 3 ^ 40 * 430913 * 2
def baseEnd_430913 : Nat := 7284460552130955871795

theorem tailTrace_430913 : CollatzResearch.WordTrace tailWord_430913 prefixEnd_430913 7284460552130955871795 := by
  unfold tailWord_430913
  simp only [CollatzResearch.WordTrace]
  refine ⟨15716688287883269926385393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10477792191922179950923595 15716688287883269926385393)
  ·
    refine ⟨11787516215912452444789045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15716688287883269926385393 11787516215912452444789045)
    ·
      refine ⟨1105079645241792416698973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11787516215912452444789045 1105079645241792416698973)
      ·
        refine ⟨414404866965672156262115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1105079645241792416698973 414404866965672156262115)
        ·
          refine ⟨621607300448508234393173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414404866965672156262115 621607300448508234393173)
          ·
            refine ⟨7284460552130955871795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 621607300448508234393173 7284460552130955871795)
            ·
              rfl

theorem cell20_430913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 8].length) (baseStart_430913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430913 prefixEnd_430913 := by exact prefixLift 430913
  have htrace : WordTrace (prefixWord ++ tailWord_430913) baseStart_430913 baseEnd_430913 := by
    simpa [prefixWord, tailWord_430913, baseEnd_430913] using wordTrace_append hprefix tailTrace_430913
  have hstable : (prefixWord ++ tailWord_430913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430913).length < 2 ^ (prefixWord ++ tailWord_430913).sum := by decide
  have hdescent : baseEnd_430913 < baseStart_430913 := by decide
  rcases family_descends (prefixWord ++ tailWord_430913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430920 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_430920 : Nat := 118140960795 + 430920 * 2 ^ 59
def prefixEnd_430920 : Nat := 4983230072969 + 3 ^ 40 * 430920 * 2
def baseEnd_430920 : Nat := 196683629898274895305103

theorem tailTrace_430920 : CollatzResearch.WordTrace tailWord_430920 prefixEnd_430920 196683629898274895305103 := by
  unfold tailWord_430920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858471799428955060945107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10477962399238606747926809 7858471799428955060945107)
  ·
    refine ⟨11787707699143432591417661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7858471799428955060945107 11787707699143432591417661)
    ·
      refine ⟨4420390387178787221781623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11787707699143432591417661 4420390387178787221781623)
      ·
        refine ⟨6630585580768180832672435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420390387178787221781623 6630585580768180832672435)
        ·
          refine ⟨9945878371152271249008653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630585580768180832672435 9945878371152271249008653)
          ·
            refine ⟨3729704389182101718378245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9945878371152271249008653 3729704389182101718378245)
            ·
              refine ⟨699319572971644072195921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3729704389182101718378245 699319572971644072195921)
              ·
                refine ⟨524489679728733054146941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699319572971644072195921 524489679728733054146941)
                ·
                  refine ⟨196683629898274895305103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524489679728733054146941 196683629898274895305103)
                  ·
                    rfl

theorem cell20_430920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_430920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430920 prefixEnd_430920 := by exact prefixLift 430920
  have htrace : WordTrace (prefixWord ++ tailWord_430920) baseStart_430920 baseEnd_430920 := by
    simpa [prefixWord, tailWord_430920, baseEnd_430920] using wordTrace_append hprefix tailTrace_430920
  have hstable : (prefixWord ++ tailWord_430920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430920).length < 2 ^ (prefixWord ++ tailWord_430920).sum := by decide
  have hdescent : baseEnd_430920 < baseStart_430920 := by decide
  rcases family_descends (prefixWord ++ tailWord_430920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430951 : List Nat := [1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_430951 : Nat := 118140960795 + 430951 * 2 ^ 59
def prefixEnd_430951 : Nat := 4983230072969 + 3 ^ 40 * 430951 * 2
def baseEnd_430951 : Nat := 65565926380992188423881

theorem tailTrace_430951 : CollatzResearch.WordTrace tailWord_430951 prefixEnd_430951 65565926380992188423881 := by
  unfold tailWord_430951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718074261745602416268707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10478716174497068277512471 15718074261745602416268707)
  ·
    refine ⟨23577111392618403624403061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15718074261745602416268707 23577111392618403624403061)
    ·
      refine ⟨2210354193057975339787787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23577111392618403624403061 2210354193057975339787787)
      ·
        refine ⟨3315531289586963009681681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210354193057975339787787 3315531289586963009681681)
        ·
          refine ⟨2486648467190222257261261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3315531289586963009681681 2486648467190222257261261)
          ·
            refine ⟨932493175196333346472973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2486648467190222257261261 932493175196333346472973)
            ·
              refine ⟨349684940698625004927365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932493175196333346472973 349684940698625004927365)
              ·
                refine ⟨65565926380992188423881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349684940698625004927365 65565926380992188423881)
                ·
                  rfl

theorem cell20_430951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_430951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430951 prefixEnd_430951 := by exact prefixLift 430951
  have htrace : WordTrace (prefixWord ++ tailWord_430951) baseStart_430951 baseEnd_430951 := by
    simpa [prefixWord, tailWord_430951, baseEnd_430951] using wordTrace_append hprefix tailTrace_430951
  have hstable : (prefixWord ++ tailWord_430951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430951).length < 2 ^ (prefixWord ++ tailWord_430951).sum := by decide
  have hdescent : baseEnd_430951 < baseStart_430951 := by decide
  rcases family_descends (prefixWord ++ tailWord_430951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430955 : List Nat := [1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_430955 : Nat := 118140960795 + 430955 * 2 ^ 59
def prefixEnd_430955 : Nat := 4983230072969 + 3 ^ 40 * 430955 * 2
def baseEnd_430955 : Nat := 65566534950656776379431

theorem tailTrace_430955 : CollatzResearch.WordTrace tailWord_430955 prefixEnd_430955 65566534950656776379431 := by
  unfold tailWord_430955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718220153731111099414319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10478813435820740732942879 15718220153731111099414319)
  ·
    refine ⟨23577330230596666649121479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15718220153731111099414319 23577330230596666649121479)
    ·
      refine ⟨35365995345894999973682219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23577330230596666649121479 35365995345894999973682219)
      ·
        refine ⟨53048993018842499960523329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35365995345894999973682219 53048993018842499960523329)
        ·
          refine ⟨39786744764131874970392497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53048993018842499960523329 39786744764131874970392497)
          ·
            refine ⟨29840058573098906227794373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39786744764131874970392497 29840058573098906227794373)
            ·
              refine ⟨5595010982456044917711445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29840058573098906227794373 5595010982456044917711445)
              ·
                refine ⟨65566534950656776379431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5595010982456044917711445 65566534950656776379431)
                ·
                  rfl

theorem cell20_430955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_430955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430955 prefixEnd_430955 := by exact prefixLift 430955
  have htrace : WordTrace (prefixWord ++ tailWord_430955) baseStart_430955 baseEnd_430955 := by
    simpa [prefixWord, tailWord_430955, baseEnd_430955] using wordTrace_append hprefix tailTrace_430955
  have hstable : (prefixWord ++ tailWord_430955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430955).length < 2 ^ (prefixWord ++ tailWord_430955).sum := by decide
  have hdescent : baseEnd_430955 < baseStart_430955 := by decide
  rcases family_descends (prefixWord ++ tailWord_430955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430978 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_430978 : Nat := 118140960795 + 430978 * 2 ^ 59
def prefixEnd_430978 : Nat := 4983230072969 + 3 ^ 40 * 430978 * 2
def baseEnd_430978 : Nat := 196710102678684471371533

theorem tailTrace_430978 : CollatzResearch.WordTrace tailWord_430978 prefixEnd_430978 196710102678684471371533 := by
  unfold tailWord_430978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929764758161946506875397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10479372688431857351667725 3929764758161946506875397)
  ·
    refine ⟨736830892155364970039137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3929764758161946506875397 736830892155364970039137)
    ·
      refine ⟨552623169116523727529353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 736830892155364970039137 552623169116523727529353)
      ·
        refine ⟨414467376837392795647015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552623169116523727529353 414467376837392795647015)
        ·
          refine ⟨621701065256089193470523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414467376837392795647015 621701065256089193470523)
          ·
            refine ⟨932551597884133790205785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621701065256089193470523 932551597884133790205785)
            ·
              refine ⟨699413698413100342654339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932551597884133790205785 699413698413100342654339)
              ·
                refine ⟨1049120547619650513981509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699413698413100342654339 1049120547619650513981509)
                ·
                  refine ⟨196710102678684471371533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049120547619650513981509 196710102678684471371533)
                  ·
                    rfl

theorem cell20_430978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_430978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430978 prefixEnd_430978 := by exact prefixLift 430978
  have htrace : WordTrace (prefixWord ++ tailWord_430978) baseStart_430978 baseEnd_430978 := by
    simpa [prefixWord, tailWord_430978, baseEnd_430978] using wordTrace_append hprefix tailTrace_430978
  have hstable : (prefixWord ++ tailWord_430978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430978).length < 2 ^ (prefixWord ++ tailWord_430978).sum := by decide
  have hdescent : baseEnd_430978 < baseStart_430978 := by decide
  rcases family_descends (prefixWord ++ tailWord_430978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430979 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_430979 : Nat := 118140960795 + 430979 * 2 ^ 59
def prefixEnd_430979 : Nat := 4983230072969 + 3 ^ 40 * 430979 * 2
def baseEnd_430979 : Nat := 196710559105932912338195

theorem tailTrace_430979 : CollatzResearch.WordTrace tailWord_430979 prefixEnd_430979 196710559105932912338195 := by
  unfold tailWord_430979
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719095505644163198287991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10479397003762775465525327 15719095505644163198287991)
  ·
    refine ⟨23578643258466244797431987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15719095505644163198287991 23578643258466244797431987)
    ·
      refine ⟨35367964887699367196147981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23578643258466244797431987 35367964887699367196147981)
      ·
        refine ⟨13262986832887262698555493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35367964887699367196147981 13262986832887262698555493)
        ·
          refine ⟨2486810031166361755979155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13262986832887262698555493 2486810031166361755979155)
          ·
            refine ⟨3730215046749542633968733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486810031166361755979155 3730215046749542633968733)
            ·
              refine ⟨1398830642531078487738275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3730215046749542633968733 1398830642531078487738275)
              ·
                refine ⟨2098245963796617731607413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398830642531078487738275 2098245963796617731607413)
                ·
                  refine ⟨196710559105932912338195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098245963796617731607413 196710559105932912338195)
                  ·
                    rfl

theorem cell20_430979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_430979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430979 prefixEnd_430979 := by exact prefixLift 430979
  have htrace : WordTrace (prefixWord ++ tailWord_430979) baseStart_430979 baseEnd_430979 := by
    simpa [prefixWord, tailWord_430979, baseEnd_430979] using wordTrace_append hprefix tailTrace_430979
  have hstable : (prefixWord ++ tailWord_430979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430979).length < 2 ^ (prefixWord ++ tailWord_430979).sum := by decide
  have hdescent : baseEnd_430979 < baseStart_430979 := by decide
  rcases family_descends (prefixWord ++ tailWord_430979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430993 : List Nat := [1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_430993 : Nat := 118140960795 + 430993 * 2 ^ 59
def prefixEnd_430993 : Nat := 4983230072969 + 3 ^ 40 * 430993 * 2
def baseEnd_430993 : Nat := 65572316362470361957157

theorem tailTrace_430993 : CollatzResearch.WordTrace tailWord_430993 prefixEnd_430993 65572316362470361957157 := by
  unfold tailWord_430993
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719606127593443589297633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10479737418395629059531755 15719606127593443589297633)
  ·
    refine ⟨11789704595695082691973225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15719606127593443589297633 11789704595695082691973225)
    ·
      refine ⟨8842278446771312018979919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11789704595695082691973225 8842278446771312018979919)
      ·
        refine ⟨13263417670156968028469879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842278446771312018979919 13263417670156968028469879)
        ·
          refine ⟨19895126505235452042704819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263417670156968028469879 19895126505235452042704819)
          ·
            refine ⟨29842689757853178064057229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19895126505235452042704819 29842689757853178064057229)
            ·
              refine ⟨11191008659194941774021461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29842689757853178064057229 11191008659194941774021461)
              ·
                refine ⟨65572316362470361957157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11191008659194941774021461 65572316362470361957157)
                ·
                  rfl

theorem cell20_430993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_430993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_430993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_430993 prefixEnd_430993 := by exact prefixLift 430993
  have htrace : WordTrace (prefixWord ++ tailWord_430993) baseStart_430993 baseEnd_430993 := by
    simpa [prefixWord, tailWord_430993, baseEnd_430993] using wordTrace_append hprefix tailTrace_430993
  have hstable : (prefixWord ++ tailWord_430993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430993).length < 2 ^ (prefixWord ++ tailWord_430993).sum := by decide
  have hdescent : baseEnd_430993 < baseStart_430993 := by decide
  rcases family_descends (prefixWord ++ tailWord_430993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431031 : List Nat := [1, 1, 3, 1, 3, 1, 10]
def baseStart_431031 : Nat := 118140960795 + 431031 * 2 ^ 59
def prefixEnd_431031 : Nat := 4983230072969 + 3 ^ 40 * 431031 * 2
def baseEnd_431031 : Nat := 21859365924761315844961

theorem tailTrace_431031 : CollatzResearch.WordTrace tailWord_431031 prefixEnd_431031 21859365924761315844961 := by
  unfold tailWord_431031
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720992101455776079180947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10480661400970517386120631 15720992101455776079180947)
  ·
    refine ⟨23581488152183664118771421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15720992101455776079180947 23581488152183664118771421)
    ·
      refine ⟨8843058057068874044539283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23581488152183664118771421 8843058057068874044539283)
      ·
        refine ⟨13264587085603311066808925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8843058057068874044539283 13264587085603311066808925)
        ·
          refine ⟨4974220157101241650053347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13264587085603311066808925 4974220157101241650053347)
          ·
            refine ⟨7461330235651862475080021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974220157101241650053347 7461330235651862475080021)
            ·
              refine ⟨21859365924761315844961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7461330235651862475080021 21859365924761315844961)
              ·
                rfl

theorem cell20_431031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_431031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431031 prefixEnd_431031 := by exact prefixLift 431031
  have htrace : WordTrace (prefixWord ++ tailWord_431031) baseStart_431031 baseEnd_431031 := by
    simpa [prefixWord, tailWord_431031, baseEnd_431031] using wordTrace_append hprefix tailTrace_431031
  have hstable : (prefixWord ++ tailWord_431031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431031).length < 2 ^ (prefixWord ++ tailWord_431031).sum := by decide
  have hdescent : baseEnd_431031 < baseStart_431031 := by decide
  rcases family_descends (prefixWord ++ tailWord_431031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431037 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 4]
def baseStart_431037 : Nat := 118140960795 + 431037 * 2 ^ 59
def prefixEnd_431037 : Nat := 4983230072969 + 3 ^ 40 * 431037 * 2
def baseEnd_431037 : Nat := 196737031886342488404625

theorem tailTrace_431037 : CollatzResearch.WordTrace tailWord_431037 prefixEnd_431037 196737031886342488404625 := by
  unfold tailWord_431037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721210939434039103899365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10480807292956026069266243 15721210939434039103899365)
  ·
    refine ⟨2947727051143882331981131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15721210939434039103899365 2947727051143882331981131)
    ·
      refine ⟨4421590576715823497971697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947727051143882331981131 4421590576715823497971697)
      ·
        refine ⟨3316192932536867623478773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4421590576715823497971697 3316192932536867623478773)
        ·
          refine ⟨310893087425331339701135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3316192932536867623478773 310893087425331339701135)
          ·
            refine ⟨466339631137997009551703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310893087425331339701135 466339631137997009551703)
            ·
              refine ⟨699509446706995514327555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466339631137997009551703 699509446706995514327555)
              ·
                refine ⟨1049264170060493271491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699509446706995514327555 1049264170060493271491333)
                ·
                  refine ⟨196737031886342488404625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049264170060493271491333 196737031886342488404625)
                  ·
                    rfl

theorem cell20_431037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_431037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431037 prefixEnd_431037 := by exact prefixLift 431037
  have htrace : WordTrace (prefixWord ++ tailWord_431037) baseStart_431037 baseEnd_431037 := by
    simpa [prefixWord, tailWord_431037, baseEnd_431037] using wordTrace_append hprefix tailTrace_431037
  have hstable : (prefixWord ++ tailWord_431037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431037).length < 2 ^ (prefixWord ++ tailWord_431037).sum := by decide
  have hdescent : baseEnd_431037 < baseStart_431037 := by decide
  rcases family_descends (prefixWord ++ tailWord_431037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431044 : List Nat := [2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_431044 : Nat := 118140960795 + 431044 * 2 ^ 59
def prefixEnd_431044 : Nat := 4983230072969 + 3 ^ 40 * 431044 * 2
def baseEnd_431044 : Nat := 65580075625693858390421

theorem tailTrace_431044 : CollatzResearch.WordTrace tailWord_431044 prefixEnd_431044 65580075625693858390421 := by
  unfold tailWord_431044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860733125204339649702093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10480977500272452866269457 7860733125204339649702093)
  ·
    refine ⟨2947774921951627368638285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7860733125204339649702093 2947774921951627368638285)
    ·
      refine ⟨1105415595731860263239357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2947774921951627368638285 1105415595731860263239357)
      ·
        refine ⟨414530848399447598714759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1105415595731860263239357 414530848399447598714759)
        ·
          refine ⟨621796272599171398072139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414530848399447598714759 621796272599171398072139)
          ·
            refine ⟨932694408898757097108209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621796272599171398072139 932694408898757097108209)
            ·
              refine ⟨699520806674067822831157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932694408898757097108209 699520806674067822831157)
              ·
                refine ⟨65580075625693858390421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699520806674067822831157 65580075625693858390421)
                ·
                  rfl

theorem cell20_431044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_431044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431044 prefixEnd_431044 := by exact prefixLift 431044
  have htrace : WordTrace (prefixWord ++ tailWord_431044) baseStart_431044 baseEnd_431044 := by
    simpa [prefixWord, tailWord_431044, baseEnd_431044] using wordTrace_append hprefix tailTrace_431044
  have hstable : (prefixWord ++ tailWord_431044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431044).length < 2 ^ (prefixWord ++ tailWord_431044).sum := by decide
  have hdescent : baseEnd_431044 < baseStart_431044 := by decide
  rcases family_descends (prefixWord ++ tailWord_431044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431051 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 3]
def baseStart_431051 : Nat := 118140960795 + 431051 * 2 ^ 59
def prefixEnd_431051 : Nat := 4983230072969 + 3 ^ 40 * 431051 * 2
def baseEnd_431051 : Nat := 196743421867820661937901

theorem tailTrace_431051 : CollatzResearch.WordTrace tailWord_431051 prefixEnd_431051 196743421867820661937901 := by
  unfold tailWord_431051
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721721561383319494909007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10481147707588879663272671 15721721561383319494909007)
  ·
    refine ⟨23582582342074979242363511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15721721561383319494909007 23582582342074979242363511)
    ·
      refine ⟨35373873513112468863545267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23582582342074979242363511 35373873513112468863545267)
      ·
        refine ⟨53060810269668703295317901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35373873513112468863545267 53060810269668703295317901)
        ·
          refine ⟨19897803851125763735744213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53060810269668703295317901 19897803851125763735744213)
          ·
            refine ⟨466354777760760087556505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19897803851125763735744213 466354777760760087556505)
            ·
              refine ⟨349766083320570065667379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466354777760760087556505 349766083320570065667379)
              ·
                refine ⟨524649124980855098501069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349766083320570065667379 524649124980855098501069)
                ·
                  refine ⟨196743421867820661937901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524649124980855098501069 196743421867820661937901)
                  ·
                    rfl

theorem cell20_431051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_431051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431051 prefixEnd_431051 := by exact prefixLift 431051
  have htrace : WordTrace (prefixWord ++ tailWord_431051) baseStart_431051 baseEnd_431051 := by
    simpa [prefixWord, tailWord_431051, baseEnd_431051] using wordTrace_append hprefix tailTrace_431051
  have hstable : (prefixWord ++ tailWord_431051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431051).length < 2 ^ (prefixWord ++ tailWord_431051).sum := by decide
  have hdescent : baseEnd_431051 < baseStart_431051 := by decide
  rcases family_descends (prefixWord ++ tailWord_431051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431086 : List Nat := [4, 1, 2, 1, 4, 8]
def baseStart_431086 : Nat := 118140960795 + 431086 * 2 ^ 59
def prefixEnd_431086 : Nat := 4983230072969 + 3 ^ 40 * 431086 * 2
def baseEnd_431086 : Nat := 7287385067463559102633

theorem tailTrace_431086 : CollatzResearch.WordTrace tailWord_431086 prefixEnd_431086 7287385067463559102633 := by
  unfold tailWord_431086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965374764532065059054139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10481998744171013648288741 1965374764532065059054139)
  ·
    refine ⟨2948062146798097588581209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965374764532065059054139 2948062146798097588581209)
    ·
      refine ⟨2211046610098573191435907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2948062146798097588581209 2211046610098573191435907)
      ·
        refine ⟨3316569915147859787153861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211046610098573191435907 3316569915147859787153861)
        ·
          refine ⟨621856859090223710091349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3316569915147859787153861 621856859090223710091349)
          ·
            refine ⟨7287385067463559102633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 621856859090223710091349 7287385067463559102633)
            ·
              rfl

theorem cell20_431086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 8].length) (baseStart_431086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431086 prefixEnd_431086 := by exact prefixLift 431086
  have htrace : WordTrace (prefixWord ++ tailWord_431086) baseStart_431086 baseEnd_431086 := by
    simpa [prefixWord, tailWord_431086, baseEnd_431086] using wordTrace_append hprefix tailTrace_431086
  have hstable : (prefixWord ++ tailWord_431086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431086).length < 2 ^ (prefixWord ++ tailWord_431086).sum := by decide
  have hdescent : baseEnd_431086 < baseStart_431086 := by decide
  rcases family_descends (prefixWord ++ tailWord_431086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431165 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 3]
def baseStart_431165 : Nat := 118140960795 + 431165 * 2 ^ 59
def prefixEnd_431165 : Nat := 4983230072969 + 3 ^ 40 * 431165 * 2
def baseEnd_431165 : Nat := 196795454574142932137435

theorem tailTrace_431165 : CollatzResearch.WordTrace tailWord_431165 prefixEnd_431165 196795454574142932137435 := by
  unfold tailWord_431165
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725879482970316964558949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10483919655313544643039299 15725879482970316964558949)
  ·
    refine ⟨2948602403056934430854803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15725879482970316964558949 2948602403056934430854803)
    ·
      refine ⟨4422903604585401646282205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948602403056934430854803 4422903604585401646282205)
      ·
        refine ⟨1658588851719525617355827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4422903604585401646282205 1658588851719525617355827)
        ·
          refine ⟨2487883277579288426033741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658588851719525617355827 2487883277579288426033741)
          ·
            refine ⟨932956229092233159762653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2487883277579288426033741 932956229092233159762653)
            ·
              refine ⟨349858585909587434910995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932956229092233159762653 349858585909587434910995)
              ·
                refine ⟨524787878864381152366493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349858585909587434910995 524787878864381152366493)
                ·
                  refine ⟨196795454574142932137435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524787878864381152366493 196795454574142932137435)
                  ·
                    rfl

theorem cell20_431165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_431165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431165 prefixEnd_431165 := by exact prefixLift 431165
  have htrace : WordTrace (prefixWord ++ tailWord_431165) baseStart_431165 baseEnd_431165 := by
    simpa [prefixWord, tailWord_431165, baseEnd_431165] using wordTrace_append hprefix tailTrace_431165
  have hstable : (prefixWord ++ tailWord_431165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431165).length < 2 ^ (prefixWord ++ tailWord_431165).sum := by decide
  have hdescent : baseEnd_431165 < baseStart_431165 := by decide
  rcases family_descends (prefixWord ++ tailWord_431165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431176 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_431176 : Nat := 118140960795 + 431176 * 2 ^ 59
def prefixEnd_431176 : Nat := 4983230072969 + 3 ^ 40 * 431176 * 2
def baseEnd_431176 : Nat := 196800475273875782770723

theorem tailTrace_431176 : CollatzResearch.WordTrace tailWord_431176 prefixEnd_431176 196800475273875782770723 := by
  unfold tailWord_431176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863140342965232921604691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10484187123953643895472921 7863140342965232921604691)
  ·
    refine ⟨11794710514447849382407037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863140342965232921604691 11794710514447849382407037)
    ·
      refine ⟨4423016442917943518402639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11794710514447849382407037 4423016442917943518402639)
      ·
        refine ⟨6634524664376915277603959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423016442917943518402639 6634524664376915277603959)
        ·
          refine ⟨9951786996565372916405939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634524664376915277603959 9951786996565372916405939)
          ·
            refine ⟨14927680494848059374608909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951786996565372916405939 14927680494848059374608909)
            ·
              refine ⟨5597880185568022265478341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14927680494848059374608909 5597880185568022265478341)
              ·
                refine ⟨1049602534794004174777189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5597880185568022265478341 1049602534794004174777189)
                ·
                  refine ⟨196800475273875782770723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049602534794004174777189 196800475273875782770723)
                  ·
                    rfl

theorem cell20_431176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_431176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431176 prefixEnd_431176 := by exact prefixLift 431176
  have htrace : WordTrace (prefixWord ++ tailWord_431176) baseStart_431176 baseEnd_431176 := by
    simpa [prefixWord, tailWord_431176, baseEnd_431176] using wordTrace_append hprefix tailTrace_431176
  have hstable : (prefixWord ++ tailWord_431176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431176).length < 2 ^ (prefixWord ++ tailWord_431176).sum := by decide
  have hdescent : baseEnd_431176 < baseStart_431176 := by decide
  rcases family_descends (prefixWord ++ tailWord_431176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431193 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 2]
def baseStart_431193 : Nat := 118140960795 + 431193 * 2 ^ 59
def prefixEnd_431193 : Nat := 4983230072969 + 3 ^ 40 * 431193 * 2
def baseEnd_431193 : Nat := 196808234537099279203987

theorem tailTrace_431193 : CollatzResearch.WordTrace tailWord_431193 prefixEnd_431193 196808234537099279203987 := by
  unfold tailWord_431193
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726900726868877746578233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10484600484579251831052155 15726900726868877746578233)
  ·
    refine ⟨11795175545151658309933675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15726900726868877746578233 11795175545151658309933675)
    ·
      refine ⟨17692763317727487464900513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795175545151658309933675 17692763317727487464900513)
      ·
        refine ⟨13269572488295615598675385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17692763317727487464900513 13269572488295615598675385)
        ·
          refine ⟨9952179366221711699006539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13269572488295615598675385 9952179366221711699006539)
          ·
            refine ⟨14928269049332567548509809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952179366221711699006539 14928269049332567548509809)
            ·
              refine ⟨11196201786999425661382357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14928269049332567548509809 11196201786999425661382357)
              ·
                refine ⟨262410979382799038938649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11196201786999425661382357 262410979382799038938649)
                ·
                  refine ⟨196808234537099279203987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262410979382799038938649 196808234537099279203987)
                  ·
                    rfl

theorem cell20_431193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_431193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431193 prefixEnd_431193 := by exact prefixLift 431193
  have htrace : WordTrace (prefixWord ++ tailWord_431193) baseStart_431193 baseEnd_431193 := by
    simpa [prefixWord, tailWord_431193, baseEnd_431193] using wordTrace_append hprefix tailTrace_431193
  have hstable : (prefixWord ++ tailWord_431193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431193).length < 2 ^ (prefixWord ++ tailWord_431193).sum := by decide
  have hdescent : baseEnd_431193 < baseStart_431193 := by decide
  rcases family_descends (prefixWord ++ tailWord_431193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431207 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_431207 : Nat := 118140960795 + 431207 * 2 ^ 59
def prefixEnd_431207 : Nat := 4983230072969 + 3 ^ 40 * 431207 * 2
def baseEnd_431207 : Nat := 196814624518577452737263

theorem tailTrace_431207 : CollatzResearch.WordTrace tailWord_431207 prefixEnd_431207 196814624518577452737263 := by
  unfold tailWord_431207
  simp only [CollatzResearch.WordTrace]
  refine ⟨15727411348818158137587875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10484940899212105425058583 15727411348818158137587875)
  ·
    refine ⟨23591117023227237206381813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15727411348818158137587875 23591117023227237206381813)
    ·
      refine ⟨2211667220927553488098295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23591117023227237206381813 2211667220927553488098295)
      ·
        refine ⟨3317500831391330232147443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211667220927553488098295 3317500831391330232147443)
        ·
          refine ⟨4976251247086995348221165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317500831391330232147443 4976251247086995348221165)
          ·
            refine ⟨1866094217657623255582937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4976251247086995348221165 1866094217657623255582937)
            ·
              refine ⟨1399570663243217441687203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866094217657623255582937 1399570663243217441687203)
              ·
                refine ⟨2099355994864826162530805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399570663243217441687203 2099355994864826162530805)
                ·
                  refine ⟨196814624518577452737263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099355994864826162530805 196814624518577452737263)
                  ·
                    rfl

theorem cell20_431207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_431207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431207 prefixEnd_431207 := by exact prefixLift 431207
  have htrace : WordTrace (prefixWord ++ tailWord_431207) baseStart_431207 baseEnd_431207 := by
    simpa [prefixWord, tailWord_431207, baseEnd_431207] using wordTrace_append hprefix tailTrace_431207
  have hstable : (prefixWord ++ tailWord_431207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431207).length < 2 ^ (prefixWord ++ tailWord_431207).sum := by decide
  have hdescent : baseEnd_431207 < baseStart_431207 := by decide
  rcases family_descends (prefixWord ++ tailWord_431207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431210 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_431210 : Nat := 118140960795 + 431210 * 2 ^ 59
def prefixEnd_431210 : Nat := 4983230072969 + 3 ^ 40 * 431210 * 2
def baseEnd_431210 : Nat := 196815993800322775637251

theorem tailTrace_431210 : CollatzResearch.WordTrace tailWord_431210 prefixEnd_431210 196815993800322775637251 := by
  unfold tailWord_431210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931880191951822412486771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10485013845204859766631389 3931880191951822412486771)
  ·
    refine ⟨5897820287927733618730157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3931880191951822412486771 5897820287927733618730157)
    ·
      refine ⟨2211682607972900107023809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5897820287927733618730157 2211682607972900107023809)
      ·
        refine ⟨1658761955979675080267857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211682607972900107023809 1658761955979675080267857)
        ·
          refine ⟨1244071466984756310200893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658761955979675080267857 1244071466984756310200893)
          ·
            refine ⟨466526800119283616325335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1244071466984756310200893 466526800119283616325335)
            ·
              refine ⟨699790200178925424488003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466526800119283616325335 699790200178925424488003)
              ·
                refine ⟨1049685300268388136732005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699790200178925424488003 1049685300268388136732005)
                ·
                  refine ⟨196815993800322775637251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049685300268388136732005 196815993800322775637251)
                  ·
                    rfl

theorem cell20_431210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_431210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431210 prefixEnd_431210 := by exact prefixLift 431210
  have htrace : WordTrace (prefixWord ++ tailWord_431210) baseStart_431210 baseEnd_431210 := by
    simpa [prefixWord, tailWord_431210, baseEnd_431210] using wordTrace_append hprefix tailTrace_431210
  have hstable : (prefixWord ++ tailWord_431210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431210).length < 2 ^ (prefixWord ++ tailWord_431210).sum := by decide
  have hdescent : baseEnd_431210 < baseStart_431210 := by decide
  rcases family_descends (prefixWord ++ tailWord_431210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431224 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_431224 : Nat := 118140960795 + 431224 * 2 ^ 59
def prefixEnd_431224 : Nat := 4983230072969 + 3 ^ 40 * 431224 * 2
def baseEnd_431224 : Nat := 196822383781800949170527

theorem tailTrace_431224 : CollatzResearch.WordTrace tailWord_431224 prefixEnd_431224 196822383781800949170527 := by
  unfold tailWord_431224
  simp only [CollatzResearch.WordTrace]
  refine ⟨7864015694878285020478363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10485354259837713360637817 7864015694878285020478363)
  ·
    refine ⟨11796023542317427530717545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7864015694878285020478363 11796023542317427530717545)
    ·
      refine ⟨8847017656738070648038159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11796023542317427530717545 8847017656738070648038159)
      ·
        refine ⟨13270526485107105972057239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8847017656738070648038159 13270526485107105972057239)
        ·
          refine ⟨19905789727660658958085859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13270526485107105972057239 19905789727660658958085859)
          ·
            refine ⟨29858684591490988437128789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19905789727660658958085859 29858684591490988437128789)
            ·
              refine ⟨349906460056535020747603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 29858684591490988437128789 349906460056535020747603)
              ·
                refine ⟨524859690084802531121405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349906460056535020747603 524859690084802531121405)
                ·
                  refine ⟨196822383781800949170527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524859690084802531121405 196822383781800949170527)
                  ·
                    rfl

theorem cell20_431224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_431224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431224 prefixEnd_431224 := by exact prefixLift 431224
  have htrace : WordTrace (prefixWord ++ tailWord_431224) baseStart_431224 baseEnd_431224 := by
    simpa [prefixWord, tailWord_431224, baseEnd_431224] using wordTrace_append hprefix tailTrace_431224
  have hstable : (prefixWord ++ tailWord_431224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431224).length < 2 ^ (prefixWord ++ tailWord_431224).sum := by decide
  have hdescent : baseEnd_431224 < baseStart_431224 := by decide
  rcases family_descends (prefixWord ++ tailWord_431224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
