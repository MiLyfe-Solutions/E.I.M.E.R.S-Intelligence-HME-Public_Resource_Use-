import V185TrunkScan23Chunk1346

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7977203 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4]
def baseStart_7977203 : Nat := 118140960795 + 7977203 * 2 ^ 59
def prefixEnd_7977203 : Nat := 4983230072969 + 3 ^ 40 * 7977203 * 2
def baseEnd_7977203 : Nat := 4096139417488257890276017

theorem tailTrace_7977203 : CollatzResearch.WordTrace tailWord_7977203 prefixEnd_7977203 4096139417488257890276017 := by
  unfold tailWord_7977203
  simp only [CollatzResearch.WordTrace]
  refine ⟨290952496118963403651480263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193968330745975602434320175 290952496118963403651480263)
  ·
    refine ⟨436428744178445105477220395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290952496118963403651480263 436428744178445105477220395)
    ·
      refine ⟨654643116267667658215830593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436428744178445105477220395 654643116267667658215830593)
      ·
        refine ⟨490982337200750743661872945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654643116267667658215830593 490982337200750743661872945)
        ·
          refine ⟨368236752900563057746404709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490982337200750743661872945 368236752900563057746404709)
          ·
            refine ⟨69044391168855573327450883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368236752900563057746404709 69044391168855573327450883)
            ·
              refine ⟨103566586753283359991176325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69044391168855573327450883 103566586753283359991176325)
              ·
                refine ⟨19418735016240629998345561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103566586753283359991176325 19418735016240629998345561)
                ·
                  refine ⟨14564051262180472498759171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19418735016240629998345561 14564051262180472498759171)
                  ·
                    refine ⟨21846076893270708748138757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14564051262180472498759171 21846076893270708748138757)
                    ·
                      refine ⟨4096139417488257890276017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21846076893270708748138757 4096139417488257890276017)
                      ·
                        rfl

theorem cell23_7977203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_7977203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977203 prefixEnd_7977203 := by exact prefixLift 7977203
  have htrace : WordTrace (prefixWord ++ tailWord_7977203) baseStart_7977203 baseEnd_7977203 := by
    simpa [prefixWord, tailWord_7977203, baseEnd_7977203] using wordTrace_append hprefix tailTrace_7977203
  have hstable : (prefixWord ++ tailWord_7977203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977203).length < 2 ^ (prefixWord ++ tailWord_7977203).sum := by decide
  have hdescent : baseEnd_7977203 < baseStart_7977203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977213 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_7977213 : Nat := 118140960795 + 7977213 * 2 ^ 59
def prefixEnd_7977213 : Nat := 4983230072969 + 3 ^ 40 * 7977213 * 2
def baseEnd_7977213 : Nat := 1365381517431600950383657

theorem tailTrace_7977213 : CollatzResearch.WordTrace tailWord_7977213 prefixEnd_7977213 1365381517431600950383657 := by
  unfold tailWord_7977213
  simp only [CollatzResearch.WordTrace]
  refine ⟨290952860848927175359344293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193968573899284783572896195 290952860848927175359344293)
  ·
    refine ⟨54553661409173845379877055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290952860848927175359344293 54553661409173845379877055)
    ·
      refine ⟨81830492113760768069815583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54553661409173845379877055 81830492113760768069815583)
      ·
        refine ⟨122745738170641152104723375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81830492113760768069815583 122745738170641152104723375)
        ·
          refine ⟨184118607255961728157085063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122745738170641152104723375 184118607255961728157085063)
          ·
            refine ⟨276177910883942592235627595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184118607255961728157085063 276177910883942592235627595)
            ·
              refine ⟨414266866325913888353441393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276177910883942592235627595 414266866325913888353441393)
              ·
                refine ⟨310700149744435416265081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414266866325913888353441393 310700149744435416265081045)
                ·
                  refine ⟨7282034759635205068712837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310700149744435416265081045 7282034759635205068712837)
                  ·
                    refine ⟨1365381517431600950383657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282034759635205068712837 1365381517431600950383657)
                    ·
                      rfl

theorem cell23_7977213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_7977213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977213 prefixEnd_7977213 := by exact prefixLift 7977213
  have htrace : WordTrace (prefixWord ++ tailWord_7977213) baseStart_7977213 baseEnd_7977213 := by
    simpa [prefixWord, tailWord_7977213, baseEnd_7977213] using wordTrace_append hprefix tailTrace_7977213
  have hstable : (prefixWord ++ tailWord_7977213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977213).length < 2 ^ (prefixWord ++ tailWord_7977213).sum := by decide
  have hdescent : baseEnd_7977213 < baseStart_7977213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977230 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_7977230 : Nat := 118140960795 + 7977230 * 2 ^ 59
def prefixEnd_7977230 : Nat := 4983230072969 + 3 ^ 40 * 7977230 * 2
def baseEnd_7977230 : Nat := 1365384427155309761546131

theorem tailTrace_7977230 : CollatzResearch.WordTrace tailWord_7977230 prefixEnd_7977230 1365384427155309761546131 := by
  unfold tailWord_7977230
  simp only [CollatzResearch.WordTrace]
  refine ⟨36369185111233198407839143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193968987259910391508475429 36369185111233198407839143)
  ·
    refine ⟨54553777666849797611758715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36369185111233198407839143 54553777666849797611758715)
    ·
      refine ⟨81830666500274696417638073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54553777666849797611758715 81830666500274696417638073)
      ·
        refine ⟨61372999875206022313228555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81830666500274696417638073 61372999875206022313228555)
        ·
          refine ⟨92059499812809033469842833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61372999875206022313228555 92059499812809033469842833)
          ·
            refine ⟨69044624859606775102382125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92059499812809033469842833 69044624859606775102382125)
            ·
              refine ⟨25891734322352540663393297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69044624859606775102382125 25891734322352540663393297)
              ·
                refine ⟨19418800741764405497544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25891734322352540663393297 19418800741764405497544973)
                ·
                  refine ⟨7282050278161652061579365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19418800741764405497544973 7282050278161652061579365)
                  ·
                    refine ⟨1365384427155309761546131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282050278161652061579365 1365384427155309761546131)
                    ·
                      rfl

theorem cell23_7977230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_7977230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977230 prefixEnd_7977230 := by exact prefixLift 7977230
  have htrace : WordTrace (prefixWord ++ tailWord_7977230) baseStart_7977230 baseEnd_7977230 := by
    simpa [prefixWord, tailWord_7977230, baseEnd_7977230] using wordTrace_append hprefix tailTrace_7977230
  have hstable : (prefixWord ++ tailWord_7977230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977230).length < 2 ^ (prefixWord ++ tailWord_7977230).sum := by decide
  have hdescent : baseEnd_7977230 < baseStart_7977230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977247 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 1, 4]
def baseStart_7977247 : Nat := 118140960795 + 7977247 * 2 ^ 59
def prefixEnd_7977247 : Nat := 4983230072969 + 3 ^ 40 * 7977247 * 2
def baseEnd_7977247 : Nat := 1365387336879018572708605

theorem tailTrace_7977247 : CollatzResearch.WordTrace tailWord_7977247 prefixEnd_7977247 1365387336879018572708605 := by
  unfold tailWord_7977247
  simp only [CollatzResearch.WordTrace]
  refine ⟨290954100930803999166081995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193969400620535999444054663 290954100930803999166081995)
  ·
    refine ⟨436431151396205998749122993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290954100930803999166081995 436431151396205998749122993)
    ·
      refine ⟨327323363547154499061842245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436431151396205998749122993 327323363547154499061842245)
      ·
        refine ⟨61373130665091468574095421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327323363547154499061842245 61373130665091468574095421)
        ·
          refine ⟨23014923999409300715285783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61373130665091468574095421 23014923999409300715285783)
          ·
            refine ⟨34522385999113951072928675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23014923999409300715285783 34522385999113951072928675)
            ·
              refine ⟨51783578998670926609393013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34522385999113951072928675 51783578998670926609393013)
              ·
                refine ⟨4854710531125399369630595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51783578998670926609393013 4854710531125399369630595)
                ·
                  refine ⟨7282065796688099054445893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854710531125399369630595 7282065796688099054445893)
                  ·
                    refine ⟨1365387336879018572708605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282065796688099054445893 1365387336879018572708605)
                    ·
                      rfl

theorem cell23_7977247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 4].length) (baseStart_7977247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977247 prefixEnd_7977247 := by exact prefixLift 7977247
  have htrace : WordTrace (prefixWord ++ tailWord_7977247) baseStart_7977247 baseEnd_7977247 := by
    simpa [prefixWord, tailWord_7977247, baseEnd_7977247] using wordTrace_append hprefix tailTrace_7977247
  have hstable : (prefixWord ++ tailWord_7977247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977247).length < 2 ^ (prefixWord ++ tailWord_7977247).sum := by decide
  have hdescent : baseEnd_7977247 < baseStart_7977247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977280 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2]
def baseStart_7977280 : Nat := 118140960795 + 7977280 * 2 ^ 59
def prefixEnd_7977280 : Nat := 4983230072969 + 3 ^ 40 * 7977280 * 2
def baseEnd_7977280 : Nat := 4096178955498654089013163

theorem tailTrace_7977280 : CollatzResearch.WordTrace tailWord_7977280 prefixEnd_7977280 4096178955498654089013163 := by
  unfold tailWord_7977280
  simp only [CollatzResearch.WordTrace]
  refine ⟨145477652269842222901016647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193970203026456297201355529 145477652269842222901016647)
  ·
    refine ⟨218216478404763334351524971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145477652269842222901016647 218216478404763334351524971)
    ·
      refine ⟨327324717607145001527287457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218216478404763334351524971 327324717607145001527287457)
      ·
        refine ⟨245493538205358751145465593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327324717607145001527287457 245493538205358751145465593)
        ·
          refine ⟨184120153654019063359099195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245493538205358751145465593 184120153654019063359099195)
          ·
            refine ⟨276180230481028595038648793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184120153654019063359099195 276180230481028595038648793)
            ·
              refine ⟨207135172860771446278986595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276180230481028595038648793 207135172860771446278986595)
              ·
                refine ⟨310702759291157169418479893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207135172860771446278986595 310702759291157169418479893)
                ·
                  refine ⟨14564191841772992316491245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310702759291157169418479893 14564191841772992316491245)
                  ·
                    refine ⟨5461571940664872118684217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14564191841772992316491245 5461571940664872118684217)
                    ·
                      refine ⟨4096178955498654089013163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461571940664872118684217 4096178955498654089013163)
                      ·
                        rfl

theorem cell23_7977280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_7977280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977280 prefixEnd_7977280 := by exact prefixLift 7977280
  have htrace : WordTrace (prefixWord ++ tailWord_7977280) baseStart_7977280 baseEnd_7977280 := by
    simpa [prefixWord, tailWord_7977280, baseEnd_7977280] using wordTrace_append hprefix tailTrace_7977280
  have hstable : (prefixWord ++ tailWord_7977280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977280).length < 2 ^ (prefixWord ++ tailWord_7977280).sum := by decide
  have hdescent : baseEnd_7977280 < baseStart_7977280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977303 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 3, 6]
def baseStart_7977303 : Nat := 118140960795 + 7977303 * 2 ^ 59
def prefixEnd_7977303 : Nat := 4983230072969 + 3 ^ 40 * 7977303 * 2
def baseEnd_7977303 : Nat := 1365396921851235833008519

theorem tailTrace_7977303 : CollatzResearch.WordTrace tailWord_7977303 prefixEnd_7977303 1365396921851235833008519 := by
  unfold tailWord_7977303
  simp only [CollatzResearch.WordTrace]
  refine ⟨290956143418601120730120563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193970762279067413820080375 290956143418601120730120563)
  ·
    refine ⟨436434215127901681095180845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290956143418601120730120563 436434215127901681095180845)
    ·
      refine ⟨163662830672963130410692817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436434215127901681095180845 163662830672963130410692817)
      ·
        refine ⟨122747123004722347808019613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163662830672963130410692817 122747123004722347808019613)
        ·
          refine ⟨46030171126770880428007355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122747123004722347808019613 46030171126770880428007355)
          ·
            refine ⟨69045256690156320642011033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46030171126770880428007355 69045256690156320642011033)
            ·
              refine ⟨51783942517617240481508275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69045256690156320642011033 51783942517617240481508275)
              ·
                refine ⟨77675913776425860722262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51783942517617240481508275 77675913776425860722262413)
                ·
                  refine ⟨29128467666159697770848405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77675913776425860722262413 29128467666159697770848405)
                  ·
                    refine ⟨1365396921851235833008519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29128467666159697770848405 1365396921851235833008519)
                    ·
                      rfl

theorem cell23_7977303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_7977303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977303 prefixEnd_7977303 := by exact prefixLift 7977303
  have htrace : WordTrace (prefixWord ++ tailWord_7977303) baseStart_7977303 baseEnd_7977303 := by
    simpa [prefixWord, tailWord_7977303, baseEnd_7977303] using wordTrace_append hprefix tailTrace_7977303
  have hstable : (prefixWord ++ tailWord_7977303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977303).length < 2 ^ (prefixWord ++ tailWord_7977303).sum := by decide
  have hdescent : baseEnd_7977303 < baseStart_7977303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977314 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7977314 : Nat := 118140960795 + 7977314 * 2 ^ 59
def prefixEnd_7977314 : Nat := 4983230072969 + 3 ^ 40 * 7977314 * 2
def baseEnd_7977314 : Nat := 4096196413840906955988007

theorem tailTrace_7977314 : CollatzResearch.WordTrace tailWord_7977314 prefixEnd_7977314 4096196413840906955988007 := by
  unfold tailWord_7977314
  simp only [CollatzResearch.WordTrace]
  refine ⟨72739136155390317402192749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193971029747707513072513997 72739136155390317402192749)
  ·
    refine ⟨27277176058271369025822281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72739136155390317402192749 27277176058271369025822281)
    ·
      refine ⟨20457882043703526769366711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27277176058271369025822281 20457882043703526769366711)
      ·
        refine ⟨30686823065555290154050067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20457882043703526769366711 30686823065555290154050067)
        ·
          refine ⟨46030234598332935231075101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30686823065555290154050067 46030234598332935231075101)
          ·
            refine ⟨17261337974374850711653163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46030234598332935231075101 17261337974374850711653163)
            ·
              refine ⟨25892006961562276067479745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261337974374850711653163 25892006961562276067479745)
              ·
                refine ⟨19419005221171707050609809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25892006961562276067479745 19419005221171707050609809)
                ·
                  refine ⟨14564253915878780287957357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19419005221171707050609809 14564253915878780287957357)
                  ·
                    refine ⟨5461595218454542607984009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14564253915878780287957357 5461595218454542607984009)
                    ·
                      refine ⟨4096196413840906955988007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461595218454542607984009 4096196413840906955988007)
                      ·
                        rfl

theorem cell23_7977314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7977314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977314 prefixEnd_7977314 := by exact prefixLift 7977314
  have htrace : WordTrace (prefixWord ++ tailWord_7977314) baseStart_7977314 baseEnd_7977314 := by
    simpa [prefixWord, tailWord_7977314, baseEnd_7977314] using wordTrace_append hprefix tailTrace_7977314
  have hstable : (prefixWord ++ tailWord_7977314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977314).length < 2 ^ (prefixWord ++ tailWord_7977314).sum := by decide
  have hdescent : baseEnd_7977314 < baseStart_7977314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977323 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_7977323 : Nat := 118140960795 + 7977323 * 2 ^ 59
def prefixEnd_7977323 : Nat := 4983230072969 + 3 ^ 40 * 7977323 * 2
def baseEnd_7977323 : Nat := 4096201035166797420775465

theorem tailTrace_7977323 : CollatzResearch.WordTrace tailWord_7977323 prefixEnd_7977323 4096201035166797420775465 := by
  unfold tailWord_7977323
  simp only [CollatzResearch.WordTrace]
  refine ⟨290956872878528664145848623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193971248585685776097232415 290956872878528664145848623)
  ·
    refine ⟨436435309317792996218772935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290956872878528664145848623 436435309317792996218772935)
    ·
      refine ⟨654652963976689494328159403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436435309317792996218772935 654652963976689494328159403)
      ·
        refine ⟨981979445965034241492239105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654652963976689494328159403 981979445965034241492239105)
        ·
          refine ⟨736484584473775681119179329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981979445965034241492239105 736484584473775681119179329)
          ·
            refine ⟨552363438355331760839384497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736484584473775681119179329 552363438355331760839384497)
            ·
              refine ⟨414272578766498820629538373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552363438355331760839384497 414272578766498820629538373)
              ·
                refine ⟨77676108518718528868038445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414272578766498820629538373 77676108518718528868038445)
                ·
                  refine ⟨29128540694519448325514417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77676108518718528868038445 29128540694519448325514417)
                  ·
                    refine ⟨21846405520889586244135813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29128540694519448325514417 21846405520889586244135813)
                    ·
                      refine ⟨4096201035166797420775465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21846405520889586244135813 4096201035166797420775465)
                      ·
                        rfl

theorem cell23_7977323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_7977323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977323 prefixEnd_7977323 := by exact prefixLift 7977323
  have htrace : WordTrace (prefixWord ++ tailWord_7977323) baseStart_7977323 baseEnd_7977323 := by
    simpa [prefixWord, tailWord_7977323, baseEnd_7977323] using wordTrace_append hprefix tailTrace_7977323
  have hstable : (prefixWord ++ tailWord_7977323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977323).length < 2 ^ (prefixWord ++ tailWord_7977323).sum := by decide
  have hdescent : baseEnd_7977323 < baseStart_7977323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977327 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 3, 2, 2]
def baseStart_7977327 : Nat := 118140960795 + 7977327 * 2 ^ 59
def prefixEnd_7977327 : Nat := 4983230072969 + 3 ^ 40 * 7977327 * 2
def baseEnd_7977327 : Nat := 4096203089089415405125447

theorem tailTrace_7977327 : CollatzResearch.WordTrace tailWord_7977327 prefixEnd_7977327 4096203089089415405125447 := by
  unfold tailWord_7977327
  simp only [CollatzResearch.WordTrace]
  refine ⟨290957018770514172828994235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193971345847009448552662823 290957018770514172828994235)
  ·
    refine ⟨436435528155771259243491353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290957018770514172828994235 436435528155771259243491353)
    ·
      refine ⟨327326646116828444432618515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436435528155771259243491353 327326646116828444432618515)
      ·
        refine ⟨490989969175242666648927773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327326646116828444432618515 490989969175242666648927773)
        ·
          refine ⟨184121238440715999993347915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490989969175242666648927773 184121238440715999993347915)
          ·
            refine ⟨276181857661073999990021873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184121238440715999993347915 276181857661073999990021873)
            ·
              refine ⟨207136393245805499992516405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276181857661073999990021873 207136393245805499992516405)
              ·
                refine ⟨19419036866794265624298413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207136393245805499992516405 19419036866794265624298413)
                ·
                  refine ⟨7282138825047849609111905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19419036866794265624298413 7282138825047849609111905)
                  ·
                    refine ⟨5461604118785887206833929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282138825047849609111905 5461604118785887206833929)
                    ·
                      refine ⟨4096203089089415405125447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461604118785887206833929 4096203089089415405125447)
                      ·
                        rfl

theorem cell23_7977327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2, 2].length) (baseStart_7977327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977327 prefixEnd_7977327 := by exact prefixLift 7977327
  have htrace : WordTrace (prefixWord ++ tailWord_7977327) baseStart_7977327 baseEnd_7977327 := by
    simpa [prefixWord, tailWord_7977327, baseEnd_7977327] using wordTrace_append hprefix tailTrace_7977327
  have hstable : (prefixWord ++ tailWord_7977327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977327).length < 2 ^ (prefixWord ++ tailWord_7977327).sum := by decide
  have hdescent : baseEnd_7977327 < baseStart_7977327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977330 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_7977330 : Nat := 118140960795 + 7977330 * 2 ^ 59
def prefixEnd_7977330 : Nat := 4983230072969 + 3 ^ 40 * 7977330 * 2
def baseEnd_7977330 : Nat := 4096204629531378893387933

theorem tailTrace_7977330 : CollatzResearch.WordTrace tailWord_7977330 prefixEnd_7977330 4096204629531378893387933 := by
  unfold tailWord_7977330
  simp only [CollatzResearch.WordTrace]
  refine ⟨72739282047375826085338361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193971418793002202894235629 72739282047375826085338361)
  ·
    refine ⟨54554461535531869564003771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72739282047375826085338361 54554461535531869564003771)
    ·
      refine ⟨81831692303297804346005657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54554461535531869564003771 81831692303297804346005657)
      ·
        refine ⟨61373769227473353259504243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81831692303297804346005657 61373769227473353259504243)
        ·
          refine ⟨92060653841210029889256365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61373769227473353259504243 92060653841210029889256365)
          ·
            refine ⟨34522745190453761208471137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92060653841210029889256365 34522745190453761208471137)
            ·
              refine ⟨25892058892840320906353353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34522745190453761208471137 25892058892840320906353353)
              ·
                refine ⟨19419044169630240679765015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25892058892840320906353353 19419044169630240679765015)
                ·
                  refine ⟨29128566254445361019647523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19419044169630240679765015 29128566254445361019647523)
                  ·
                    refine ⟨43692849381668041529471285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29128566254445361019647523 43692849381668041529471285)
                    ·
                      refine ⟨4096204629531378893387933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43692849381668041529471285 4096204629531378893387933)
                      ·
                        rfl

theorem cell23_7977330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_7977330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977330 prefixEnd_7977330 := by exact prefixLift 7977330
  have htrace : WordTrace (prefixWord ++ tailWord_7977330) baseStart_7977330 baseEnd_7977330 := by
    simpa [prefixWord, tailWord_7977330, baseEnd_7977330] using wordTrace_append hprefix tailTrace_7977330
  have hstable : (prefixWord ++ tailWord_7977330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977330).length < 2 ^ (prefixWord ++ tailWord_7977330).sum := by decide
  have hdescent : baseEnd_7977330 < baseStart_7977330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977347 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3]
def baseStart_7977347 : Nat := 118140960795 + 7977347 * 2 ^ 59
def prefixEnd_7977347 : Nat := 4983230072969 + 3 ^ 40 * 7977347 * 2
def baseEnd_7977347 : Nat := 4096213358702505326875355

theorem tailTrace_7977347 : CollatzResearch.WordTrace tailWord_7977347 prefixEnd_7977347 4096213358702505326875355 := by
  unfold tailWord_7977347
  simp only [CollatzResearch.WordTrace]
  refine ⟨290957748230441716244722295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193971832153627810829814863 290957748230441716244722295)
  ·
    refine ⟨436436622345662574367083443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290957748230441716244722295 436436622345662574367083443)
    ·
      refine ⟨654654933518493861550625165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436436622345662574367083443 654654933518493861550625165)
      ·
        refine ⟨245495600069435198081484437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654654933518493861550625165 245495600069435198081484437)
        ·
          refine ⟨11507606253254774910069583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245495600069435198081484437 11507606253254774910069583)
          ·
            refine ⟨17261409379882162365104375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11507606253254774910069583 17261409379882162365104375)
            ·
              refine ⟨25892114069823243547656563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261409379882162365104375 25892114069823243547656563)
              ·
                refine ⟨38838171104734865321484845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25892114069823243547656563 38838171104734865321484845)
                ·
                  refine ⟨14564314164275574495556817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38838171104734865321484845 14564314164275574495556817)
                  ·
                    refine ⟨10923235623206680871667613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14564314164275574495556817 10923235623206680871667613)
                    ·
                      refine ⟨4096213358702505326875355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923235623206680871667613 4096213358702505326875355)
                      ·
                        rfl

theorem cell23_7977347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_7977347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977347 prefixEnd_7977347 := by exact prefixLift 7977347
  have htrace : WordTrace (prefixWord ++ tailWord_7977347) baseStart_7977347 baseEnd_7977347 := by
    simpa [prefixWord, tailWord_7977347, baseEnd_7977347] using wordTrace_append hprefix tailTrace_7977347
  have hstable : (prefixWord ++ tailWord_7977347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977347).length < 2 ^ (prefixWord ++ tailWord_7977347).sum := by decide
  have hdescent : baseEnd_7977347 < baseStart_7977347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977364 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7977364 : Nat := 118140960795 + 7977364 * 2 ^ 59
def prefixEnd_7977364 : Nat := 4983230072969 + 3 ^ 40 * 7977364 * 2
def baseEnd_7977364 : Nat := 4096222087873631760362777

theorem tailTrace_7977364 : CollatzResearch.WordTrace tailWord_7977364 prefixEnd_7977364 4096222087873631760362777 := by
  unfold tailWord_7977364
  simp only [CollatzResearch.WordTrace]
  refine ⟨145479184135690064074045573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193972245514253418765394097 145479184135690064074045573)
  ·
    refine ⟨27277347025441887013883545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145479184135690064074045573 27277347025441887013883545)
    ·
      refine ⟨20458010269081415260412659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27277347025441887013883545 20458010269081415260412659)
      ·
        refine ⟨30687015403622122890618989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20458010269081415260412659 30687015403622122890618989)
        ·
          refine ⟨11507630776358296083982121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30687015403622122890618989 11507630776358296083982121)
          ·
            refine ⟨8630723082268722062986591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11507630776358296083982121 8630723082268722062986591)
            ·
              refine ⟨12946084623403083094479887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630723082268722062986591 12946084623403083094479887)
              ·
                refine ⟨19419126935104624641719831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12946084623403083094479887 19419126935104624641719831)
                ·
                  refine ⟨29128690402656936962579747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19419126935104624641719831 29128690402656936962579747)
                  ·
                    refine ⟨43693035603985405443869621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29128690402656936962579747 43693035603985405443869621)
                    ·
                      refine ⟨4096222087873631760362777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43693035603985405443869621 4096222087873631760362777)
                      ·
                        rfl

theorem cell23_7977364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7977364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977364 prefixEnd_7977364 := by exact prefixLift 7977364
  have htrace : WordTrace (prefixWord ++ tailWord_7977364) baseStart_7977364 baseEnd_7977364 := by
    simpa [prefixWord, tailWord_7977364, baseEnd_7977364] using wordTrace_append hprefix tailTrace_7977364
  have hstable : (prefixWord ++ tailWord_7977364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977364).length < 2 ^ (prefixWord ++ tailWord_7977364).sum := by decide
  have hdescent : baseEnd_7977364 < baseStart_7977364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977403 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_7977403 : Nat := 118140960795 + 7977403 * 2 ^ 59
def prefixEnd_7977403 : Nat := 4983230072969 + 3 ^ 40 * 7977403 * 2
def baseEnd_7977403 : Nat := 4096242113619157107775097

theorem tailTrace_7977403 : CollatzResearch.WordTrace tailWord_7977403 prefixEnd_7977403 4096242113619157107775097 := by
  unfold tailWord_7977403
  simp only [CollatzResearch.WordTrace]
  refine ⟨290959790718238837808760863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193973193812159225205840575 290959790718238837808760863)
  ·
    refine ⟨436439686077358256713141295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290959790718238837808760863 436439686077358256713141295)
    ·
      refine ⟨654659529116037385069711943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436439686077358256713141295 654659529116037385069711943)
      ·
        refine ⟨981989293674056077604567915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654659529116037385069711943 981989293674056077604567915)
        ·
          refine ⟨1472983940511084116406851873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981989293674056077604567915 1472983940511084116406851873)
          ·
            refine ⟨1104737955383313087305138905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472983940511084116406851873 1104737955383313087305138905)
            ·
              refine ⟨828553466537484815478854179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104737955383313087305138905 828553466537484815478854179)
              ·
                refine ⟨1242830199806227223218281269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828553466537484815478854179 1242830199806227223218281269)
                ·
                  refine ⟨116515331231833802176713869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242830199806227223218281269 116515331231833802176713869)
                  ·
                    refine ⟨43693249211937675816267701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116515331231833802176713869 43693249211937675816267701)
                    ·
                      refine ⟨4096242113619157107775097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43693249211937675816267701 4096242113619157107775097)
                      ·
                        rfl

theorem cell23_7977403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_7977403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977403 prefixEnd_7977403 := by exact prefixLift 7977403
  have htrace : WordTrace (prefixWord ++ tailWord_7977403) baseStart_7977403 baseEnd_7977403 := by
    simpa [prefixWord, tailWord_7977403, baseEnd_7977403] using wordTrace_append hprefix tailTrace_7977403
  have hstable : (prefixWord ++ tailWord_7977403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977403).length < 2 ^ (prefixWord ++ tailWord_7977403).sum := by decide
  have hdescent : baseEnd_7977403 < baseStart_7977403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977404 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7977404 : Nat := 118140960795 + 7977404 * 2 ^ 59
def prefixEnd_7977404 : Nat := 4983230072969 + 3 ^ 40 * 7977404 * 2
def baseEnd_7977404 : Nat := 4096242627099811603862593

theorem tailTrace_7977404 : CollatzResearch.WordTrace tailWord_7977404 prefixEnd_7977404 4096242627099811603862593 := by
  unfold tailWord_7977404
  simp only [CollatzResearch.WordTrace]
  refine ⟨145479913595617607489773633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193973218127490143319698177 145479913595617607489773633)
  ·
    refine ⟨109109935196713205617330225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145479913595617607489773633 109109935196713205617330225)
    ·
      refine ⟨81832451397534904212997669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109109935196713205617330225 81832451397534904212997669)
      ·
        refine ⟨15343584637037794539937063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81832451397534904212997669 15343584637037794539937063)
        ·
          refine ⟨23015376955556691809905595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15343584637037794539937063 23015376955556691809905595)
          ·
            refine ⟨34523065433335037714858393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23015376955556691809905595 34523065433335037714858393)
            ·
              refine ⟨25892299075001278286143795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34523065433335037714858393 25892299075001278286143795)
              ·
                refine ⟨38838448612501917429215693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25892299075001278286143795 38838448612501917429215693)
                ·
                  refine ⟨14564418229688219035955885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38838448612501917429215693 14564418229688219035955885)
                  ·
                    refine ⟨5461656836133082138483457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14564418229688219035955885 5461656836133082138483457)
                    ·
                      refine ⟨4096242627099811603862593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461656836133082138483457 4096242627099811603862593)
                      ·
                        rfl

theorem cell23_7977404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7977404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977404 prefixEnd_7977404 := by exact prefixLift 7977404
  have htrace : WordTrace (prefixWord ++ tailWord_7977404) baseStart_7977404 baseEnd_7977404 := by
    simpa [prefixWord, tailWord_7977404, baseEnd_7977404] using wordTrace_append hprefix tailTrace_7977404
  have hstable : (prefixWord ++ tailWord_7977404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977404).length < 2 ^ (prefixWord ++ tailWord_7977404).sum := by decide
  have hdescent : baseEnd_7977404 < baseStart_7977404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977417 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 1, 4, 2]
def baseStart_7977417 : Nat := 118140960795 + 7977417 * 2 ^ 59
def prefixEnd_7977417 : Nat := 4983230072969 + 3 ^ 40 * 7977417 * 2
def baseEnd_7977417 : Nat := 4096249302348320053000033

theorem tailTrace_7977417 : CollatzResearch.WordTrace tailWord_7977417 prefixEnd_7977417 4096249302348320053000033 := by
  unfold tailWord_7977417
  simp only [CollatzResearch.WordTrace]
  refine ⟨290960301340188118199770505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193973534226792078799847003 290960301340188118199770505)
  ·
    refine ⟨218220226005141088649827879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290960301340188118199770505 218220226005141088649827879)
    ·
      refine ⟨327330339007711632974741819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218220226005141088649827879 327330339007711632974741819)
      ·
        refine ⟨490995508511567449462112729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327330339007711632974741819 490995508511567449462112729)
        ·
          refine ⟨368246631383675587096584547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490995508511567449462112729 368246631383675587096584547)
          ·
            refine ⟨552369947075513380644876821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368246631383675587096584547 552369947075513380644876821)
            ·
              refine ⟨25892341269164689717728601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 552369947075513380644876821 25892341269164689717728601)
              ·
                refine ⟨19419255951873517288296451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25892341269164689717728601 19419255951873517288296451)
                ·
                  refine ⟨29128883927810275932444677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19419255951873517288296451 29128883927810275932444677)
                  ·
                    refine ⟨5461665736464426737333377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29128883927810275932444677 5461665736464426737333377)
                    ·
                      refine ⟨4096249302348320053000033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461665736464426737333377 4096249302348320053000033)
                      ·
                        rfl

theorem cell23_7977417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4, 2].length) (baseStart_7977417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977417 prefixEnd_7977417 := by exact prefixLift 7977417
  have htrace : WordTrace (prefixWord ++ tailWord_7977417) baseStart_7977417 baseEnd_7977417 := by
    simpa [prefixWord, tailWord_7977417, baseEnd_7977417] using wordTrace_append hprefix tailTrace_7977417
  have hstable : (prefixWord ++ tailWord_7977417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977417).length < 2 ^ (prefixWord ++ tailWord_7977417).sum := by decide
  have hdescent : baseEnd_7977417 < baseStart_7977417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977423 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 11]
def baseStart_7977423 : Nat := 118140960795 + 7977423 * 2 ^ 59
def prefixEnd_7977423 : Nat := 4983230072969 + 3 ^ 40 * 7977423 * 2
def baseEnd_7977423 : Nat := 455139153692471892169445

theorem tailTrace_7977423 : CollatzResearch.WordTrace tailWord_7977423 prefixEnd_7977423 455139153692471892169445 := by
  unfold tailWord_7977423
  simp only [CollatzResearch.WordTrace]
  refine ⟨290960520178166381224488923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193973680118777587482992615 290960520178166381224488923)
  ·
    refine ⟨436440780267249571836733385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290960520178166381224488923 436440780267249571836733385)
    ·
      refine ⟨327330585200437178877550039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436440780267249571836733385 327330585200437178877550039)
      ·
        refine ⟨490995877800655768316325059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327330585200437178877550039 490995877800655768316325059)
        ·
          refine ⟨736493816700983652474487589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490995877800655768316325059 736493816700983652474487589)
          ·
            refine ⟨138092590631434434838966423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 736493816700983652474487589 138092590631434434838966423)
            ·
              refine ⟨207138885947151652258449635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138092590631434434838966423 207138885947151652258449635)
              ·
                refine ⟨310708328920727478387674453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207138885947151652258449635 310708328920727478387674453)
                ·
                  refine ⟨455139153692471892169445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 310708328920727478387674453 455139153692471892169445)
                  ·
                    rfl

theorem cell23_7977423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 11].length) (baseStart_7977423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977423 prefixEnd_7977423 := by exact prefixLift 7977423
  have htrace : WordTrace (prefixWord ++ tailWord_7977423) baseStart_7977423 baseEnd_7977423 := by
    simpa [prefixWord, tailWord_7977423, baseEnd_7977423] using wordTrace_append hprefix tailTrace_7977423
  have hstable : (prefixWord ++ tailWord_7977423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977423).length < 2 ^ (prefixWord ++ tailWord_7977423).sum := by decide
  have hdescent : baseEnd_7977423 < baseStart_7977423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977434 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_7977434 : Nat := 118140960795 + 7977434 * 2 ^ 59
def prefixEnd_7977434 : Nat := 4983230072969 + 3 ^ 40 * 7977434 * 2
def baseEnd_7977434 : Nat := 4096258031519446486487455

theorem tailTrace_7977434 : CollatzResearch.WordTrace tailWord_7977434 prefixEnd_7977434 4096258031519446486487455 := by
  unfold tailWord_7977434
  simp only [CollatzResearch.WordTrace]
  refine ⟨72740230345281632525784839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193973947587417686735426237 72740230345281632525784839)
  ·
    refine ⟨109110345517922448788677259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72740230345281632525784839 109110345517922448788677259)
    ·
      refine ⟨163665518276883673183015889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109110345517922448788677259 163665518276883673183015889)
      ·
        refine ⟨122749138707662754887261917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163665518276883673183015889 122749138707662754887261917)
        ·
          refine ⟨46030927015373533082723219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122749138707662754887261917 46030927015373533082723219)
          ·
            refine ⟨69046390523060299624084829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46030927015373533082723219 69046390523060299624084829)
            ·
              refine ⟨25892396446147612359031811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69046390523060299624084829 25892396446147612359031811)
              ·
                refine ⟨38838594669221418538547717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25892396446147612359031811 38838594669221418538547717)
                ·
                  refine ⟨7282236500479015975977697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38838594669221418538547717 7282236500479015975977697)
                  ·
                    refine ⟨5461677375359261981983273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282236500479015975977697 5461677375359261981983273)
                    ·
                      refine ⟨4096258031519446486487455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461677375359261981983273 4096258031519446486487455)
                      ·
                        rfl

theorem cell23_7977434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_7977434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977434 prefixEnd_7977434 := by exact prefixLift 7977434
  have htrace : WordTrace (prefixWord ++ tailWord_7977434) baseStart_7977434 baseEnd_7977434 := by
    simpa [prefixWord, tailWord_7977434, baseEnd_7977434] using wordTrace_append hprefix tailTrace_7977434
  have hstable : (prefixWord ++ tailWord_7977434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977434).length < 2 ^ (prefixWord ++ tailWord_7977434).sum := by decide
  have hdescent : baseEnd_7977434 < baseStart_7977434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977440 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 7]
def baseStart_7977440 : Nat := 118140960795 + 7977440 * 2 ^ 59
def prefixEnd_7977440 : Nat := 4983230072969 + 3 ^ 40 * 7977440 * 2
def baseEnd_7977440 : Nat := 455140123600374829223603

theorem tailTrace_7977440 : CollatzResearch.WordTrace tailWord_7977440 prefixEnd_7977440 455140123600374829223603 := by
  unfold tailWord_7977440
  simp only [CollatzResearch.WordTrace]
  refine ⟨145480570109552396563928887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193974093479403195418571849 145480570109552396563928887)
  ·
    refine ⟨218220855164328594845893331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145480570109552396563928887 218220855164328594845893331)
    ·
      refine ⟨327331282746492892268839997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218220855164328594845893331 327331282746492892268839997)
      ·
        refine ⟨122749231029934834600814999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327331282746492892268839997 122749231029934834600814999)
        ·
          refine ⟨184123846544902251901222499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122749231029934834600814999 184123846544902251901222499)
          ·
            refine ⟨276185769817353377851833749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184123846544902251901222499 276185769817353377851833749)
            ·
              refine ⟨12946207960188439586804707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276185769817353377851833749 12946207960188439586804707)
              ·
                refine ⟨19419311940282659380207061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12946207960188439586804707 19419311940282659380207061)
                ·
                  refine ⟨455140123600374829223603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19419311940282659380207061 455140123600374829223603)
                  ·
                    rfl

theorem cell23_7977440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_7977440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977440 prefixEnd_7977440 := by exact prefixLift 7977440
  have htrace : WordTrace (prefixWord ++ tailWord_7977440) baseStart_7977440 baseEnd_7977440 := by
    simpa [prefixWord, tailWord_7977440, baseEnd_7977440] using wordTrace_append hprefix tailTrace_7977440
  have hstable : (prefixWord ++ tailWord_7977440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977440).length < 2 ^ (prefixWord ++ tailWord_7977440).sum := by decide
  have hdescent : baseEnd_7977440 < baseStart_7977440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977451 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 2, 2, 2]
def baseStart_7977451 : Nat := 118140960795 + 7977451 * 2 ^ 59
def prefixEnd_7977451 : Nat := 4983230072969 + 3 ^ 40 * 7977451 * 2
def baseEnd_7977451 : Nat := 4096266760690572919974877

theorem tailTrace_7977451 : CollatzResearch.WordTrace tailWord_7977451 prefixEnd_7977451 4096266760690572919974877 := by
  unfold tailWord_7977451
  simp only [CollatzResearch.WordTrace]
  refine ⟨290961541422064942006508207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193974360948043294671005471 290961541422064942006508207)
  ·
    refine ⟨436442312133097413009762311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290961541422064942006508207 436442312133097413009762311)
    ·
      refine ⟨654663468199646119514643467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436442312133097413009762311 654663468199646119514643467)
      ·
        refine ⟨981995202299469179271965201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654663468199646119514643467 981995202299469179271965201)
        ·
          refine ⟨736496401724601884453973901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981995202299469179271965201 736496401724601884453973901)
          ·
            refine ⟨276186150646725706670240213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736496401724601884453973901 276186150646725706670240213)
            ·
              refine ⟨6473112905782633750083755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 276186150646725706670240213 6473112905782633750083755)
              ·
                refine ⟨9709669358673950625125633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473112905782633750083755 9709669358673950625125633)
                ·
                  refine ⟨7282252019005462968844225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9709669358673950625125633 7282252019005462968844225)
                  ·
                    refine ⟨5461689014254097226633169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282252019005462968844225 5461689014254097226633169)
                    ·
                      refine ⟨4096266760690572919974877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461689014254097226633169 4096266760690572919974877)
                      ·
                        rfl

theorem cell23_7977451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 2, 2].length) (baseStart_7977451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977451 prefixEnd_7977451 := by exact prefixLift 7977451
  have htrace : WordTrace (prefixWord ++ tailWord_7977451) baseStart_7977451 baseEnd_7977451 := by
    simpa [prefixWord, tailWord_7977451, baseEnd_7977451] using wordTrace_append hprefix tailTrace_7977451
  have hstable : (prefixWord ++ tailWord_7977451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977451).length < 2 ^ (prefixWord ++ tailWord_7977451).sum := by decide
  have hdescent : baseEnd_7977451 < baseStart_7977451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977480 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_7977480 : Nat := 118140960795 + 7977480 * 2 ^ 59
def prefixEnd_7977480 : Nat := 4983230072969 + 3 ^ 40 * 7977480 * 2
def baseEnd_7977480 : Nat := 4096281651629553306512243

theorem tailTrace_7977480 : CollatzResearch.WordTrace tailWord_7977480 prefixEnd_7977480 4096281651629553306512243 := by
  unfold tailWord_7977480
  simp only [CollatzResearch.WordTrace]
  refine ⟨145481299569479939979656947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193975066092639919972875929 145481299569479939979656947)
  ·
    refine ⟨218221949354219909969485421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145481299569479939979656947 218221949354219909969485421)
    ·
      refine ⟨81833231007832466238557033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218221949354219909969485421 81833231007832466238557033)
      ·
        refine ⟨61374923255874349678917775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81833231007832466238557033 61374923255874349678917775)
        ·
          refine ⟨92062384883811524518376663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61374923255874349678917775 92062384883811524518376663)
          ·
            refine ⟨138093577325717286777564995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92062384883811524518376663 138093577325717286777564995)
            ·
              refine ⟨207140365988575930166347493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138093577325717286777564995 207140365988575930166347493)
              ·
                refine ⟨38838818622857986906190155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207140365988575930166347493 38838818622857986906190155)
                ·
                  refine ⟨58258227934286980359285233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38838818622857986906190155 58258227934286980359285233)
                  ·
                    refine ⟨43693670950715235269463925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58258227934286980359285233 43693670950715235269463925)
                    ·
                      refine ⟨4096281651629553306512243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43693670950715235269463925 4096281651629553306512243)
                      ·
                        rfl

theorem cell23_7977480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_7977480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977480 prefixEnd_7977480 := by exact prefixLift 7977480
  have htrace : WordTrace (prefixWord ++ tailWord_7977480) baseStart_7977480 baseEnd_7977480 := by
    simpa [prefixWord, tailWord_7977480, baseEnd_7977480] using wordTrace_append hprefix tailTrace_7977480
  have hstable : (prefixWord ++ tailWord_7977480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977480).length < 2 ^ (prefixWord ++ tailWord_7977480).sum := by decide
  have hdescent : baseEnd_7977480 < baseStart_7977480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977520 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_7977520 : Nat := 118140960795 + 7977520 * 2 ^ 59
def prefixEnd_7977520 : Nat := 4983230072969 + 3 ^ 40 * 7977520 * 2
def baseEnd_7977520 : Nat := 4096302190855733150012059

theorem tailTrace_7977520 : CollatzResearch.WordTrace tailWord_7977520 prefixEnd_7977520 4096302190855733150012059 := by
  unfold tailWord_7977520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145482029029407483395385007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193976038705876644527180009 145482029029407483395385007)
  ·
    refine ⟨218223043544111225093077511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145482029029407483395385007 218223043544111225093077511)
    ·
      refine ⟨327334565316166837639616267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218223043544111225093077511 327334565316166837639616267)
      ·
        refine ⟨491001847974250256459424401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327334565316166837639616267 491001847974250256459424401)
        ·
          refine ⟨368251385980687692344568301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491001847974250256459424401 368251385980687692344568301)
          ·
            refine ⟨138094269742757884629213113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368251385980687692344568301 138094269742757884629213113)
            ·
              refine ⟨103570702307068413471909835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138094269742757884629213113 103570702307068413471909835)
              ·
                refine ⟨155356053460602620207864753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103570702307068413471909835 155356053460602620207864753)
                ·
                  refine ⟨116517040095451965155898565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155356053460602620207864753 116517040095451965155898565)
                  ·
                    refine ⟨21846945017897243466730981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116517040095451965155898565 21846945017897243466730981)
                    ·
                      refine ⟨4096302190855733150012059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21846945017897243466730981 4096302190855733150012059)
                      ·
                        rfl

theorem cell23_7977520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_7977520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977520 prefixEnd_7977520 := by exact prefixLift 7977520
  have htrace : WordTrace (prefixWord ++ tailWord_7977520) baseStart_7977520 baseEnd_7977520 := by
    simpa [prefixWord, tailWord_7977520, baseEnd_7977520] using wordTrace_append hprefix tailTrace_7977520
  have hstable : (prefixWord ++ tailWord_7977520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977520).length < 2 ^ (prefixWord ++ tailWord_7977520).sum := by decide
  have hdescent : baseEnd_7977520 < baseStart_7977520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977551 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 1, 4]
def baseStart_7977551 : Nat := 118140960795 + 7977551 * 2 ^ 59
def prefixEnd_7977551 : Nat := 4983230072969 + 3 ^ 40 * 7977551 * 2
def baseEnd_7977551 : Nat := 1365439369585340842908139

theorem tailTrace_7977551 : CollatzResearch.WordTrace tailWord_7977551 prefixEnd_7977551 1365439369585340842908139 := by
  unfold tailWord_7977551
  simp only [CollatzResearch.WordTrace]
  refine ⟨290965188721702659085148507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193976792481135106056765671 290965188721702659085148507)
  ·
    refine ⟨436447783082553988627722761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290965188721702659085148507 436447783082553988627722761)
    ·
      refine ⟨327335837311915491470792071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436447783082553988627722761 327335837311915491470792071)
      ·
        refine ⟨491003755967873237206188107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327335837311915491470792071 491003755967873237206188107)
        ·
          refine ⟨736505633951809855809282161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491003755967873237206188107 736505633951809855809282161)
          ·
            refine ⟨552379225463857391856961621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736505633951809855809282161 552379225463857391856961621)
            ·
              refine ⟨6473194048404578810823769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 552379225463857391856961621 6473194048404578810823769)
              ·
                refine ⟨4854895536303434108117827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6473194048404578810823769 4854895536303434108117827)
                ·
                  refine ⟨7282343304455151162176741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854895536303434108117827 7282343304455151162176741)
                  ·
                    refine ⟨1365439369585340842908139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282343304455151162176741 1365439369585340842908139)
                    ·
                      rfl

theorem cell23_7977551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 4].length) (baseStart_7977551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977551 prefixEnd_7977551 := by exact prefixLift 7977551
  have htrace : WordTrace (prefixWord ++ tailWord_7977551) baseStart_7977551 baseEnd_7977551 := by
    simpa [prefixWord, tailWord_7977551, baseEnd_7977551] using wordTrace_append hprefix tailTrace_7977551
  have hstable : (prefixWord ++ tailWord_7977551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977551).length < 2 ^ (prefixWord ++ tailWord_7977551).sum := by decide
  have hdescent : baseEnd_7977551 < baseStart_7977551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977577 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_7977577 : Nat := 118140960795 + 7977577 * 2 ^ 59
def prefixEnd_7977577 : Nat := 4983230072969 + 3 ^ 40 * 7977577 * 2
def baseEnd_7977577 : Nat := 1365443819751013142333099

theorem tailTrace_7977577 : CollatzResearch.WordTrace tailWord_7977577 prefixEnd_7977577 1365443819751013142333099 := by
  unfold tailWord_7977577
  simp only [CollatzResearch.WordTrace]
  refine ⟨290966137019608465525594985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193977424679738977017063323 290966137019608465525594985)
  ·
    refine ⟨218224602764706349144196239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290966137019608465525594985 218224602764706349144196239)
    ·
      refine ⟨327336904147059523716294359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218224602764706349144196239 327336904147059523716294359)
      ·
        refine ⟨491005356220589285574441539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327336904147059523716294359 491005356220589285574441539)
        ·
          refine ⟨736508034330883928361662309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491005356220589285574441539 736508034330883928361662309)
          ·
            refine ⟨138095256437040736567811683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 736508034330883928361662309 138095256437040736567811683)
            ·
              refine ⟨207142884655561104851717525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138095256437040736567811683 207142884655561104851717525)
              ·
                refine ⟨9709822718229426789924259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207142884655561104851717525 9709822718229426789924259)
                ·
                  refine ⟨14564734077344140184886389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9709822718229426789924259 14564734077344140184886389)
                  ·
                    refine ⟨1365443819751013142333099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14564734077344140184886389 1365443819751013142333099)
                    ·
                      rfl

theorem cell23_7977577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_7977577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977577 prefixEnd_7977577 := by exact prefixLift 7977577
  have htrace : WordTrace (prefixWord ++ tailWord_7977577) baseStart_7977577 baseEnd_7977577 := by
    simpa [prefixWord, tailWord_7977577, baseEnd_7977577] using wordTrace_append hprefix tailTrace_7977577
  have hstable : (prefixWord ++ tailWord_7977577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977577).length < 2 ^ (prefixWord ++ tailWord_7977577).sum := by decide
  have hdescent : baseEnd_7977577 < baseStart_7977577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977591 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 1, 1, 3]
def baseStart_7977591 : Nat := 118140960795 + 7977591 * 2 ^ 59
def prefixEnd_7977591 : Nat := 4983230072969 + 3 ^ 40 * 7977591 * 2
def baseEnd_7977591 : Nat := 4096338647982202372224233

theorem tailTrace_7977591 : CollatzResearch.WordTrace tailWord_7977591 prefixEnd_7977591 4096338647982202372224233 := by
  unfold tailWord_7977591
  simp only [CollatzResearch.WordTrace]
  refine ⟨290966647641557745916604627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193977765094371830611069751 290966647641557745916604627)
  ·
    refine ⟨436449971462336618874906941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290966647641557745916604627 436449971462336618874906941)
    ·
      refine ⟨163668739298376232078090103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436449971462336618874906941 163668739298376232078090103)
      ·
        refine ⟨245503108947564348117135155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163668739298376232078090103 245503108947564348117135155)
        ·
          refine ⟨368254663421346522175702733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245503108947564348117135155 368254663421346522175702733)
          ·
            refine ⟨138095498783004945815888525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368254663421346522175702733 138095498783004945815888525)
            ·
              refine ⟨51785812043626854680958197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138095498783004945815888525 51785812043626854680958197)
              ·
                refine ⟨4854919879090017626339831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51785812043626854680958197 4854919879090017626339831)
                ·
                  refine ⟨7282379818635026439509747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854919879090017626339831 7282379818635026439509747)
                  ·
                    refine ⟨10923569727952539659264621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7282379818635026439509747 10923569727952539659264621)
                    ·
                      refine ⟨4096338647982202372224233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923569727952539659264621 4096338647982202372224233)
                      ·
                        rfl

theorem cell23_7977591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_7977591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977591 prefixEnd_7977591 := by exact prefixLift 7977591
  have htrace : WordTrace (prefixWord ++ tailWord_7977591) baseStart_7977591 baseEnd_7977591 := by
    simpa [prefixWord, tailWord_7977591, baseEnd_7977591] using wordTrace_append hprefix tailTrace_7977591
  have hstable : (prefixWord ++ tailWord_7977591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977591).length < 2 ^ (prefixWord ++ tailWord_7977591).sum := by decide
  have hdescent : baseEnd_7977591 < baseStart_7977591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977681 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_7977681 : Nat := 118140960795 + 7977681 * 2 ^ 59
def prefixEnd_7977681 : Nat := 4983230072969 + 3 ^ 40 * 7977681 * 2
def baseEnd_7977681 : Nat := 4096384861241107020098819

theorem tailTrace_7977681 : CollatzResearch.WordTrace tailWord_7977681 prefixEnd_7977681 4096384861241107020098819 := by
  unfold tailWord_7977681
  simp only [CollatzResearch.WordTrace]
  refine ⟨290969930211231691287380897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193979953474154460858253931 290969930211231691287380897)
  ·
    refine ⟨218227447658423768465535673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290969930211231691287380897 218227447658423768465535673)
    ·
      refine ⟨163670585743817826349151755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218227447658423768465535673 163670585743817826349151755)
      ·
        refine ⟨245505878615726739523727633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163670585743817826349151755 245505878615726739523727633)
        ·
          refine ⟨184129408961795054642795725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245505878615726739523727633 184129408961795054642795725)
          ·
            refine ⟨69048528360673145491048397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184129408961795054642795725 69048528360673145491048397)
            ·
              refine ⟨25893198135252429559143149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69048528360673145491048397 25893198135252429559143149)
              ·
                refine ⟨9709949300719661084678681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25893198135252429559143149 9709949300719661084678681)
                ·
                  refine ⟨7282461975539745813509011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9709949300719661084678681 7282461975539745813509011)
                  ·
                    refine ⟨10923692963309618720263517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7282461975539745813509011 10923692963309618720263517)
                    ·
                      refine ⟨4096384861241107020098819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923692963309618720263517 4096384861241107020098819)
                      ·
                        rfl

theorem cell23_7977681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_7977681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977681 prefixEnd_7977681 := by exact prefixLift 7977681
  have htrace : WordTrace (prefixWord ++ tailWord_7977681) baseStart_7977681 baseEnd_7977681 := by
    simpa [prefixWord, tailWord_7977681, baseEnd_7977681] using wordTrace_append hprefix tailTrace_7977681
  have hstable : (prefixWord ++ tailWord_7977681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977681).length < 2 ^ (prefixWord ++ tailWord_7977681).sum := by decide
  have hdescent : baseEnd_7977681 < baseStart_7977681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977685 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7977685 : Nat := 118140960795 + 7977685 * 2 ^ 59
def prefixEnd_7977685 : Nat := 4983230072969 + 3 ^ 40 * 7977685 * 2
def baseEnd_7977685 : Nat := 4096386915163725004448801

theorem tailTrace_7977685 : CollatzResearch.WordTrace tailWord_7977685 prefixEnd_7977685 4096386915163725004448801 := by
  unfold tailWord_7977685
  simp only [CollatzResearch.WordTrace]
  refine ⟨290970076103217199970526509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193980050735478133313684339 290970076103217199970526509)
  ·
    refine ⟨109113778538706449988947441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290970076103217199970526509 109113778538706449988947441)
    ·
      refine ⟨81835333904029837491710581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109113778538706449988947441 81835333904029837491710581)
      ·
        refine ⟨7672062553502797264847867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81835333904029837491710581 7672062553502797264847867)
        ·
          refine ⟨11508093830254195897271801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672062553502797264847867 11508093830254195897271801)
          ·
            refine ⟨8631070372690646922953851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11508093830254195897271801 8631070372690646922953851)
            ·
              refine ⟨12946605559035970384430777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631070372690646922953851 12946605559035970384430777)
              ·
                refine ⟨9709954169276977788323083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12946605559035970384430777 9709954169276977788323083)
                ·
                  refine ⟨14564931253915466682484625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9709954169276977788323083 14564931253915466682484625)
                  ·
                    refine ⟨10923698440436600011863469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14564931253915466682484625 10923698440436600011863469)
                    ·
                      refine ⟨4096386915163725004448801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923698440436600011863469 4096386915163725004448801)
                      ·
                        rfl

theorem cell23_7977685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7977685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977685 prefixEnd_7977685 := by exact prefixLift 7977685
  have htrace : WordTrace (prefixWord ++ tailWord_7977685) baseStart_7977685 baseEnd_7977685 := by
    simpa [prefixWord, tailWord_7977685, baseEnd_7977685] using wordTrace_append hprefix tailTrace_7977685
  have hstable : (prefixWord ++ tailWord_7977685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977685).length < 2 ^ (prefixWord ++ tailWord_7977685).sum := by decide
  have hdescent : baseEnd_7977685 < baseStart_7977685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977721 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 4, 2, 2]
def baseStart_7977721 : Nat := 118140960795 + 7977721 * 2 ^ 59
def prefixEnd_7977721 : Nat := 4983230072969 + 3 ^ 40 * 7977721 * 2
def baseEnd_7977721 : Nat := 4096405400467286863598635

theorem tailTrace_7977721 : CollatzResearch.WordTrace tailWord_7977721 prefixEnd_7977721 4096405400467286863598635 := by
  unfold tailWord_7977721
  simp only [CollatzResearch.WordTrace]
  refine ⟨290971389131086778118837017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193980926087391185412558011 290971389131086778118837017)
  ·
    refine ⟨218228541848315083589127763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290971389131086778118837017 218228541848315083589127763)
    ·
      refine ⟨327342812772472625383691645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218228541848315083589127763 327342812772472625383691645)
      ·
        refine ⟨122753554789677234518884367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327342812772472625383691645 122753554789677234518884367)
        ·
          refine ⟨184130332184515851778326551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122753554789677234518884367 184130332184515851778326551)
          ·
            refine ⟨276195498276773777667489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184130332184515851778326551 276195498276773777667489827)
            ·
              refine ⟨414293247415160666501234741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276195498276773777667489827 414293247415160666501234741)
              ·
                refine ⟨38839991945171312484490757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414293247415160666501234741 38839991945171312484490757)
                ·
                  refine ⟨7282498489719621090842017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38839991945171312484490757 7282498489719621090842017)
                  ·
                    refine ⟨5461873867289715818131513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282498489719621090842017 5461873867289715818131513)
                    ·
                      refine ⟨4096405400467286863598635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461873867289715818131513 4096405400467286863598635)
                      ·
                        rfl

theorem cell23_7977721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_7977721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977721 prefixEnd_7977721 := by exact prefixLift 7977721
  have htrace : WordTrace (prefixWord ++ tailWord_7977721) baseStart_7977721 baseEnd_7977721 := by
    simpa [prefixWord, tailWord_7977721, baseEnd_7977721] using wordTrace_append hprefix tailTrace_7977721
  have hstable : (prefixWord ++ tailWord_7977721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977721).length < 2 ^ (prefixWord ++ tailWord_7977721).sum := by decide
  have hdescent : baseEnd_7977721 < baseStart_7977721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977724 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_7977724 : Nat := 118140960795 + 7977724 * 2 ^ 59
def prefixEnd_7977724 : Nat := 4983230072969 + 3 ^ 40 * 7977724 * 2
def baseEnd_7977724 : Nat := 4096406940909250351861121

theorem tailTrace_7977724 : CollatzResearch.WordTrace tailWord_7977724 prefixEnd_7977724 4096406940909250351861121 := by
  unfold tailWord_7977724
  simp only [CollatzResearch.WordTrace]
  refine ⟨145485749275037954815598113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193980999033383939754130817 145485749275037954815598113)
  ·
    refine ⟨109114311956278466111698585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145485749275037954815598113 109114311956278466111698585)
    ·
      refine ⟨81835733967208849583773939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109114311956278466111698585 81835733967208849583773939)
      ·
        refine ⟨122753600950813274375660909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81835733967208849583773939 122753600950813274375660909)
        ·
          refine ⟨46032600356554977890872841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122753600950813274375660909 46032600356554977890872841)
          ·
            refine ⟨34524450267416233418154631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46032600356554977890872841 34524450267416233418154631)
            ·
              refine ⟨51786675401124350127231947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34524450267416233418154631 51786675401124350127231947)
              ·
                refine ⟨77680013101686525190847921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51786675401124350127231947 77680013101686525190847921)
                ·
                  refine ⟨58260009826264893893135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77680013101686525190847921 58260009826264893893135941)
                  ·
                    refine ⟨10923751842424667604962989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58260009826264893893135941 10923751842424667604962989)
                    ·
                      refine ⟨4096406940909250351861121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923751842424667604962989 4096406940909250351861121)
                      ·
                        rfl

theorem cell23_7977724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_7977724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977724 prefixEnd_7977724 := by exact prefixLift 7977724
  have htrace : WordTrace (prefixWord ++ tailWord_7977724) baseStart_7977724 baseEnd_7977724 := by
    simpa [prefixWord, tailWord_7977724, baseEnd_7977724] using wordTrace_append hprefix tailTrace_7977724
  have hstable : (prefixWord ++ tailWord_7977724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977724).length < 2 ^ (prefixWord ++ tailWord_7977724).sum := by decide
  have hdescent : baseEnd_7977724 < baseStart_7977724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977727 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 7]
def baseStart_7977727 : Nat := 118140960795 + 7977727 * 2 ^ 59
def prefixEnd_7977727 : Nat := 4983230072969 + 3 ^ 40 * 7977727 * 2
def baseEnd_7977727 : Nat := 455156497927912648902623

theorem tailTrace_7977727 : CollatzResearch.WordTrace tailWord_7977727 prefixEnd_7977727 455156497927912648902623 := by
  unfold tailWord_7977727
  simp only [CollatzResearch.WordTrace]
  refine ⟨290971607969065041143555435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193981071979376694095703623 290971607969065041143555435)
  ·
    refine ⟨436457411953597561715333153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290971607969065041143555435 436457411953597561715333153)
    ·
      refine ⟨327343058965198171286499865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436457411953597561715333153 327343058965198171286499865)
      ·
        refine ⟨245507294223898628464874899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327343058965198171286499865 245507294223898628464874899)
        ·
          refine ⟨368260941335847942697312349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245507294223898628464874899 368260941335847942697312349)
          ·
            refine ⟨138097853000942978511492131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368260941335847942697312349 138097853000942978511492131)
            ·
              refine ⟨207146779501414467767238197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138097853000942978511492131 207146779501414467767238197)
              ·
                refine ⟨19420010578257606353178581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207146779501414467767238197 19420010578257606353178581)
                ·
                  refine ⟨455156497927912648902623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19420010578257606353178581 455156497927912648902623)
                  ·
                    rfl

theorem cell23_7977727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 7].length) (baseStart_7977727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977727 prefixEnd_7977727 := by exact prefixLift 7977727
  have htrace : WordTrace (prefixWord ++ tailWord_7977727) baseStart_7977727 baseEnd_7977727 := by
    simpa [prefixWord, tailWord_7977727, baseEnd_7977727] using wordTrace_append hprefix tailTrace_7977727
  have hstable : (prefixWord ++ tailWord_7977727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977727).length < 2 ^ (prefixWord ++ tailWord_7977727).sum := by decide
  have hdescent : baseEnd_7977727 < baseStart_7977727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977738 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_7977738 : Nat := 118140960795 + 7977738 * 2 ^ 59
def prefixEnd_7977738 : Nat := 4983230072969 + 3 ^ 40 * 7977738 * 2
def baseEnd_7977738 : Nat := 4096414129638413297086057

theorem tailTrace_7977738 : CollatzResearch.WordTrace tailWord_7977738 prefixEnd_7977738 4096414129638413297086057 := by
  unfold tailWord_7977738
  simp only [CollatzResearch.WordTrace]
  refine ⟨72743002293006297505551467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193981339448016793348137245 72743002293006297505551467)
  ·
    refine ⟨109114503439509446258327201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72743002293006297505551467 109114503439509446258327201)
    ·
      refine ⟨81835877579632084693745401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109114503439509446258327201 81835877579632084693745401)
      ·
        refine ⟨61376908184724063520309051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81835877579632084693745401 61376908184724063520309051)
        ·
          refine ⟨92065362277086095280463577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61376908184724063520309051 92065362277086095280463577)
          ·
            refine ⟨69049021707814571460347683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92065362277086095280463577 69049021707814571460347683)
            ·
              refine ⟨103573532561721857190521525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69049021707814571460347683 103573532561721857190521525)
              ·
                refine ⟨9710018677661424111611393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103573532561721857190521525 9710018677661424111611393)
                ·
                  refine ⟨7282514008246068083708545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710018677661424111611393 7282514008246068083708545)
                  ·
                    refine ⟨5461885506184551062781409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282514008246068083708545 5461885506184551062781409)
                    ·
                      refine ⟨4096414129638413297086057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461885506184551062781409 4096414129638413297086057)
                      ·
                        rfl

theorem cell23_7977738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_7977738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977738 prefixEnd_7977738 := by exact prefixLift 7977738
  have htrace : WordTrace (prefixWord ++ tailWord_7977738) baseStart_7977738 baseEnd_7977738 := by
    simpa [prefixWord, tailWord_7977738, baseEnd_7977738] using wordTrace_append hprefix tailTrace_7977738
  have hstable : (prefixWord ++ tailWord_7977738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977738).length < 2 ^ (prefixWord ++ tailWord_7977738).sum := by decide
  have hdescent : baseEnd_7977738 < baseStart_7977738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977754 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_7977754 : Nat := 118140960795 + 7977754 * 2 ^ 59
def prefixEnd_7977754 : Nat := 4983230072969 + 3 ^ 40 * 7977754 * 2
def baseEnd_7977754 : Nat := 4096422345328885234485983

theorem tailTrace_7977754 : CollatzResearch.WordTrace tailWord_7977754 prefixEnd_7977754 4096422345328885234485983 := by
  unfold tailWord_7977754
  simp only [CollatzResearch.WordTrace]
  refine ⟨72743148184991806188697079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193981728493311483169858877 72743148184991806188697079)
  ·
    refine ⟨109114722277487709283045619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72743148184991806188697079 109114722277487709283045619)
    ·
      refine ⟨163672083416231563924568429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109114722277487709283045619 163672083416231563924568429)
      ·
        refine ⟨61377031281086836471713161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163672083416231563924568429 61377031281086836471713161)
        ·
          refine ⟨46032773460815127353784871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61377031281086836471713161 46032773460815127353784871)
          ·
            refine ⟨69049160191222691030677307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46032773460815127353784871 69049160191222691030677307)
            ·
              refine ⟨103573740286834036546015961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69049160191222691030677307 103573740286834036546015961)
              ·
                refine ⟨77680305215125527409511971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103573740286834036546015961 77680305215125527409511971)
                ·
                  refine ⟨116520457822688291114267957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77680305215125527409511971 116520457822688291114267957)
                  ·
                    refine ⟨10923792920877027291962621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116520457822688291114267957 10923792920877027291962621)
                    ·
                      refine ⟨4096422345328885234485983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923792920877027291962621 4096422345328885234485983)
                      ·
                        rfl

theorem cell23_7977754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_7977754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977754 prefixEnd_7977754 := by exact prefixLift 7977754
  have htrace : WordTrace (prefixWord ++ tailWord_7977754) baseStart_7977754 baseEnd_7977754 := by
    simpa [prefixWord, tailWord_7977754, baseEnd_7977754] using wordTrace_append hprefix tailTrace_7977754
  have hstable : (prefixWord ++ tailWord_7977754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977754).length < 2 ^ (prefixWord ++ tailWord_7977754).sum := by decide
  have hdescent : baseEnd_7977754 < baseStart_7977754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977761 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 5]
def baseStart_7977761 : Nat := 118140960795 + 7977761 * 2 ^ 59
def prefixEnd_7977761 : Nat := 4983230072969 + 3 ^ 40 * 7977761 * 2
def baseEnd_7977761 : Nat := 455158437743718523010939

theorem tailTrace_7977761 : CollatzResearch.WordTrace tailWord_7977761 prefixEnd_7977761 455158437743718523010939 := by
  unfold tailWord_7977761
  simp only [CollatzResearch.WordTrace]
  refine ⟨290972848050941864950293137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193981898700627909966862091 290972848050941864950293137)
  ·
    refine ⟨218229636038206398712719853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290972848050941864950293137 218229636038206398712719853)
    ·
      refine ⟨81836113514327399517269945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218229636038206398712719853 81836113514327399517269945)
      ·
        refine ⟨61377085135745549637952459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81836113514327399517269945 61377085135745549637952459)
        ·
          refine ⟨92065627703618324456928689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61377085135745549637952459 92065627703618324456928689)
          ·
            refine ⟨69049220777713743342696517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92065627703618324456928689 69049220777713743342696517)
            ·
              refine ⟨12946728895821326876755597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69049220777713743342696517 12946728895821326876755597)
              ·
                refine ⟨4855023335932997578783349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12946728895821326876755597 4855023335932997578783349)
                ·
                  refine ⟨455158437743718523010939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855023335932997578783349 455158437743718523010939)
                  ·
                    rfl

theorem cell23_7977761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 5].length) (baseStart_7977761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977761 prefixEnd_7977761 := by exact prefixLift 7977761
  have htrace : WordTrace (prefixWord ++ tailWord_7977761) baseStart_7977761 baseEnd_7977761 := by
    simpa [prefixWord, tailWord_7977761, baseEnd_7977761] using wordTrace_append hprefix tailTrace_7977761
  have hstable : (prefixWord ++ tailWord_7977761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977761).length < 2 ^ (prefixWord ++ tailWord_7977761).sum := by decide
  have hdescent : baseEnd_7977761 < baseStart_7977761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977831 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_7977831 : Nat := 118140960795 + 7977831 * 2 ^ 59
def prefixEnd_7977831 : Nat := 4983230072969 + 3 ^ 40 * 7977831 * 2
def baseEnd_7977831 : Nat := 4096461883339281433223129

theorem tailTrace_7977831 : CollatzResearch.WordTrace tailWord_7977831 prefixEnd_7977831 4096461883339281433223129 := by
  unfold tailWord_7977831
  simp only [CollatzResearch.WordTrace]
  refine ⟨290975401160688266905341347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193983600773792177936894231 290975401160688266905341347)
  ·
    refine ⟨436463101741032400358012021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290975401160688266905341347 436463101741032400358012021)
    ·
      refine ⟨40918415788221787533563627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436463101741032400358012021 40918415788221787533563627)
      ·
        refine ⟨61377623682332681300345441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40918415788221787533563627 61377623682332681300345441)
        ·
          refine ⟨46033217761749510975259081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61377623682332681300345441 46033217761749510975259081)
          ·
            refine ⟨34524913321312133231444311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46033217761749510975259081 34524913321312133231444311)
            ·
              refine ⟨51787369981968199847166467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34524913321312133231444311 51787369981968199847166467)
              ·
                refine ⟨77681054972952299770749701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51787369981968199847166467 77681054972952299770749701)
                ·
                  refine ⟨14565197807428556207015569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77681054972952299770749701 14565197807428556207015569)
                  ·
                    refine ⟨10923898355571417155261677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14565197807428556207015569 10923898355571417155261677)
                    ·
                      refine ⟨4096461883339281433223129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10923898355571417155261677 4096461883339281433223129)
                      ·
                        rfl

theorem cell23_7977831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_7977831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977831 prefixEnd_7977831 := by exact prefixLift 7977831
  have htrace : WordTrace (prefixWord ++ tailWord_7977831) baseStart_7977831 baseEnd_7977831 := by
    simpa [prefixWord, tailWord_7977831, baseEnd_7977831] using wordTrace_append hprefix tailTrace_7977831
  have hstable : (prefixWord ++ tailWord_7977831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977831).length < 2 ^ (prefixWord ++ tailWord_7977831).sum := by decide
  have hdescent : baseEnd_7977831 < baseStart_7977831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977851 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 6]
def baseStart_7977851 : Nat := 118140960795 + 7977851 * 2 ^ 59
def prefixEnd_7977851 : Nat := 4983230072969 + 3 ^ 40 * 7977851 * 2
def baseEnd_7977851 : Nat := 455163572550263483885893

theorem tailTrace_7977851 : CollatzResearch.WordTrace tailWord_7977851 prefixEnd_7977851 455163572550263483885893 := by
  unfold tailWord_7977851
  simp only [CollatzResearch.WordTrace]
  refine ⟨290976130620615810321069407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193984087080410540214046271 290976130620615810321069407)
  ·
    refine ⟨436464195930923715481604111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290976130620615810321069407 436464195930923715481604111)
    ·
      refine ⟨654696293896385573222406167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436464195930923715481604111 654696293896385573222406167)
      ·
        refine ⟨982044440844578359833609251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654696293896385573222406167 982044440844578359833609251)
        ·
          refine ⟨1473066661266867539750413877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982044440844578359833609251 1473066661266867539750413877)
          ·
            refine ⟨138099999493768831851601301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1473066661266867539750413877 138099999493768831851601301)
            ·
              refine ⟨6473437476270413993043811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138099999493768831851601301 6473437476270413993043811)
              ·
                refine ⟨9710156214405620989565717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473437476270413993043811 9710156214405620989565717)
                ·
                  refine ⟨455163572550263483885893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9710156214405620989565717 455163572550263483885893)
                  ·
                    rfl

theorem cell23_7977851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 6].length) (baseStart_7977851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977851 prefixEnd_7977851 := by exact prefixLift 7977851
  have htrace : WordTrace (prefixWord ++ tailWord_7977851) baseStart_7977851 baseEnd_7977851 := by
    simpa [prefixWord, tailWord_7977851, baseEnd_7977851] using wordTrace_append hprefix tailTrace_7977851
  have hstable : (prefixWord ++ tailWord_7977851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977851).length < 2 ^ (prefixWord ++ tailWord_7977851).sum := by decide
  have hdescent : baseEnd_7977851 < baseStart_7977851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977888 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2]
def baseStart_7977888 : Nat := 118140960795 + 7977888 * 2 ^ 59
def prefixEnd_7977888 : Nat := 4983230072969 + 3 ^ 40 * 7977888 * 2
def baseEnd_7977888 : Nat := 4096491151736587710210367

theorem tailTrace_7977888 : CollatzResearch.WordTrace tailWord_7977888 prefixEnd_7977888 4096491151736587710210367 := by
  unfold tailWord_7977888
  simp only [CollatzResearch.WordTrace]
  refine ⟨145488740060740882820083159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193984986747654510426777545 145488740060740882820083159)
  ·
    refine ⟨218233110091111324230124739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145488740060740882820083159 218233110091111324230124739)
    ·
      refine ⟨327349665136666986345187109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218233110091111324230124739 327349665136666986345187109)
      ·
        refine ⟨61378062213125059939722583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327349665136666986345187109 61378062213125059939722583)
        ·
          refine ⟨92067093319687589909583875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61378062213125059939722583 92067093319687589909583875)
          ·
            refine ⟨138100639979531384864375813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92067093319687589909583875 138100639979531384864375813)
            ·
              refine ⟨25893869996162134662070465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138100639979531384864375813 25893869996162134662070465)
              ·
                refine ⟨19420402497121600996552849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25893869996162134662070465 19420402497121600996552849)
                ·
                  refine ⟨14565301872841200747414637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19420402497121600996552849 14565301872841200747414637)
                  ·
                    refine ⟨5461988202315450280280489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14565301872841200747414637 5461988202315450280280489)
                    ·
                      refine ⟨4096491151736587710210367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5461988202315450280280489 4096491151736587710210367)
                      ·
                        rfl

theorem cell23_7977888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_7977888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977888 prefixEnd_7977888 := by exact prefixLift 7977888
  have htrace : WordTrace (prefixWord ++ tailWord_7977888) baseStart_7977888 baseEnd_7977888 := by
    simpa [prefixWord, tailWord_7977888, baseEnd_7977888] using wordTrace_append hprefix tailTrace_7977888
  have hstable : (prefixWord ++ tailWord_7977888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977888).length < 2 ^ (prefixWord ++ tailWord_7977888).sum := by decide
  have hdescent : baseEnd_7977888 < baseStart_7977888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977918 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_7977918 : Nat := 118140960795 + 7977918 * 2 ^ 59
def prefixEnd_7977918 : Nat := 4983230072969 + 3 ^ 40 * 7977918 * 2
def baseEnd_7977918 : Nat := 4096506556156222592835229

theorem tailTrace_7977918 : CollatzResearch.WordTrace tailWord_7977918 prefixEnd_7977918 4096506556156222592835229 := by
  unfold tailWord_7977918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372321788921635095469801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193985716207582053842505605 36372321788921635095469801)
  ·
    refine ⟨27279241341691226321602351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36372321788921635095469801 27279241341691226321602351)
    ·
      refine ⟨40918862012536839482403527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27279241341691226321602351 40918862012536839482403527)
      ·
        refine ⟨61378293018805259223605291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40918862012536839482403527 61378293018805259223605291)
        ·
          refine ⟨92067439528207888835407937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61378293018805259223605291 92067439528207888835407937)
          ·
            refine ⟨69050579646155916626555953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92067439528207888835407937 69050579646155916626555953)
            ·
              refine ⟨51787934734616937469916965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69050579646155916626555953 51787934734616937469916965)
              ·
                refine ⟨9710237762740675775609431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51787934734616937469916965 9710237762740675775609431)
                ·
                  refine ⟨14565356644111013663414147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710237762740675775609431 14565356644111013663414147)
                  ·
                    refine ⟨21848034966166520495121221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14565356644111013663414147 21848034966166520495121221)
                    ·
                      refine ⟨4096506556156222592835229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21848034966166520495121221 4096506556156222592835229)
                      ·
                        rfl

theorem cell23_7977918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_7977918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977918 prefixEnd_7977918 := by exact prefixLift 7977918
  have htrace : WordTrace (prefixWord ++ tailWord_7977918) baseStart_7977918 baseEnd_7977918 := by
    simpa [prefixWord, tailWord_7977918, baseEnd_7977918] using wordTrace_append hprefix tailTrace_7977918
  have hstable : (prefixWord ++ tailWord_7977918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977918).length < 2 ^ (prefixWord ++ tailWord_7977918).sum := by decide
  have hdescent : baseEnd_7977918 < baseStart_7977918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977931 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4]
def baseStart_7977931 : Nat := 118140960795 + 7977931 * 2 ^ 59
def prefixEnd_7977931 : Nat := 4983230072969 + 3 ^ 40 * 7977931 * 2
def baseEnd_7977931 : Nat := 4096513231404731041972669

theorem tailTrace_7977931 : CollatzResearch.WordTrace tailWord_7977931 prefixEnd_7977931 4096513231404731041972669 := by
  unfold tailWord_7977931
  simp only [CollatzResearch.WordTrace]
  refine ⟨290979048460325983983981647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193986032306883989322654431 290979048460325983983981647)
  ·
    refine ⟨436468572690488975975972471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290979048460325983983981647 436468572690488975975972471)
    ·
      refine ⟨654702859035733463963958707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436468572690488975975972471 654702859035733463963958707)
      ·
        refine ⟨982054288553600195945938061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654702859035733463963958707 982054288553600195945938061)
        ·
          refine ⟨368270358207600073479726773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 982054288553600195945938061 368270358207600073479726773)
          ·
            refine ⟨34525346081962506888724385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368270358207600073479726773 34525346081962506888724385)
            ·
              refine ⟨25894009561471880166543289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34525346081962506888724385 25894009561471880166543289)
              ·
                refine ⟨19420507171103910124907467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25894009561471880166543289 19420507171103910124907467)
                ·
                  refine ⟨29130760756655865187361201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19420507171103910124907467 29130760756655865187361201)
                  ·
                    refine ⟨21848070567491898890520901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29130760756655865187361201 21848070567491898890520901)
                    ·
                      refine ⟨4096513231404731041972669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21848070567491898890520901 4096513231404731041972669)
                      ·
                        rfl

theorem cell23_7977931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_7977931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977931 prefixEnd_7977931 := by exact prefixLift 7977931
  have htrace : WordTrace (prefixWord ++ tailWord_7977931) baseStart_7977931 baseEnd_7977931 := by
    simpa [prefixWord, tailWord_7977931, baseEnd_7977931] using wordTrace_append hprefix tailTrace_7977931
  have hstable : (prefixWord ++ tailWord_7977931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977931).length < 2 ^ (prefixWord ++ tailWord_7977931).sum := by decide
  have hdescent : baseEnd_7977931 < baseStart_7977931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977935 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 1, 1, 4]
def baseStart_7977935 : Nat := 118140960795 + 7977935 * 2 ^ 59
def prefixEnd_7977935 : Nat := 4983230072969 + 3 ^ 40 * 7977935 * 2
def baseEnd_7977935 : Nat := 4096515285327349026322651

theorem tailTrace_7977935 : CollatzResearch.WordTrace tailWord_7977935 prefixEnd_7977935 4096515285327349026322651 := by
  unfold tailWord_7977935
  simp only [CollatzResearch.WordTrace]
  refine ⟨290979194352311492667127259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193986129568207661778084839 290979194352311492667127259)
  ·
    refine ⟨436468791528467239000690889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290979194352311492667127259 436468791528467239000690889)
    ·
      refine ⟨327351593646350429250518167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436468791528467239000690889 327351593646350429250518167)
      ·
        refine ⟨491027390469525643875777251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327351593646350429250518167 491027390469525643875777251)
        ·
          refine ⟨736541085704288465813665877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491027390469525643875777251 736541085704288465813665877)
          ·
            refine ⟨8631340848097130458753897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 736541085704288465813665877 8631340848097130458753897)
            ·
              refine ⟨6473505636072847844065423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8631340848097130458753897 6473505636072847844065423)
              ·
                refine ⟨9710258454109271766098135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473505636072847844065423 9710258454109271766098135)
                ·
                  refine ⟨14565387681163907649147203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710258454109271766098135 14565387681163907649147203)
                  ·
                    refine ⟨21848081521745861473720805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14565387681163907649147203 21848081521745861473720805)
                    ·
                      refine ⟨4096515285327349026322651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21848081521745861473720805 4096515285327349026322651)
                      ·
                        rfl

theorem cell23_7977935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 1, 4].length) (baseStart_7977935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977935 prefixEnd_7977935 := by exact prefixLift 7977935
  have htrace : WordTrace (prefixWord ++ tailWord_7977935) baseStart_7977935 baseEnd_7977935 := by
    simpa [prefixWord, tailWord_7977935, baseEnd_7977935] using wordTrace_append hprefix tailTrace_7977935
  have hstable : (prefixWord ++ tailWord_7977935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977935).length < 2 ^ (prefixWord ++ tailWord_7977935).sum := by decide
  have hdescent : baseEnd_7977935 < baseStart_7977935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977941 : List Nat := [1, 3, 2, 3, 3, 1, 10]
def baseStart_7977941 : Nat := 118140960795 + 7977941 * 2 ^ 59
def prefixEnd_7977941 : Nat := 4983230072969 + 3 ^ 40 * 7977941 * 2
def baseEnd_7977941 : Nat := 50574300817423160528983

theorem tailTrace_7977941 : CollatzResearch.WordTrace tailWord_7977941 prefixEnd_7977941 50574300817423160528983 := by
  unfold tailWord_7977941
  simp only [CollatzResearch.WordTrace]
  refine ⟨290979413190289755691845677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193986275460193170461230451 290979413190289755691845677)
  ·
    refine ⟨109117279946358658384442129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290979413190289755691845677 109117279946358658384442129)
    ·
      refine ⟨81837959959768993788331597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109117279946358658384442129 81837959959768993788331597)
      ·
        refine ⟨30689234984913372670624349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81837959959768993788331597 30689234984913372670624349)
        ·
          refine ⟨11508463119342514751484131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30689234984913372670624349 11508463119342514751484131)
          ·
            refine ⟨17262694679013772127226197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508463119342514751484131 17262694679013772127226197)
            ·
              refine ⟨50574300817423160528983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17262694679013772127226197 50574300817423160528983)
              ·
                rfl

theorem cell23_7977941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 10].length) (baseStart_7977941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977941 prefixEnd_7977941 := by exact prefixLift 7977941
  have htrace : WordTrace (prefixWord ++ tailWord_7977941) baseStart_7977941 baseEnd_7977941 := by
    simpa [prefixWord, tailWord_7977941, baseEnd_7977941] using wordTrace_append hprefix tailTrace_7977941
  have hstable : (prefixWord ++ tailWord_7977941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977941).length < 2 ^ (prefixWord ++ tailWord_7977941).sum := by decide
  have hdescent : baseEnd_7977941 < baseStart_7977941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977945 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_7977945 : Nat := 118140960795 + 7977945 * 2 ^ 59
def prefixEnd_7977945 : Nat := 4983230072969 + 3 ^ 40 * 7977945 * 2
def baseEnd_7977945 : Nat := 1365506806711297995732535

theorem tailTrace_7977945 : CollatzResearch.WordTrace tailWord_7977945 prefixEnd_7977945 1365506806711297995732535 := by
  unfold tailWord_7977945
  simp only [CollatzResearch.WordTrace]
  refine ⟨290979559082275264374991289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193986372721516842916660859 290979559082275264374991289)
  ·
    refine ⟨218234669311706448281243467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290979559082275264374991289 218234669311706448281243467)
    ·
      refine ⟨327352003967559672421865201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218234669311706448281243467 327352003967559672421865201)
      ·
        refine ⟨245514002975669754316398901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327352003967559672421865201 245514002975669754316398901)
        ·
          refine ⟨23016937778969039467162397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245514002975669754316398901 23016937778969039467162397)
          ·
            refine ⟨8631351667113389800185899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23016937778969039467162397 8631351667113389800185899)
            ·
              refine ⟨12947027500670084700278849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631351667113389800185899 12947027500670084700278849)
              ·
                refine ⟨9710270625502563525209137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12947027500670084700278849 9710270625502563525209137)
                ·
                  refine ⟨7282702969126922643906853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710270625502563525209137 7282702969126922643906853)
                  ·
                    refine ⟨1365506806711297995732535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282702969126922643906853 1365506806711297995732535)
                    ·
                      rfl

theorem cell23_7977945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_7977945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977945 prefixEnd_7977945 := by exact prefixLift 7977945
  have htrace : WordTrace (prefixWord ++ tailWord_7977945) baseStart_7977945 baseEnd_7977945 := by
    simpa [prefixWord, tailWord_7977945, baseEnd_7977945] using wordTrace_append hprefix tailTrace_7977945
  have hstable : (prefixWord ++ tailWord_7977945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977945).length < 2 ^ (prefixWord ++ tailWord_7977945).sum := by decide
  have hdescent : baseEnd_7977945 < baseStart_7977945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977978 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_7977978 : Nat := 118140960795 + 7977978 * 2 ^ 59
def prefixEnd_7977978 : Nat := 4983230072969 + 3 ^ 40 * 7977978 * 2
def baseEnd_7977978 : Nat := 4096537364995492358084953

theorem tailTrace_7977978 : CollatzResearch.WordTrace tailWord_7977978 prefixEnd_7977978 4096537364995492358084953 := by
  unfold tailWord_7977978
  simp only [CollatzResearch.WordTrace]
  refine ⟨72745190672788927752735647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193987175127437140673961725 72745190672788927752735647)
  ·
    refine ⟨109117786009183391629103471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72745190672788927752735647 109117786009183391629103471)
    ·
      refine ⟨163676679013775087443655207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109117786009183391629103471 163676679013775087443655207)
      ·
        refine ⟨245515018520662631165482811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163676679013775087443655207 245515018520662631165482811)
        ·
          refine ⟨368272527780993946748224217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245515018520662631165482811 368272527780993946748224217)
          ·
            refine ⟨276204395835745460061168163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368272527780993946748224217 276204395835745460061168163)
            ·
              refine ⟨414306593753618190091752245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276204395835745460061168163 414306593753618190091752245)
              ·
                refine ⟨38841243164401705321101773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414306593753618190091752245 38841243164401705321101773)
                ·
                  refine ⟨14565466186650639495413165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38841243164401705321101773 14565466186650639495413165)
                  ·
                    refine ⟨5462049819993989810779937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14565466186650639495413165 5462049819993989810779937)
                    ·
                      refine ⟨4096537364995492358084953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462049819993989810779937 4096537364995492358084953)
                      ·
                        rfl

theorem cell23_7977978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_7977978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977978 prefixEnd_7977978 := by exact prefixLift 7977978
  have htrace : WordTrace (prefixWord ++ tailWord_7977978) baseStart_7977978 baseEnd_7977978 := by
    simpa [prefixWord, tailWord_7977978, baseEnd_7977978] using wordTrace_append hprefix tailTrace_7977978
  have hstable : (prefixWord ++ tailWord_7977978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977978).length < 2 ^ (prefixWord ++ tailWord_7977978).sum := by decide
  have hdescent : baseEnd_7977978 < baseStart_7977978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7977995 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 1, 3, 2]
def baseStart_7977995 : Nat := 118140960795 + 7977995 * 2 ^ 59
def prefixEnd_7977995 : Nat := 4983230072969 + 3 ^ 40 * 7977995 * 2
def baseEnd_7977995 : Nat := 4096546094166618791572375

theorem tailTrace_7977995 : CollatzResearch.WordTrace tailWord_7977995 prefixEnd_7977995 4096546094166618791572375 := by
  unfold tailWord_7977995
  simp only [CollatzResearch.WordTrace]
  refine ⟨290981382732094122914311439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193987588488062748609540959 290981382732094122914311439)
  ·
    refine ⟨436472074098141184371467159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290981382732094122914311439 436472074098141184371467159)
    ·
      refine ⟨654708111147211776557200739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436472074098141184371467159 654708111147211776557200739)
      ·
        refine ⟨982062166720817664835801109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654708111147211776557200739 982062166720817664835801109)
        ·
          refine ⟨46034164065038328039178177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 982062166720817664835801109 46034164065038328039178177)
          ·
            refine ⟨34525623048778746029383633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46034164065038328039178177 34525623048778746029383633)
            ·
              refine ⟨25894217286584059522037725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34525623048778746029383633 25894217286584059522037725)
              ·
                refine ⟨9710331482469022320764147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25894217286584059522037725 9710331482469022320764147)
                ·
                  refine ⟨14565497223703533481146221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710331482469022320764147 14565497223703533481146221)
                  ·
                    refine ⟨5462061458888825055429833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14565497223703533481146221 5462061458888825055429833)
                    ·
                      refine ⟨4096546094166618791572375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462061458888825055429833 4096546094166618791572375)
                      ·
                        rfl

theorem cell23_7977995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3, 2].length) (baseStart_7977995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7977995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7977995 prefixEnd_7977995 := by exact prefixLift 7977995
  have htrace : WordTrace (prefixWord ++ tailWord_7977995) baseStart_7977995 baseEnd_7977995 := by
    simpa [prefixWord, tailWord_7977995, baseEnd_7977995] using wordTrace_append hprefix tailTrace_7977995
  have hstable : (prefixWord ++ tailWord_7977995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7977995).length < 2 ^ (prefixWord ++ tailWord_7977995).sum := by decide
  have hdescent : baseEnd_7977995 < baseStart_7977995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7977995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978021 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_7978021 : Nat := 118140960795 + 7978021 * 2 ^ 59
def prefixEnd_7978021 : Nat := 4983230072969 + 3 ^ 40 * 7978021 * 2
def baseEnd_7978021 : Nat := 4096559444663635689847255

theorem tailTrace_7978021 : CollatzResearch.WordTrace tailWord_7978021 prefixEnd_7978021 4096559444663635689847255 := by
  unfold tailWord_7978021
  simp only [CollatzResearch.WordTrace]
  refine ⟨290982331029999929354757917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193988220686666619569838611 290982331029999929354757917)
  ·
    refine ⟨109118374136249973508034219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290982331029999929354757917 109118374136249973508034219)
    ·
      refine ⟨163677561204374960262051329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109118374136249973508034219 163677561204374960262051329)
      ·
        refine ⟨122758170903281220196538497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163677561204374960262051329 122758170903281220196538497)
        ·
          refine ⟨92068628177460915147403873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122758170903281220196538497 92068628177460915147403873)
          ·
            refine ⟨69051471133095686360552905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92068628177460915147403873 69051471133095686360552905)
            ·
              refine ⟨51788603349821764770414679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69051471133095686360552905 51788603349821764770414679)
              ·
                refine ⟨77682905024732647155622019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51788603349821764770414679 77682905024732647155622019)
                ·
                  refine ⟨116524357537098970733433029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77682905024732647155622019 116524357537098970733433029)
                  ·
                    refine ⟨21848317038206057012518693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116524357537098970733433029 21848317038206057012518693)
                    ·
                      refine ⟨4096559444663635689847255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21848317038206057012518693 4096559444663635689847255)
                      ·
                        rfl

theorem cell23_7978021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_7978021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978021 prefixEnd_7978021 := by exact prefixLift 7978021
  have htrace : WordTrace (prefixWord ++ tailWord_7978021) baseStart_7978021 baseEnd_7978021 := by
    simpa [prefixWord, tailWord_7978021, baseEnd_7978021] using wordTrace_append hprefix tailTrace_7978021
  have hstable : (prefixWord ++ tailWord_7978021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978021).length < 2 ^ (prefixWord ++ tailWord_7978021).sum := by decide
  have hdescent : baseEnd_7978021 < baseStart_7978021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978048 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 5]
def baseStart_7978048 : Nat := 118140960795 + 7978048 * 2 ^ 59
def prefixEnd_7978048 : Nat := 4983230072969 + 3 ^ 40 * 7978048 * 2
def baseEnd_7978048 : Nat := 455174812071256342689959

theorem tailTrace_7978048 : CollatzResearch.WordTrace tailWord_7978048 prefixEnd_7978048 455174812071256342689959 := by
  unfold tailWord_7978048
  simp only [CollatzResearch.WordTrace]
  refine ⟨145491657900451056482995399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193988877200601408643993865 145491657900451056482995399)
  ·
    refine ⟨218237486850676584724493099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145491657900451056482995399 218237486850676584724493099)
    ·
      refine ⟨327356230276014877086739649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218237486850676584724493099 327356230276014877086739649)
      ·
        refine ⟨245517172707011157815054737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327356230276014877086739649 245517172707011157815054737)
        ·
          refine ⟨184137879530258368361291053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245517172707011157815054737 184137879530258368361291053)
          ·
            refine ⟨69051704823846888135484145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184137879530258368361291053 69051704823846888135484145)
            ·
              refine ⟨51788778617885166101613109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69051704823846888135484145 51788778617885166101613109)
              ·
                refine ⟨4855197995426734322026229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51788778617885166101613109 4855197995426734322026229)
                ·
                  refine ⟨455174812071256342689959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855197995426734322026229 455174812071256342689959)
                  ·
                    rfl

theorem cell23_7978048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 5].length) (baseStart_7978048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978048 prefixEnd_7978048 := by exact prefixLift 7978048
  have htrace : WordTrace (prefixWord ++ tailWord_7978048) baseStart_7978048 baseEnd_7978048 := by
    simpa [prefixWord, tailWord_7978048, baseEnd_7978048] using wordTrace_append hprefix tailTrace_7978048
  have hstable : (prefixWord ++ tailWord_7978048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978048).length < 2 ^ (prefixWord ++ tailWord_7978048).sum := by decide
  have hdescent : baseEnd_7978048 < baseStart_7978048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978065 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 5]
def baseStart_7978065 : Nat := 118140960795 + 7978065 * 2 ^ 59
def prefixEnd_7978065 : Nat := 4983230072969 + 3 ^ 40 * 7978065 * 2
def baseEnd_7978065 : Nat := 455175781979159279744117

theorem tailTrace_7978065 : CollatzResearch.WordTrace tailWord_7978065 prefixEnd_7978065 455175781979159279744117 := by
  unfold tailWord_7978065
  simp only [CollatzResearch.WordTrace]
  refine ⟨290983935841840524869359649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193989290561227016579573099 290983935841840524869359649)
  ·
    refine ⟨218237951881380393652019737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290983935841840524869359649 218237951881380393652019737)
    ·
      refine ⟨163678463911035295239014803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218237951881380393652019737 163678463911035295239014803)
      ·
        refine ⟨245517695866552942858522205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163678463911035295239014803 245517695866552942858522205)
        ·
          refine ⟨92069135949957353571945827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245517695866552942858522205 92069135949957353571945827)
          ·
            refine ⟨138103703924936030357918741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92069135949957353571945827 138103703924936030357918741)
            ·
              refine ⟨6473611121481376423027441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138103703924936030357918741 6473611121481376423027441)
              ·
                refine ⟨4855208341111032317270581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6473611121481376423027441 4855208341111032317270581)
                ·
                  refine ⟨455175781979159279744117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855208341111032317270581 455175781979159279744117)
                  ·
                    rfl

theorem cell23_7978065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 5].length) (baseStart_7978065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978065 prefixEnd_7978065 := by exact prefixLift 7978065
  have htrace : WordTrace (prefixWord ++ tailWord_7978065) baseStart_7978065 baseEnd_7978065 := by
    simpa [prefixWord, tailWord_7978065, baseEnd_7978065] using wordTrace_append hprefix tailTrace_7978065
  have hstable : (prefixWord ++ tailWord_7978065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978065).length < 2 ^ (prefixWord ++ tailWord_7978065).sum := by decide
  have hdescent : baseEnd_7978065 < baseStart_7978065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978098 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_7978098 : Nat := 118140960795 + 7978098 * 2 ^ 59
def prefixEnd_7978098 : Nat := 4983230072969 + 3 ^ 40 * 7978098 * 2
def baseEnd_7978098 : Nat := 4096598982674031888584401

theorem tailTrace_7978098 : CollatzResearch.WordTrace tailWord_7978098 prefixEnd_7978098 4096598982674031888584401 := by
  unfold tailWord_7978098
  simp only [CollatzResearch.WordTrace]
  refine ⟨72746284862680242876327737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193990092967147314336873965 72746284862680242876327737)
  ·
    refine ⟨54559713647010182157245803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72746284862680242876327737 54559713647010182157245803)
    ·
      refine ⟨81839570470515273235868705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54559713647010182157245803 81839570470515273235868705)
      ·
        refine ⟨61379677852886454926901529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81839570470515273235868705 61379677852886454926901529)
        ·
          refine ⟨46034758389664841195176147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61379677852886454926901529 46034758389664841195176147)
          ·
            refine ⟨69052137584497261792764221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46034758389664841195176147 69052137584497261792764221)
            ·
              refine ⟨25894551594186473172286583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69052137584497261792764221 25894551594186473172286583)
              ·
                refine ⟨38841827391279709758429875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25894551594186473172286583 38841827391279709758429875)
                ·
                  refine ⟨58262741086919564637644813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38841827391279709758429875 58262741086919564637644813)
                  ·
                    refine ⟨21848527907594836739116805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58262741086919564637644813 21848527907594836739116805)
                    ·
                      refine ⟨4096598982674031888584401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21848527907594836739116805 4096598982674031888584401)
                      ·
                        rfl

theorem cell23_7978098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_7978098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978098 prefixEnd_7978098 := by exact prefixLift 7978098
  have htrace : WordTrace (prefixWord ++ tailWord_7978098) baseStart_7978098 baseEnd_7978098 := by
    simpa [prefixWord, tailWord_7978098, baseEnd_7978098] using wordTrace_append hprefix tailTrace_7978098
  have hstable : (prefixWord ++ tailWord_7978098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978098).length < 2 ^ (prefixWord ++ tailWord_7978098).sum := by decide
  have hdescent : baseEnd_7978098 < baseStart_7978098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978108 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_7978108 : Nat := 118140960795 + 7978108 * 2 ^ 59
def prefixEnd_7978108 : Nat := 4983230072969 + 3 ^ 40 * 7978108 * 2
def baseEnd_7978108 : Nat := 1365534705826858949819785

theorem tailTrace_7978108 : CollatzResearch.WordTrace tailWord_7978108 prefixEnd_7978108 1365534705826858949819785 := by
  unfold tailWord_7978108
  simp only [CollatzResearch.WordTrace]
  refine ⟨145492752090342371606587489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193990336120456495475449985 145492752090342371606587489)
  ·
    refine ⟨109119564067756778704940617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145492752090342371606587489 109119564067756778704940617)
    ·
      refine ⟨81839673050817584028705463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109119564067756778704940617 81839673050817584028705463)
      ·
        refine ⟨122759509576226376043058195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81839673050817584028705463 122759509576226376043058195)
        ·
          refine ⟨184139264364339564064587293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122759509576226376043058195 184139264364339564064587293)
          ·
            refine ⟨69052224136627336524220235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184139264364339564064587293 69052224136627336524220235)
            ·
              refine ⟨103578336204941004786330353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69052224136627336524220235 103578336204941004786330353)
              ·
                refine ⟨77683752153705753589747765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103578336204941004786330353 77683752153705753589747765)
                ·
                  refine ⟨7282851764409914399038853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77683752153705753589747765 7282851764409914399038853)
                  ·
                    refine ⟨1365534705826858949819785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282851764409914399038853 1365534705826858949819785)
                    ·
                      rfl

theorem cell23_7978108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_7978108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978108 prefixEnd_7978108 := by exact prefixLift 7978108
  have htrace : WordTrace (prefixWord ++ tailWord_7978108) baseStart_7978108 baseEnd_7978108 := by
    simpa [prefixWord, tailWord_7978108, baseEnd_7978108] using wordTrace_append hprefix tailTrace_7978108
  have hstable : (prefixWord ++ tailWord_7978108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978108).length < 2 ^ (prefixWord ++ tailWord_7978108).sum := by decide
  have hdescent : baseEnd_7978108 < baseStart_7978108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978110 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7978110 : Nat := 118140960795 + 7978110 * 2 ^ 59
def prefixEnd_7978110 : Nat := 4983230072969 + 3 ^ 40 * 7978110 * 2
def baseEnd_7978110 : Nat := 4096605144441885841634347

theorem tailTrace_7978110 : CollatzResearch.WordTrace tailWord_7978110 prefixEnd_7978110 4096605144441885841634347 := by
  unfold tailWord_7978110
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373197140834687194343473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193990384751118331703165189 36373197140834687194343473)
  ·
    refine ⟨27279897855626015395757605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36373197140834687194343473 27279897855626015395757605)
    ·
      refine ⟨5114980847929877886704551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27279897855626015395757605 5114980847929877886704551)
      ·
        refine ⟨7672471271894816830056827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5114980847929877886704551 7672471271894816830056827)
        ·
          refine ⟨11508706907842225245085241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672471271894816830056827 11508706907842225245085241)
          ·
            refine ⟨8631530180881668933813931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11508706907842225245085241 8631530180881668933813931)
            ·
              refine ⟨12947295271322503400720897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631530180881668933813931 12947295271322503400720897)
              ·
                refine ⟨9710471453491877550540673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12947295271322503400720897 9710471453491877550540673)
                ·
                  refine ⟨7282853590118908162905505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710471453491877550540673 7282853590118908162905505)
                  ·
                    refine ⟨5462140192589181122179129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282853590118908162905505 5462140192589181122179129)
                    ·
                      refine ⟨4096605144441885841634347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462140192589181122179129 4096605144441885841634347)
                      ·
                        rfl

theorem cell23_7978110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7978110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978110 prefixEnd_7978110 := by exact prefixLift 7978110
  have htrace : WordTrace (prefixWord ++ tailWord_7978110) baseStart_7978110 baseEnd_7978110 := by
    simpa [prefixWord, tailWord_7978110, baseEnd_7978110] using wordTrace_append hprefix tailTrace_7978110
  have hstable : (prefixWord ++ tailWord_7978110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978110).length < 2 ^ (prefixWord ++ tailWord_7978110).sum := by decide
  have hdescent : baseEnd_7978110 < baseStart_7978110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978111 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_7978111 : Nat := 118140960795 + 7978111 * 2 ^ 59
def prefixEnd_7978111 : Nat := 4983230072969 + 3 ^ 40 * 7978111 * 2
def baseEnd_7978111 : Nat := 4096605657922540337721841

theorem tailTrace_7978111 : CollatzResearch.WordTrace tailWord_7978111 prefixEnd_7978111 4096605657922540337721841 := by
  unfold tailWord_7978111
  simp only [CollatzResearch.WordTrace]
  refine ⟨290985613599673874725534187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193990409066449249817022791 290985613599673874725534187)
  ·
    refine ⟨436478420399510812088301281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290985613599673874725534187 436478420399510812088301281)
    ·
      refine ⟨327358815299633109066225961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436478420399510812088301281 327358815299633109066225961)
      ·
        refine ⟨245519111474724831799669471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327358815299633109066225961 245519111474724831799669471)
        ·
          refine ⟨368278667212087247699504207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245519111474724831799669471 368278667212087247699504207)
          ·
            refine ⟨552418000818130871549256311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368278667212087247699504207 552418000818130871549256311)
            ·
              refine ⟨828627001227196307323884467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552418000818130871549256311 828627001227196307323884467)
              ·
                refine ⟨1242940501840794460985826701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828627001227196307323884467 1242940501840794460985826701)
                ·
                  refine ⟨466102688190297922869685013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242940501840794460985826701 466102688190297922869685013)
                  ·
                    refine ⟨21848563508920215134516485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 466102688190297922869685013 21848563508920215134516485)
                    ·
                      refine ⟨4096605657922540337721841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21848563508920215134516485 4096605657922540337721841)
                      ·
                        rfl

theorem cell23_7978111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_7978111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978111 prefixEnd_7978111 := by exact prefixLift 7978111
  have htrace : WordTrace (prefixWord ++ tailWord_7978111) baseStart_7978111 baseEnd_7978111 := by
    simpa [prefixWord, tailWord_7978111, baseEnd_7978111] using wordTrace_append hprefix tailTrace_7978111
  have hstable : (prefixWord ++ tailWord_7978111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978111).length < 2 ^ (prefixWord ++ tailWord_7978111).sum := by decide
  have hdescent : baseEnd_7978111 < baseStart_7978111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978142 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7978142 : Nat := 118140960795 + 7978142 * 2 ^ 59
def prefixEnd_7978142 : Nat := 4983230072969 + 3 ^ 40 * 7978142 * 2
def baseEnd_7978142 : Nat := 1365540525274276572144733

theorem tailTrace_7978142 : CollatzResearch.WordTrace tailWord_7978142 prefixEnd_7978142 1365540525274276572144733 := by
  unfold tailWord_7978142
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373343032820195877489085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193991162841707711346608453 36373343032820195877489085)
  ·
    refine ⟨13640003637307573454058407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36373343032820195877489085 13640003637307573454058407)
    ·
      refine ⟨20460005455961360181087611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13640003637307573454058407 20460005455961360181087611)
      ·
        refine ⟨30690008183942040271631417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20460005455961360181087611 30690008183942040271631417)
        ·
          refine ⟨23017506137956530203723563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30690008183942040271631417 23017506137956530203723563)
          ·
            refine ⟨34526259206934795305585345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23017506137956530203723563 34526259206934795305585345)
            ·
              refine ⟨25894694405201096479189009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34526259206934795305585345 25894694405201096479189009)
              ·
                refine ⟨19421020803900822359391757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25894694405201096479189009 19421020803900822359391757)
                ·
                  refine ⟨7282882801462808384771909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19421020803900822359391757 7282882801462808384771909)
                  ·
                    refine ⟨1365540525274276572144733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282882801462808384771909 1365540525274276572144733)
                    ·
                      rfl

theorem cell23_7978142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7978142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978142 prefixEnd_7978142 := by exact prefixLift 7978142
  have htrace : WordTrace (prefixWord ++ tailWord_7978142) baseStart_7978142 baseEnd_7978142 := by
    simpa [prefixWord, tailWord_7978142, baseEnd_7978142] using wordTrace_append hprefix tailTrace_7978142
  have hstable : (prefixWord ++ tailWord_7978142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978142).length < 2 ^ (prefixWord ++ tailWord_7978142).sum := by decide
  have hdescent : baseEnd_7978142 < baseStart_7978142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978175 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 4, 3, 2]
def baseStart_7978175 : Nat := 118140960795 + 7978175 * 2 ^ 59
def prefixEnd_7978175 : Nat := 4983230072969 + 3 ^ 40 * 7978175 * 2
def baseEnd_7978175 : Nat := 4096638520684428087321547

theorem tailTrace_7978175 : CollatzResearch.WordTrace tailWord_7978175 prefixEnd_7978175 4096638520684428087321547 := by
  unfold tailWord_7978175
  simp only [CollatzResearch.WordTrace]
  refine ⟨290987947871442013655863979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193991965247628009103909319 290987947871442013655863979)
  ·
    refine ⟨436481921807163020483795969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290987947871442013655863979 436481921807163020483795969)
    ·
      refine ⟨327361441355372265362846977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436481921807163020483795969 327361441355372265362846977)
      ·
        refine ⟨245521081016529199022135233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327361441355372265362846977 245521081016529199022135233)
        ·
          refine ⟨184140810762396899266601425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245521081016529199022135233 184140810762396899266601425)
          ·
            refine ⟨138105608071797674449951069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184140810762396899266601425 138105608071797674449951069)
            ·
              refine ⟨51789603026924127918731651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138105608071797674449951069 51789603026924127918731651)
              ·
                refine ⟨77684404540386191878097477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51789603026924127918731651 77684404540386191878097477)
                ·
                  refine ⟨14565825851322410977143277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77684404540386191878097477 14565825851322410977143277)
                  ·
                    refine ⟨5462184694245904116428729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14565825851322410977143277 5462184694245904116428729)
                    ·
                      refine ⟨4096638520684428087321547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462184694245904116428729 4096638520684428087321547)
                      ·
                        rfl

theorem cell23_7978175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_7978175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978175 prefixEnd_7978175 := by exact prefixLift 7978175
  have htrace : WordTrace (prefixWord ++ tailWord_7978175) baseStart_7978175 baseEnd_7978175 := by
    simpa [prefixWord, tailWord_7978175, baseEnd_7978175] using wordTrace_append hprefix tailTrace_7978175
  have hstable : (prefixWord ++ tailWord_7978175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978175).length < 2 ^ (prefixWord ++ tailWord_7978175).sum := by decide
  have hdescent : baseEnd_7978175 < baseStart_7978175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978189 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7978189 : Nat := 118140960795 + 7978189 * 2 ^ 59
def prefixEnd_7978189 : Nat := 4983230072969 + 3 ^ 40 * 7978189 * 2
def baseEnd_7978189 : Nat := 455182856601510114727387

theorem tailTrace_7978189 : CollatzResearch.WordTrace tailWord_7978189 prefixEnd_7978189 455182856601510114727387 := by
  unfold tailWord_7978189
  simp only [CollatzResearch.WordTrace]
  refine ⟨290988458493391294046873621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193992305662260862697915747 290988458493391294046873621)
  ·
    refine ⟨13640083991877716908447201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 290988458493391294046873621 13640083991877716908447201)
    ·
      refine ⟨10230062993908287681335401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13640083991877716908447201 10230062993908287681335401)
      ·
        refine ⟨7672547245431215761001551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230062993908287681335401 7672547245431215761001551)
        ·
          refine ⟨11508820868146823641502327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672547245431215761001551 11508820868146823641502327)
          ·
            refine ⟨17263231302220235462253491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508820868146823641502327 17263231302220235462253491)
            ·
              refine ⟨25894846953330353193380237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17263231302220235462253491 25894846953330353193380237)
              ·
                refine ⟨9710567607498882447517589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25894846953330353193380237 9710567607498882447517589)
                ·
                  refine ⟨455182856601510114727387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9710567607498882447517589 455182856601510114727387)
                  ·
                    rfl

theorem cell23_7978189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7978189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978189 prefixEnd_7978189 := by exact prefixLift 7978189
  have htrace : WordTrace (prefixWord ++ tailWord_7978189) baseStart_7978189 baseEnd_7978189 := by
    simpa [prefixWord, tailWord_7978189, baseEnd_7978189] using wordTrace_append hprefix tailTrace_7978189
  have hstable : (prefixWord ++ tailWord_7978189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978189).length < 2 ^ (prefixWord ++ tailWord_7978189).sum := by decide
  have hdescent : baseEnd_7978189 < baseStart_7978189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978255 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 3]
def baseStart_7978255 : Nat := 118140960795 + 7978255 * 2 ^ 59
def prefixEnd_7978255 : Nat := 4983230072969 + 3 ^ 40 * 7978255 * 2
def baseEnd_7978255 : Nat := 4096679599136787774321179

theorem tailTrace_7978255 : CollatzResearch.WordTrace tailWord_7978255 prefixEnd_7978255 4096679599136787774321179 := by
  unfold tailWord_7978255
  simp only [CollatzResearch.WordTrace]
  refine ⟨290990865711152187318776219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193993910474101458212517479 290990865711152187318776219)
  ·
    refine ⟨436486298566728280978164329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290990865711152187318776219 436486298566728280978164329)
    ·
      refine ⟨327364723925046210733623247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436486298566728280978164329 327364723925046210733623247)
      ·
        refine ⟨491047085887569316100434871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327364723925046210733623247 491047085887569316100434871)
        ·
          refine ⟨736570628831353974150652307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491047085887569316100434871 736570628831353974150652307)
          ·
            refine ⟨1104855943247030961225978461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736570628831353974150652307 1104855943247030961225978461)
            ·
              refine ⟨414320978717636610459741923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1104855943247030961225978461 414320978717636610459741923)
              ·
                refine ⟨621481468076454915689612885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414320978717636610459741923 621481468076454915689612885)
                ·
                  refine ⟨7282985954020956043237651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 621481468076454915689612885 7282985954020956043237651)
                  ·
                    refine ⟨10924478931031434064856477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7282985954020956043237651 10924478931031434064856477)
                    ·
                      refine ⟨4096679599136787774321179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924478931031434064856477 4096679599136787774321179)
                      ·
                        rfl

theorem cell23_7978255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_7978255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978255 prefixEnd_7978255 := by exact prefixLift 7978255
  have htrace : WordTrace (prefixWord ++ tailWord_7978255) baseStart_7978255 baseEnd_7978255 := by
    simpa [prefixWord, tailWord_7978255, baseEnd_7978255] using wordTrace_append hprefix tailTrace_7978255
  have hstable : (prefixWord ++ tailWord_7978255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978255).length < 2 ^ (prefixWord ++ tailWord_7978255).sum := by decide
  have hdescent : baseEnd_7978255 < baseStart_7978255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978288 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_7978288 : Nat := 118140960795 + 7978288 * 2 ^ 59
def prefixEnd_7978288 : Nat := 4983230072969 + 3 ^ 40 * 7978288 * 2
def baseEnd_7978288 : Nat := 1365565514666128715069509

theorem tailTrace_7978288 : CollatzResearch.WordTrace tailWord_7978288 prefixEnd_7978288 1365565514666128715069509 := by
  unfold tailWord_7978288
  simp only [CollatzResearch.WordTrace]
  refine ⟨145496034660016316977363759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193994712880021755969818345 145496034660016316977363759)
  ·
    refine ⟨218244051990024475466045639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145496034660016316977363759 218244051990024475466045639)
    ·
      refine ⟨327366077985036713199068459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218244051990024475466045639 327366077985036713199068459)
      ·
        refine ⟨491049116977555069798602689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327366077985036713199068459 491049116977555069798602689)
        ·
          refine ⟨368286837733166302348952017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491049116977555069798602689 368286837733166302348952017)
          ·
            refine ⟨276215128299874726761714013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368286837733166302348952017 276215128299874726761714013)
            ·
              refine ⟨103580673112453022535642755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276215128299874726761714013 103580673112453022535642755)
              ·
                refine ⟨155371009668679533803464133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103580673112453022535642755 155371009668679533803464133)
                ·
                  refine ⟨29132064312877412588149525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155371009668679533803464133 29132064312877412588149525)
                  ·
                    refine ⟨1365565514666128715069509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29132064312877412588149525 1365565514666128715069509)
                    ·
                      rfl

theorem cell23_7978288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_7978288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978288 prefixEnd_7978288 := by exact prefixLift 7978288
  have htrace : WordTrace (prefixWord ++ tailWord_7978288) baseStart_7978288 baseEnd_7978288 := by
    simpa [prefixWord, tailWord_7978288, baseEnd_7978288] using wordTrace_append hprefix tailTrace_7978288
  have hstable : (prefixWord ++ tailWord_7978288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978288).length < 2 ^ (prefixWord ++ tailWord_7978288).sum := by decide
  have hdescent : baseEnd_7978288 < baseStart_7978288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978289 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_7978289 : Nat := 118140960795 + 7978289 * 2 ^ 59
def prefixEnd_7978289 : Nat := 4983230072969 + 3 ^ 40 * 7978289 * 2
def baseEnd_7978289 : Nat := 4096697057479040641296023

theorem tailTrace_7978289 : CollatzResearch.WordTrace tailWord_7978289 prefixEnd_7978289 4096697057479040641296023 := by
  unfold tailWord_7978289
  simp only [CollatzResearch.WordTrace]
  refine ⟨290992105793029011125513921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193994737195352674083675947 290992105793029011125513921)
  ·
    refine ⟨218244079344771758344135441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290992105793029011125513921 218244079344771758344135441)
    ·
      refine ⟨163683059508578818758101581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218244079344771758344135441 163683059508578818758101581)
      ·
        refine ⟨61381147315717057034288093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163683059508578818758101581 61381147315717057034288093)
        ·
          refine ⟨23017930243393896387858035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61381147315717057034288093 23017930243393896387858035)
          ·
            refine ⟨34526895365090844581787053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23017930243393896387858035 34526895365090844581787053)
            ·
              refine ⟨12947585761909066718170145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34526895365090844581787053 12947585761909066718170145)
              ·
                refine ⟨9710689321431800038627609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12947585761909066718170145 9710689321431800038627609)
                ·
                  refine ⟨7283016991073850028970707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710689321431800038627609 7283016991073850028970707)
                  ·
                    refine ⟨10924525486610775043456061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283016991073850028970707 10924525486610775043456061)
                    ·
                      refine ⟨4096697057479040641296023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924525486610775043456061 4096697057479040641296023)
                      ·
                        rfl

theorem cell23_7978289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_7978289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978289 prefixEnd_7978289 := by exact prefixLift 7978289
  have htrace : WordTrace (prefixWord ++ tailWord_7978289) baseStart_7978289 baseEnd_7978289 := by
    simpa [prefixWord, tailWord_7978289, baseEnd_7978289] using wordTrace_append hprefix tailTrace_7978289
  have hstable : (prefixWord ++ tailWord_7978289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978289).length < 2 ^ (prefixWord ++ tailWord_7978289).sum := by decide
  have hdescent : baseEnd_7978289 < baseStart_7978289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978295 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_7978295 : Nat := 118140960795 + 7978295 * 2 ^ 59
def prefixEnd_7978295 : Nat := 4983230072969 + 3 ^ 40 * 7978295 * 2
def baseEnd_7978295 : Nat := 4096700138362967617820995

theorem tailTrace_7978295 : CollatzResearch.WordTrace tailWord_7978295 prefixEnd_7978295 4096700138362967617820995 := by
  unfold tailWord_7978295
  simp only [CollatzResearch.WordTrace]
  refine ⟨290992324631007274150232339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193994883087338182766821559 290992324631007274150232339)
  ·
    refine ⟨436488486946510911225348509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290992324631007274150232339 436488486946510911225348509)
    ·
      refine ⟨163683182604941591709505691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436488486946510911225348509 163683182604941591709505691)
      ·
        refine ⟨245524773907412387564258537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163683182604941591709505691 245524773907412387564258537)
        ·
          refine ⟨184143580430559290673193903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245524773907412387564258537 184143580430559290673193903)
          ·
            refine ⟨276215370645838936009790855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184143580430559290673193903 276215370645838936009790855)
            ·
              refine ⟨414323055968758404014686283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276215370645838936009790855 414323055968758404014686283)
              ·
                refine ⟨621484583953137606022029425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414323055968758404014686283 621484583953137606022029425)
                ·
                  refine ⟨466113437964853204516522069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621484583953137606022029425 466113437964853204516522069)
                  ·
                    refine ⟨5462266851150623490427993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 466113437964853204516522069 5462266851150623490427993)
                    ·
                      refine ⟨4096700138362967617820995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462266851150623490427993 4096700138362967617820995)
                      ·
                        rfl

theorem cell23_7978295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_7978295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978295 prefixEnd_7978295 := by exact prefixLift 7978295
  have htrace : WordTrace (prefixWord ++ tailWord_7978295) baseStart_7978295 baseEnd_7978295 := by
    simpa [prefixWord, tailWord_7978295, baseEnd_7978295] using wordTrace_append hprefix tailTrace_7978295
  have hstable : (prefixWord ++ tailWord_7978295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978295).length < 2 ^ (prefixWord ++ tailWord_7978295).sum := by decide
  have hdescent : baseEnd_7978295 < baseStart_7978295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978345 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_7978345 : Nat := 118140960795 + 7978345 * 2 ^ 59
def prefixEnd_7978345 : Nat := 4983230072969 + 3 ^ 40 * 7978345 * 2
def baseEnd_7978345 : Nat := 4096725812395692422195765

theorem tailTrace_7978345 : CollatzResearch.WordTrace tailWord_7978345 prefixEnd_7978345 4096725812395692422195765 := by
  unfold tailWord_7978345
  simp only [CollatzResearch.WordTrace]
  refine ⟨290994148280826132689552489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193996098853884088459701659 290994148280826132689552489)
  ·
    refine ⟨218245611210619599517164367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290994148280826132689552489 218245611210619599517164367)
    ·
      refine ⟨327368416815929399275746551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218245611210619599517164367 327368416815929399275746551)
      ·
        refine ⟨491052625223894098913619827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327368416815929399275746551 491052625223894098913619827)
        ·
          refine ⟨736578937835841148370429741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491052625223894098913619827 736578937835841148370429741)
          ·
            refine ⟨276217101688440430638911153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736578937835841148370429741 276217101688440430638911153)
            ·
              refine ⟨207162826266330322979183365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276217101688440430638911153 207162826266330322979183365)
              ·
                refine ⟨38843029924936935558596881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207162826266330322979183365 38843029924936935558596881)
                ·
                  refine ⟨29132272443702701668947661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38843029924936935558596881 29132272443702701668947661)
                  ·
                    refine ⟨10924602166388513125855373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29132272443702701668947661 10924602166388513125855373)
                    ·
                      refine ⟨4096725812395692422195765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924602166388513125855373 4096725812395692422195765)
                      ·
                        rfl

theorem cell23_7978345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_7978345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978345 prefixEnd_7978345 := by exact prefixLift 7978345
  have htrace : WordTrace (prefixWord ++ tailWord_7978345) baseStart_7978345 baseEnd_7978345 := by
    simpa [prefixWord, tailWord_7978345, baseEnd_7978345] using wordTrace_append hprefix tailTrace_7978345
  have hstable : (prefixWord ++ tailWord_7978345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978345).length < 2 ^ (prefixWord ++ tailWord_7978345).sum := by decide
  have hdescent : baseEnd_7978345 < baseStart_7978345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978365 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7978365 : Nat := 118140960795 + 7978365 * 2 ^ 59
def prefixEnd_7978365 : Nat := 4983230072969 + 3 ^ 40 * 7978365 * 2
def baseEnd_7978365 : Nat := 1365578694002927447981891

theorem tailTrace_7978365 : CollatzResearch.WordTrace tailWord_7978365 prefixEnd_7978365 1365578694002927447981891 := by
  unfold tailWord_7978365
  simp only [CollatzResearch.WordTrace]
  refine ⟨290994877740753676105280549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193996585160502450736853699 290994877740753676105280549)
  ·
    refine ⟨54561539576391314269740103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290994877740753676105280549 54561539576391314269740103)
    ·
      refine ⟨81842309364586971404610155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54561539576391314269740103 81842309364586971404610155)
      ·
        refine ⟨122763464046880457106915233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81842309364586971404610155 122763464046880457106915233)
        ·
          refine ⟨92072598035160342830186425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122763464046880457106915233 92072598035160342830186425)
          ·
            refine ⟨69054448526370257122639819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92072598035160342830186425 69054448526370257122639819)
            ·
              refine ⟨103581672789555385683959729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69054448526370257122639819 103581672789555385683959729)
              ·
                refine ⟨77686254592166539262969797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103581672789555385683959729 77686254592166539262969797)
                ·
                  refine ⟨14566172736031226111806837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77686254592166539262969797 14566172736031226111806837)
                  ·
                    refine ⟨1365578694002927447981891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14566172736031226111806837 1365578694002927447981891)
                    ·
                      rfl

theorem cell23_7978365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7978365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978365 prefixEnd_7978365 := by exact prefixLift 7978365
  have htrace : WordTrace (prefixWord ++ tailWord_7978365) baseStart_7978365 baseEnd_7978365 := by
    simpa [prefixWord, tailWord_7978365, baseEnd_7978365] using wordTrace_append hprefix tailTrace_7978365
  have hstable : (prefixWord ++ tailWord_7978365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978365).length < 2 ^ (prefixWord ++ tailWord_7978365).sum := by decide
  have hdescent : baseEnd_7978365 < baseStart_7978365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978385 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_7978385 : Nat := 118140960795 + 7978385 * 2 ^ 59
def prefixEnd_7978385 : Nat := 4983230072969 + 3 ^ 40 * 7978385 * 2
def baseEnd_7978385 : Nat := 4096746351621872265695581

theorem tailTrace_7978385 : CollatzResearch.WordTrace tailWord_7978385 prefixEnd_7978385 4096746351621872265695581 := by
  unfold tailWord_7978385
  simp only [CollatzResearch.WordTrace]
  refine ⟨290995607200681219521008609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193997071467120813014005739 290995607200681219521008609)
  ·
    refine ⟨218246705400510914640756457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290995607200681219521008609 218246705400510914640756457)
    ·
      refine ⟨163685029050383185980567343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218246705400510914640756457 163685029050383185980567343)
      ·
        refine ⟨245527543575574778970851015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163685029050383185980567343 245527543575574778970851015)
        ·
          refine ⟨368291315363362168456276523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245527543575574778970851015 368291315363362168456276523)
          ·
            refine ⟨552436973045043252684414785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368291315363362168456276523 552436973045043252684414785)
            ·
              refine ⟨414327729783782439513311089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552436973045043252684414785 414327729783782439513311089)
              ·
                refine ⟨310745797337836829634983317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414327729783782439513311089 310745797337836829634983317)
                ·
                  refine ⟨14566209250211101389139843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310745797337836829634983317 14566209250211101389139843)
                  ·
                    refine ⟨21849313875316652083709765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14566209250211101389139843 21849313875316652083709765)
                    ·
                      refine ⟨4096746351621872265695581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21849313875316652083709765 4096746351621872265695581)
                      ·
                        rfl

theorem cell23_7978385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_7978385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978385 prefixEnd_7978385 := by exact prefixLift 7978385
  have htrace : WordTrace (prefixWord ++ tailWord_7978385) baseStart_7978385 baseEnd_7978385 := by
    simpa [prefixWord, tailWord_7978385, baseEnd_7978385] using wordTrace_append hprefix tailTrace_7978385
  have hstable : (prefixWord ++ tailWord_7978385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978385).length < 2 ^ (prefixWord ++ tailWord_7978385).sum := by decide
  have hdescent : baseEnd_7978385 < baseStart_7978385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978436 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7978436 : Nat := 118140960795 + 7978436 * 2 ^ 59
def prefixEnd_7978436 : Nat := 4983230072969 + 3 ^ 40 * 7978436 * 2
def baseEnd_7978436 : Nat := 4096772539135251566157847

theorem tailTrace_7978436 : CollatzResearch.WordTrace tailWord_7978436 prefixEnd_7978436 4096772539135251566157847 := by
  unfold tailWord_7978436
  simp only [CollatzResearch.WordTrace]
  refine ⟨145498733661748227615557581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193998311548997636820743441 145498733661748227615557581)
  ·
    refine ⟨54562025123155585355834093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145498733661748227615557581 54562025123155585355834093)
    ·
      refine ⟨20460759421183344508437785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54562025123155585355834093 20460759421183344508437785)
      ·
        refine ⟨15345569565887508381328339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20460759421183344508437785 15345569565887508381328339)
        ·
          refine ⟨23018354348831262571992509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15345569565887508381328339 23018354348831262571992509)
          ·
            refine ⟨8631882880811723464497191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23018354348831262571992509 8631882880811723464497191)
            ·
              refine ⟨12947824321217585196745787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631882880811723464497191 12947824321217585196745787)
              ·
                refine ⟨19421736481826377795118681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12947824321217585196745787 19421736481826377795118681)
                ·
                  refine ⟨14566302361369783346339011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19421736481826377795118681 14566302361369783346339011)
                  ·
                    refine ⟨21849453542054675019508517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14566302361369783346339011 21849453542054675019508517)
                    ·
                      refine ⟨4096772539135251566157847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21849453542054675019508517 4096772539135251566157847)
                      ·
                        rfl

theorem cell23_7978436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7978436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978436 prefixEnd_7978436 := by exact prefixLift 7978436
  have htrace : WordTrace (prefixWord ++ tailWord_7978436) baseStart_7978436 baseEnd_7978436 := by
    simpa [prefixWord, tailWord_7978436, baseEnd_7978436] using wordTrace_append hprefix tailTrace_7978436
  have hstable : (prefixWord ++ tailWord_7978436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978436).length < 2 ^ (prefixWord ++ tailWord_7978436).sum := by decide
  have hdescent : baseEnd_7978436 < baseStart_7978436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978475 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_7978475 : Nat := 118140960795 + 7978475 * 2 ^ 59
def prefixEnd_7978475 : Nat := 4983230072969 + 3 ^ 40 * 7978475 * 2
def baseEnd_7978475 : Nat := 4096792564880776913570167

theorem tailTrace_7978475 : CollatzResearch.WordTrace tailWord_7978475 prefixEnd_7978475 4096792564880776913570167 := by
  unfold tailWord_7978475
  simp only [CollatzResearch.WordTrace]
  refine ⟨290998889770355164891784879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193999259846903443261189919 290998889770355164891784879)
  ·
    refine ⟨436498334655532747337677319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290998889770355164891784879 436498334655532747337677319)
    ·
      refine ⟨654747501983299121006515979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436498334655532747337677319 654747501983299121006515979)
      ·
        refine ⟨982121252974948681509773969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654747501983299121006515979 982121252974948681509773969)
        ·
          refine ⟨736590939731211511132330477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982121252974948681509773969 736590939731211511132330477)
          ·
            refine ⟨276221602399204316674623929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736590939731211511132330477 276221602399204316674623929)
            ·
              refine ⟨207166201799403237505967947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276221602399204316674623929 207166201799403237505967947)
              ·
                refine ⟨310749302699104856258951921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207166201799403237505967947 310749302699104856258951921)
                ·
                  refine ⟨233061977024328642194213941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310749302699104856258951921 233061977024328642194213941)
                  ·
                    refine ⟨21849560346030810205707557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233061977024328642194213941 21849560346030810205707557)
                    ·
                      refine ⟨4096792564880776913570167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21849560346030810205707557 4096792564880776913570167)
                      ·
                        rfl

theorem cell23_7978475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_7978475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978475 prefixEnd_7978475 := by exact prefixLift 7978475
  have htrace : WordTrace (prefixWord ++ tailWord_7978475) baseStart_7978475 baseEnd_7978475 := by
    simpa [prefixWord, tailWord_7978475, baseEnd_7978475] using wordTrace_append hprefix tailTrace_7978475
  have hstable : (prefixWord ++ tailWord_7978475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978475).length < 2 ^ (prefixWord ++ tailWord_7978475).sum := by decide
  have hdescent : baseEnd_7978475 < baseStart_7978475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978486 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_7978486 : Nat := 118140960795 + 7978486 * 2 ^ 59
def prefixEnd_7978486 : Nat := 4983230072969 + 3 ^ 40 * 7978486 * 2
def baseEnd_7978486 : Nat := 4096798213167976370532617

theorem tailTrace_7978486 : CollatzResearch.WordTrace tailWord_7978486 prefixEnd_7978486 4096798213167976370532617 := by
  unfold tailWord_7978486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187455685832207110652207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193999527315543542513623541 18187455685832207110652207)
  ·
    refine ⟨27281183528748310665978311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18187455685832207110652207 27281183528748310665978311)
    ·
      refine ⟨40921775293122465998967467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27281183528748310665978311 40921775293122465998967467)
      ·
        refine ⟨61382662939683698998451201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40921775293122465998967467 61382662939683698998451201)
        ·
          refine ⟨46036997204762774248838401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61382662939683698998451201 46036997204762774248838401)
          ·
            refine ⟨34527747903572080686628801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46036997204762774248838401 34527747903572080686628801)
            ·
              refine ⟨25895810927679060514971601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34527747903572080686628801 25895810927679060514971601)
              ·
                refine ⟨19421858195759295386228701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25895810927679060514971601 19421858195759295386228701)
                ·
                  refine ⟨7283196823409735769835763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19421858195759295386228701 7283196823409735769835763)
                  ·
                    refine ⟨10924795235114603654753645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283196823409735769835763 10924795235114603654753645)
                    ·
                      refine ⟨4096798213167976370532617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924795235114603654753645 4096798213167976370532617)
                      ·
                        rfl

theorem cell23_7978486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_7978486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978486 prefixEnd_7978486 := by exact prefixLift 7978486
  have htrace : WordTrace (prefixWord ++ tailWord_7978486) baseStart_7978486 baseEnd_7978486 := by
    simpa [prefixWord, tailWord_7978486, baseEnd_7978486] using wordTrace_append hprefix tailTrace_7978486
  have hstable : (prefixWord ++ tailWord_7978486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978486).length < 2 ^ (prefixWord ++ tailWord_7978486).sum := by decide
  have hdescent : baseEnd_7978486 < baseStart_7978486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978492 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_7978492 : Nat := 118140960795 + 7978492 * 2 ^ 59
def prefixEnd_7978492 : Nat := 4983230072969 + 3 ^ 40 * 7978492 * 2
def baseEnd_7978492 : Nat := 4096801294051903347057589

theorem tailTrace_7978492 : CollatzResearch.WordTrace tailWord_7978492 prefixEnd_7978492 4096801294051903347057589 := by
  unfold tailWord_7978492
  simp only [CollatzResearch.WordTrace]
  refine ⟨145499754905646788397576865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193999673207529051196769153 145499754905646788397576865)
  ·
    refine ⟨109124816179235091298182649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145499754905646788397576865 109124816179235091298182649)
    ·
      refine ⟨81843612134426318473636987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109124816179235091298182649 81843612134426318473636987)
      ·
        refine ⟨122765418201639477710455481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81843612134426318473636987 122765418201639477710455481)
        ·
          refine ⟨92074063651229608282841611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122765418201639477710455481 92074063651229608282841611)
          ·
            refine ⟨138111095476844412424262417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92074063651229608282841611 138111095476844412424262417)
            ·
              refine ⟨103583321607633309318196813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138111095476844412424262417 103583321607633309318196813)
              ·
                refine ⟨38843745602862490994323805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103583321607633309318196813 38843745602862490994323805)
                ·
                  refine ⟨14566404601073434122871427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38843745602862490994323805 14566404601073434122871427)
                  ·
                    refine ⟨21849606901610151184307141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14566404601073434122871427 21849606901610151184307141)
                    ·
                      refine ⟨4096801294051903347057589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21849606901610151184307141 4096801294051903347057589)
                      ·
                        rfl

theorem cell23_7978492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_7978492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978492 prefixEnd_7978492 := by exact prefixLift 7978492
  have htrace : WordTrace (prefixWord ++ tailWord_7978492) baseStart_7978492 baseEnd_7978492 := by
    simpa [prefixWord, tailWord_7978492, baseEnd_7978492] using wordTrace_append hprefix tailTrace_7978492
  have hstable : (prefixWord ++ tailWord_7978492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978492).length < 2 ^ (prefixWord ++ tailWord_7978492).sum := by decide
  have hdescent : baseEnd_7978492 < baseStart_7978492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978503 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7978503 : Nat := 118140960795 + 7978503 * 2 ^ 59
def prefixEnd_7978503 : Nat := 4983230072969 + 3 ^ 40 * 7978503 * 2
def baseEnd_7978503 : Nat := 4096806942339102804020039

theorem tailTrace_7978503 : CollatzResearch.WordTrace tailWord_7978503 prefixEnd_7978503 4096806942339102804020039 := by
  unfold tailWord_7978503
  simp only [CollatzResearch.WordTrace]
  refine ⟨290999911014253725673804163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193999940676169150449202775 290999911014253725673804163)
  ·
    refine ⟨436499866521380588510706245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290999911014253725673804163 436499866521380588510706245)
    ·
      refine ⟨81843724972758860345757421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436499866521380588510706245 81843724972758860345757421)
      ·
        refine ⟨30691396864784572629659033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81843724972758860345757421 30691396864784572629659033)
        ·
          refine ⟨23018547648588429472244275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30691396864784572629659033 23018547648588429472244275)
          ·
            refine ⟨34527821472882644208366413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23018547648588429472244275 34527821472882644208366413)
            ·
              refine ⟨12947933052330991578137405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34527821472882644208366413 12947933052330991578137405)
              ·
                refine ⟨4855474894624121841801527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12947933052330991578137405 4855474894624121841801527)
                ·
                  refine ⟨7283212341936182762702291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855474894624121841801527 7283212341936182762702291)
                  ·
                    refine ⟨10924818512904274144053437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283212341936182762702291 10924818512904274144053437)
                    ·
                      refine ⟨4096806942339102804020039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924818512904274144053437 4096806942339102804020039)
                      ·
                        rfl

theorem cell23_7978503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7978503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978503 prefixEnd_7978503 := by exact prefixLift 7978503
  have htrace : WordTrace (prefixWord ++ tailWord_7978503) baseStart_7978503 baseEnd_7978503 := by
    simpa [prefixWord, tailWord_7978503, baseEnd_7978503] using wordTrace_append hprefix tailTrace_7978503
  have hstable : (prefixWord ++ tailWord_7978503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978503).length < 2 ^ (prefixWord ++ tailWord_7978503).sum := by decide
  have hdescent : baseEnd_7978503 < baseStart_7978503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978515 : List Nat := [1, 1, 1, 2, 1, 6, 11]
def baseStart_7978515 : Nat := 118140960795 + 7978515 * 2 ^ 59
def prefixEnd_7978515 : Nat := 4983230072969 + 3 ^ 40 * 7978515 * 2
def baseEnd_7978515 : Nat := 50577939556876009346543

theorem tailTrace_7978515 : CollatzResearch.WordTrace tailWord_7978515 prefixEnd_7978515 50577939556876009346543 := by
  unfold tailWord_7978515
  simp only [CollatzResearch.WordTrace]
  refine ⟨291000348690210251723240999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194000232460140167815493999 291000348690210251723240999)
  ·
    refine ⟨436500523035315377584861499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291000348690210251723240999 436500523035315377584861499)
    ·
      refine ⟨654750784552973066377292249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436500523035315377584861499 654750784552973066377292249)
      ·
        refine ⟨491063088414729799782969187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654750784552973066377292249 491063088414729799782969187)
        ·
          refine ⟨736594632622094699674453781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491063088414729799782969187 736594632622094699674453781)
          ·
            refine ⟨34527873404160689047240021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 736594632622094699674453781 34527873404160689047240021)
            ·
              refine ⟨50577939556876009346543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34527873404160689047240021 50577939556876009346543)
              ·
                rfl

theorem cell23_7978515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 11].length) (baseStart_7978515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978515 prefixEnd_7978515 := by exact prefixLift 7978515
  have htrace : WordTrace (prefixWord ++ tailWord_7978515) baseStart_7978515 baseEnd_7978515 := by
    simpa [prefixWord, tailWord_7978515, baseEnd_7978515] using wordTrace_append hprefix tailTrace_7978515
  have hstable : (prefixWord ++ tailWord_7978515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978515).length < 2 ^ (prefixWord ++ tailWord_7978515).sum := by decide
  have hdescent : baseEnd_7978515 < baseStart_7978515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978520 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 1, 1, 3]
def baseStart_7978520 : Nat := 118140960795 + 7978520 * 2 ^ 59
def prefixEnd_7978520 : Nat := 4983230072969 + 3 ^ 40 * 7978520 * 2
def baseEnd_7978520 : Nat := 4096815671510229237507461

theorem tailTrace_7978520 : CollatzResearch.WordTrace tailWord_7978520 prefixEnd_7978520 4096815671510229237507461 := by
  unfold tailWord_7978520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145500265527596068788586507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194000354036794758384782009 145500265527596068788586507)
  ·
    refine ⟨218250398291394103182879761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145500265527596068788586507 218250398291394103182879761)
    ·
      refine ⟨163687798718545577387159821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218250398291394103182879761 163687798718545577387159821)
      ·
        refine ⟨61382924519454591520184933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163687798718545577387159821 61382924519454591520184933)
        ·
          refine ⟨11509298347397735910034675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61382924519454591520184933 11509298347397735910034675)
          ·
            refine ⟨17263947521096603865052013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509298347397735910034675 17263947521096603865052013)
            ·
              refine ⟨6473980320411226449394505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17263947521096603865052013 6473980320411226449394505)
              ·
                refine ⟨4855485240308419837045879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6473980320411226449394505 4855485240308419837045879)
                ·
                  refine ⟨7283227860462629755568819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855485240308419837045879 7283227860462629755568819)
                  ·
                    refine ⟨10924841790693944633353229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283227860462629755568819 10924841790693944633353229)
                    ·
                      refine ⟨4096815671510229237507461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924841790693944633353229 4096815671510229237507461)
                      ·
                        rfl

theorem cell23_7978520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_7978520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978520 prefixEnd_7978520 := by exact prefixLift 7978520
  have htrace : WordTrace (prefixWord ++ tailWord_7978520) baseStart_7978520 baseEnd_7978520 := by
    simpa [prefixWord, tailWord_7978520, baseEnd_7978520] using wordTrace_append hprefix tailTrace_7978520
  have hstable : (prefixWord ++ tailWord_7978520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978520).length < 2 ^ (prefixWord ++ tailWord_7978520).sum := by decide
  have hdescent : baseEnd_7978520 < baseStart_7978520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978559 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_7978559 : Nat := 118140960795 + 7978559 * 2 ^ 59
def prefixEnd_7978559 : Nat := 4983230072969 + 3 ^ 40 * 7978559 * 2
def baseEnd_7978559 : Nat := 4096835697255754584919781

theorem tailTrace_7978559 : CollatzResearch.WordTrace tailWord_7978559 prefixEnd_7978559 4096835697255754584919781 := by
  unfold tailWord_7978559
  simp only [CollatzResearch.WordTrace]
  refine ⟨291001953502050847237842731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194001302334700564825228487 291001953502050847237842731)
  ·
    refine ⟨436502930253076270856764097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291001953502050847237842731 436502930253076270856764097)
    ·
      refine ⟨327377197689807203142573073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436502930253076270856764097 327377197689807203142573073)
      ·
        refine ⟨245532898267355402356929805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327377197689807203142573073 245532898267355402356929805)
        ·
          refine ⟨92074836850258275883848677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245532898267355402356929805 92074836850258275883848677)
          ·
            refine ⟨17264031909423426728221627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92074836850258275883848677 17264031909423426728221627)
            ·
              refine ⟨25896047864135140092332441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264031909423426728221627 25896047864135140092332441)
              ·
                refine ⟨19422035898101355069249331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25896047864135140092332441 19422035898101355069249331)
                ·
                  refine ⟨29133053847152032603873997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19422035898101355069249331 29133053847152032603873997)
                  ·
                    refine ⟨10924895192682012226452749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29133053847152032603873997 10924895192682012226452749)
                    ·
                      refine ⟨4096835697255754584919781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924895192682012226452749 4096835697255754584919781)
                      ·
                        rfl

theorem cell23_7978559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_7978559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978559 prefixEnd_7978559 := by exact prefixLift 7978559
  have htrace : WordTrace (prefixWord ++ tailWord_7978559) baseStart_7978559 baseEnd_7978559 := by
    simpa [prefixWord, tailWord_7978559, baseEnd_7978559] using wordTrace_append hprefix tailTrace_7978559
  have hstable : (prefixWord ++ tailWord_7978559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978559).length < 2 ^ (prefixWord ++ tailWord_7978559).sum := by decide
  have hdescent : baseEnd_7978559 < baseStart_7978559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978566 : List Nat := [6, 1, 1, 1, 4, 10]
def baseStart_7978566 : Nat := 118140960795 + 7978566 * 2 ^ 59
def prefixEnd_7978566 : Nat := 4983230072969 + 3 ^ 40 * 7978566 * 2
def baseEnd_7978566 : Nat := 16859420953170107232643

theorem tailTrace_7978566 : CollatzResearch.WordTrace tailWord_7978566 prefixEnd_7978566 16859420953170107232643 := by
  unfold tailWord_7978566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093819025407046482292111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194001472542016991622231701 9093819025407046482292111)
  ·
    refine ⟨13640728538110569723438167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9093819025407046482292111 13640728538110569723438167)
    ·
      refine ⟨20461092807165854585157251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13640728538110569723438167 20461092807165854585157251)
      ·
        refine ⟨30691639210748781877735877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20461092807165854585157251 30691639210748781877735877)
        ·
          refine ⟨5754682352015396602075477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30691639210748781877735877 5754682352015396602075477)
          ·
            refine ⟨16859420953170107232643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5754682352015396602075477 16859420953170107232643)
            ·
              rfl

theorem cell23_7978566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 10].length) (baseStart_7978566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978566 prefixEnd_7978566 := by exact prefixLift 7978566
  have htrace : WordTrace (prefixWord ++ tailWord_7978566) baseStart_7978566 baseEnd_7978566 := by
    simpa [prefixWord, tailWord_7978566, baseEnd_7978566] using wordTrace_append hprefix tailTrace_7978566
  have hstable : (prefixWord ++ tailWord_7978566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978566).length < 2 ^ (prefixWord ++ tailWord_7978566).sum := by decide
  have hdescent : baseEnd_7978566 < baseStart_7978566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978576 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3]
def baseStart_7978576 : Nat := 118140960795 + 7978576 * 2 ^ 59
def prefixEnd_7978576 : Nat := 4983230072969 + 3 ^ 40 * 7978576 * 2
def baseEnd_7978576 : Nat := 4096844426426881018407203

theorem tailTrace_7978576 : CollatzResearch.WordTrace tailWord_7978576 prefixEnd_7978576 4096844426426881018407203 := by
  unfold tailWord_7978576
  simp only [CollatzResearch.WordTrace]
  refine ⟨145501286771494629570605791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194001715695326172760807721 145501286771494629570605791)
  ·
    refine ⟨218251930157241944355908687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145501286771494629570605791 218251930157241944355908687)
    ·
      refine ⟨327377895235862916533863031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218251930157241944355908687 327377895235862916533863031)
      ·
        refine ⟨491066842853794374800794547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327377895235862916533863031 491066842853794374800794547)
        ·
          refine ⟨736600264280691562201191821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491066842853794374800794547 736600264280691562201191821)
          ·
            refine ⟨276225099105259335825446933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736600264280691562201191821 276225099105259335825446933)
            ·
              refine ⟨12948051520559031366817825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276225099105259335825446933 12948051520559031366817825)
              ·
                refine ⟨9711038640419273525113369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12948051520559031366817825 9711038640419273525113369)
                ·
                  refine ⟨7283278980314455143835027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9711038640419273525113369 7283278980314455143835027)
                  ·
                    refine ⟨10924918470471682715752541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283278980314455143835027 10924918470471682715752541)
                    ·
                      refine ⟨4096844426426881018407203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10924918470471682715752541 4096844426426881018407203)
                      ·
                        rfl

theorem cell23_7978576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_7978576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978576 prefixEnd_7978576 := by exact prefixLift 7978576
  have htrace : WordTrace (prefixWord ++ tailWord_7978576) baseStart_7978576 baseEnd_7978576 := by
    simpa [prefixWord, tailWord_7978576, baseEnd_7978576] using wordTrace_append hprefix tailTrace_7978576
  have hstable : (prefixWord ++ tailWord_7978576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978576).length < 2 ^ (prefixWord ++ tailWord_7978576).sum := by decide
  have hdescent : baseEnd_7978576 < baseStart_7978576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978633 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 2, 2, 2]
def baseStart_7978633 : Nat := 118140960795 + 7978633 * 2 ^ 59
def prefixEnd_7978633 : Nat := 4983230072969 + 3 ^ 40 * 7978633 * 2
def baseEnd_7978633 : Nat := 4096873694824187295394441

theorem tailTrace_7978633 : CollatzResearch.WordTrace tailWord_7978633 prefixEnd_7978633 4096873694824187295394441 := by
  unfold tailWord_7978633
  simp only [CollatzResearch.WordTrace]
  refine ⟨291004652503782757876036553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194003101669188505250691035 291004652503782757876036553)
  ·
    refine ⟨218253489377837068407027415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291004652503782757876036553 218253489377837068407027415)
    ·
      refine ⟨327380234066755602610541123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218253489377837068407027415 327380234066755602610541123)
      ·
        refine ⟨491070351100133403915811685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327380234066755602610541123 491070351100133403915811685)
        ·
          refine ⟨92075690831275013234214691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 491070351100133403915811685 92075690831275013234214691)
          ·
            refine ⟨138113536246912519851322037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92075690831275013234214691 138113536246912519851322037)
            ·
              refine ⟨12948144023148048736061441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138113536246912519851322037 12948144023148048736061441)
              ·
                refine ⟨9711108017361036552046081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12948144023148048736061441 9711108017361036552046081)
                ·
                  refine ⟨7283331013020777414034561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9711108017361036552046081 7283331013020777414034561)
                  ·
                    refine ⟨5462498259765583060525921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283331013020777414034561 5462498259765583060525921)
                    ·
                      refine ⟨4096873694824187295394441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462498259765583060525921 4096873694824187295394441)
                      ·
                        rfl

theorem cell23_7978633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2, 2].length) (baseStart_7978633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978633 prefixEnd_7978633 := by exact prefixLift 7978633
  have htrace : WordTrace (prefixWord ++ tailWord_7978633) baseStart_7978633 baseEnd_7978633 := by
    simpa [prefixWord, tailWord_7978633, baseEnd_7978633] using wordTrace_append hprefix tailTrace_7978633
  have hstable : (prefixWord ++ tailWord_7978633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978633).length < 2 ^ (prefixWord ++ tailWord_7978633).sum := by decide
  have hdescent : baseEnd_7978633 < baseStart_7978633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978669 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7978669 : Nat := 118140960795 + 7978669 * 2 ^ 59
def prefixEnd_7978669 : Nat := 4983230072969 + 3 ^ 40 * 7978669 * 2
def baseEnd_7978669 : Nat := 1365630726709249718181425

theorem tailTrace_7978669 : CollatzResearch.WordTrace tailWord_7978669 prefixEnd_7978669 1365630726709249718181425 := by
  unfold tailWord_7978669
  simp only [CollatzResearch.WordTrace]
  refine ⟨291005965531652336024347061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194003977021101557349564707 291005965531652336024347061)
  ·
    refine ⟨27281809268592406502282537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291005965531652336024347061 27281809268592406502282537)
    ·
      refine ⟨20461356951444304876711903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27281809268592406502282537 20461356951444304876711903)
      ·
        refine ⟨30692035427166457315067855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20461356951444304876711903 30692035427166457315067855)
        ·
          refine ⟨46038053140749685972601783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30692035427166457315067855 46038053140749685972601783)
          ·
            refine ⟨69057079711124528958902675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46038053140749685972601783 69057079711124528958902675)
            ·
              refine ⟨103585619566686793438354013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69057079711124528958902675 103585619566686793438354013)
              ·
                refine ⟨38844607337507547539382755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103585619566686793438354013 38844607337507547539382755)
                ·
                  refine ⟨58266911006261321309074133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38844607337507547539382755 58266911006261321309074133)
                  ·
                    refine ⟨1365630726709249718181425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58266911006261321309074133 1365630726709249718181425)
                    ·
                      rfl

theorem cell23_7978669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7978669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978669 prefixEnd_7978669 := by exact prefixLift 7978669
  have htrace : WordTrace (prefixWord ++ tailWord_7978669) baseStart_7978669 baseEnd_7978669 := by
    simpa [prefixWord, tailWord_7978669, baseEnd_7978669] using wordTrace_append hprefix tailTrace_7978669
  have hstable : (prefixWord ++ tailWord_7978669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978669).length < 2 ^ (prefixWord ++ tailWord_7978669).sum := by decide
  have hdescent : baseEnd_7978669 < baseStart_7978669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978686 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7978686 : Nat := 118140960795 + 7978686 * 2 ^ 59
def prefixEnd_7978686 : Nat := 4983230072969 + 3 ^ 40 * 7978686 * 2
def baseEnd_7978686 : Nat := 1365633636432958529343899

theorem tailTrace_7978686 : CollatzResearch.WordTrace tailWord_7978686 prefixEnd_7978686 1365633636432958529343899 := by
  unfold tailWord_7978686
  simp only [CollatzResearch.WordTrace]
  refine ⟨36375823196573843490964489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194004390381727165285143941 36375823196573843490964489)
  ·
    refine ⟨27281867397430382618223367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36375823196573843490964489 27281867397430382618223367)
    ·
      refine ⟨40922801096145573927335051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27281867397430382618223367 40922801096145573927335051)
      ·
        refine ⟨61384201644218360891002577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40922801096145573927335051 61384201644218360891002577)
        ·
          refine ⟨46038151233163770668251933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61384201644218360891002577 46038151233163770668251933)
          ·
            refine ⟨17264306712436414000594475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46038151233163770668251933 17264306712436414000594475)
            ·
              refine ⟨25896460068654621000891713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264306712436414000594475 25896460068654621000891713)
              ·
                refine ⟨19422345051490965750668785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25896460068654621000891713 19422345051490965750668785)
                ·
                  refine ⟨14566758788618224313001589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422345051490965750668785 14566758788618224313001589)
                  ·
                    refine ⟨1365633636432958529343899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14566758788618224313001589 1365633636432958529343899)
                    ·
                      rfl

theorem cell23_7978686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7978686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978686 prefixEnd_7978686 := by exact prefixLift 7978686
  have htrace : WordTrace (prefixWord ++ tailWord_7978686) baseStart_7978686 baseEnd_7978686 := by
    simpa [prefixWord, tailWord_7978686, baseEnd_7978686] using wordTrace_append hprefix tailTrace_7978686
  have hstable : (prefixWord ++ tailWord_7978686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978686).length < 2 ^ (prefixWord ++ tailWord_7978686).sum := by decide
  have hdescent : baseEnd_7978686 < baseStart_7978686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978723 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7978723 : Nat := 118140960795 + 7978723 * 2 ^ 59
def prefixEnd_7978723 : Nat := 4983230072969 + 3 ^ 40 * 7978723 * 2
def baseEnd_7978723 : Nat := 4096919908083091943269027

theorem tailTrace_7978723 : CollatzResearch.WordTrace tailWord_7978723 prefixEnd_7978723 4096919908083091943269027 := by
  unfold tailWord_7978723
  simp only [CollatzResearch.WordTrace]
  refine ⟨291007935073456703246812823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194005290048971135497875215 291007935073456703246812823)
  ·
    refine ⟨436511902610185054870219235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291007935073456703246812823 436511902610185054870219235)
    ·
      refine ⟨654767853915277582305328853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436511902610185054870219235 654767853915277582305328853)
      ·
        refine ⟨15346121576139318335281145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 654767853915277582305328853 15346121576139318335281145)
        ·
          refine ⟨11509591182104488751460859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15346121576139318335281145 11509591182104488751460859)
          ·
            refine ⟨17264386773156733127191289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509591182104488751460859 17264386773156733127191289)
            ·
              refine ⟨12948290079867549845393467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17264386773156733127191289 12948290079867549845393467)
              ·
                refine ⟨19422435119801324768090201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948290079867549845393467 19422435119801324768090201)
                ·
                  refine ⟨14566826339850993576067651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422435119801324768090201 14566826339850993576067651)
                  ·
                    refine ⟨21850239509776490364101477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14566826339850993576067651 21850239509776490364101477)
                    ·
                      refine ⟨4096919908083091943269027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21850239509776490364101477 4096919908083091943269027)
                      ·
                        rfl

theorem cell23_7978723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7978723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978723 prefixEnd_7978723 := by exact prefixLift 7978723
  have htrace : WordTrace (prefixWord ++ tailWord_7978723) baseStart_7978723 baseEnd_7978723 := by
    simpa [prefixWord, tailWord_7978723, baseEnd_7978723] using wordTrace_append hprefix tailTrace_7978723
  have hstable : (prefixWord ++ tailWord_7978723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978723).length < 2 ^ (prefixWord ++ tailWord_7978723).sum := by decide
  have hdescent : baseEnd_7978723 < baseStart_7978723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978740 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7978740 : Nat := 118140960795 + 7978740 * 2 ^ 59
def prefixEnd_7978740 : Nat := 4983230072969 + 3 ^ 40 * 7978740 * 2
def baseEnd_7978740 : Nat := 4096928637254218376756449

theorem tailTrace_7978740 : CollatzResearch.WordTrace tailWord_7978740 prefixEnd_7978740 4096928637254218376756449 := by
  unfold tailWord_7978740
  simp only [CollatzResearch.WordTrace]
  refine ⟨145504277557197557575090837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194005703409596743433454449 145504277557197557575090837)
  ·
    refine ⟨6820513010493635511332383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145504277557197557575090837 6820513010493635511332383)
    ·
      refine ⟨10230769515740453266998575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820513010493635511332383 10230769515740453266998575)
      ·
        refine ⟨15346154273610679900497863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10230769515740453266998575 15346154273610679900497863)
        ·
          refine ⟨23019231410416019850746795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15346154273610679900497863 23019231410416019850746795)
          ·
            refine ⟨34528847115624029776120193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23019231410416019850746795 34528847115624029776120193)
            ·
              refine ⟨25896635336718022332090145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34528847115624029776120193 25896635336718022332090145)
              ·
                refine ⟨19422476502538516749067609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25896635336718022332090145 19422476502538516749067609)
                ·
                  refine ⟨14566857376903887561800707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422476502538516749067609 14566857376903887561800707)
                  ·
                    refine ⟨21850286065355831342701061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14566857376903887561800707 21850286065355831342701061)
                    ·
                      refine ⟨4096928637254218376756449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21850286065355831342701061 4096928637254218376756449)
                      ·
                        rfl

theorem cell23_7978740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7978740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978740 prefixEnd_7978740 := by exact prefixLift 7978740
  have htrace : WordTrace (prefixWord ++ tailWord_7978740) baseStart_7978740 baseEnd_7978740 := by
    simpa [prefixWord, tailWord_7978740, baseEnd_7978740] using wordTrace_append hprefix tailTrace_7978740
  have hstable : (prefixWord ++ tailWord_7978740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978740).length < 2 ^ (prefixWord ++ tailWord_7978740).sum := by decide
  have hdescent : baseEnd_7978740 < baseStart_7978740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978773 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_7978773 : Nat := 118140960795 + 7978773 * 2 ^ 59
def prefixEnd_7978773 : Nat := 4983230072969 + 3 ^ 40 * 7978773 * 2
def baseEnd_7978773 : Nat := 4096945582115816747643797

theorem tailTrace_7978773 : CollatzResearch.WordTrace tailWord_7978773 prefixEnd_7978773 4096945582115816747643797 := by
  unfold tailWord_7978773
  simp only [CollatzResearch.WordTrace]
  refine ⟨291009758723275561786132973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194006505815517041190755315 291009758723275561786132973)
  ·
    refine ⟨109128659521228335669799865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291009758723275561786132973 109128659521228335669799865)
    ·
      refine ⟨81846494640921251752349899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109128659521228335669799865 81846494640921251752349899)
      ·
        refine ⟨122769741961381877628524849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81846494640921251752349899 122769741961381877628524849)
        ·
          refine ⟨92077306471036408221393637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122769741961381877628524849 92077306471036408221393637)
          ·
            refine ⟨17264494963319326541511307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92077306471036408221393637 17264494963319326541511307)
            ·
              refine ⟨25896742444978989812266961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264494963319326541511307 25896742444978989812266961)
              ·
                refine ⟨19422556833734242359200221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25896742444978989812266961 19422556833734242359200221)
                ·
                  refine ⟨7283458812650340884700083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19422556833734242359200221 7283458812650340884700083)
                  ·
                    refine ⟨10925188218975511327050125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283458812650340884700083 10925188218975511327050125)
                    ·
                      refine ⟨4096945582115816747643797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925188218975511327050125 4096945582115816747643797)
                      ·
                        rfl

theorem cell23_7978773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_7978773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978773 prefixEnd_7978773 := by exact prefixLift 7978773
  have htrace : WordTrace (prefixWord ++ tailWord_7978773) baseStart_7978773 baseEnd_7978773 := by
    simpa [prefixWord, tailWord_7978773, baseEnd_7978773] using wordTrace_append hprefix tailTrace_7978773
  have hstable : (prefixWord ++ tailWord_7978773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978773).length < 2 ^ (prefixWord ++ tailWord_7978773).sum := by decide
  have hdescent : baseEnd_7978773 < baseStart_7978773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978833 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_7978833 : Nat := 118140960795 + 7978833 * 2 ^ 59
def prefixEnd_7978833 : Nat := 4983230072969 + 3 ^ 40 * 7978833 * 2
def baseEnd_7978833 : Nat := 4096976390955086512893521

theorem tailTrace_7978833 : CollatzResearch.WordTrace tailWord_7978833 prefixEnd_7978833 4096976390955086512893521 := by
  unfold tailWord_7978833
  simp only [CollatzResearch.WordTrace]
  refine ⟨291011947103058192033317153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194007964735372128022211435 291011947103058192033317153)
  ·
    refine ⟨218258960327293644024987865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291011947103058192033317153 218258960327293644024987865)
    ·
      refine ⟨163694220245470233018740899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218258960327293644024987865 163694220245470233018740899)
      ·
        refine ⟨245541330368205349528111349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163694220245470233018740899 245541330368205349528111349)
        ·
          refine ⟨23019499722019251518260439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245541330368205349528111349 23019499722019251518260439)
          ·
            refine ⟨34529249583028877277390659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23019499722019251518260439 34529249583028877277390659)
            ·
              refine ⟨51793874374543315916085989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34529249583028877277390659 51793874374543315916085989)
              ·
                refine ⟨9711351445226871734266123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51793874374543315916085989 9711351445226871734266123)
                ·
                  refine ⟨14567027167840307601399185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9711351445226871734266123 14567027167840307601399185)
                  ·
                    refine ⟨10925270375880230701049389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14567027167840307601399185 10925270375880230701049389)
                    ·
                      refine ⟨4096976390955086512893521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925270375880230701049389 4096976390955086512893521)
                      ·
                        rfl

theorem cell23_7978833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_7978833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978833 prefixEnd_7978833 := by exact prefixLift 7978833
  have htrace : WordTrace (prefixWord ++ tailWord_7978833) baseStart_7978833 baseEnd_7978833 := by
    simpa [prefixWord, tailWord_7978833, baseEnd_7978833] using wordTrace_append hprefix tailTrace_7978833
  have hstable : (prefixWord ++ tailWord_7978833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978833).length < 2 ^ (prefixWord ++ tailWord_7978833).sum := by decide
  have hdescent : baseEnd_7978833 < baseStart_7978833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978836 : List Nat := [2, 4, 1, 1, 3, 2, 1, 9]
def baseStart_7978836 : Nat := 118140960795 + 7978836 * 2 ^ 59
def prefixEnd_7978836 : Nat := 4983230072969 + 3 ^ 40 * 7978836 * 2
def baseEnd_7978836 : Nat := 151739923385075925968741

theorem tailTrace_7978836 : CollatzResearch.WordTrace tailWord_7978836 prefixEnd_7978836 151739923385075925968741 := by
  unfold tailWord_7978836
  simp only [CollatzResearch.WordTrace]
  refine ⟨145506028261023661772838181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194008037681364882363784241 145506028261023661772838181)
  ·
    refine ⟨27282380298941936582407159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145506028261023661772838181 27282380298941936582407159)
    ·
      refine ⟨40923570448412904873610739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27282380298941936582407159 40923570448412904873610739)
      ·
        refine ⟨61385355672619357310416109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40923570448412904873610739 61385355672619357310416109)
        ·
          refine ⟨23019508377232258991406041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61385355672619357310416109 23019508377232258991406041)
          ·
            refine ⟨17264631282924194243554531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23019508377232258991406041 17264631282924194243554531)
            ·
              refine ⟨25896946924386291365331797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264631282924194243554531 25896946924386291365331797)
              ·
                refine ⟨151739923385075925968741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25896946924386291365331797 151739923385075925968741)
                ·
                  rfl

theorem cell23_7978836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 9].length) (baseStart_7978836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978836 prefixEnd_7978836 := by exact prefixLift 7978836
  have htrace : WordTrace (prefixWord ++ tailWord_7978836) baseStart_7978836 baseEnd_7978836 := by
    simpa [prefixWord, tailWord_7978836, baseEnd_7978836] using wordTrace_append hprefix tailTrace_7978836
  have hstable : (prefixWord ++ tailWord_7978836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978836).length < 2 ^ (prefixWord ++ tailWord_7978836).sum := by decide
  have hdescent : baseEnd_7978836 < baseStart_7978836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978847 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 1, 2, 2]
def baseStart_7978847 : Nat := 118140960795 + 7978847 * 2 ^ 59
def prefixEnd_7978847 : Nat := 4983230072969 + 3 ^ 40 * 7978847 * 2
def baseEnd_7978847 : Nat := 4096983579684249458118457

theorem tailTrace_7978847 : CollatzResearch.WordTrace tailWord_7978847 prefixEnd_7978847 4096983579684249458118457 := by
  unfold tailWord_7978847
  simp only [CollatzResearch.WordTrace]
  refine ⟨291012457725007472424326795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194008305150004981616217863 291012457725007472424326795)
  ·
    refine ⟨436518686587511208636490193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291012457725007472424326795 436518686587511208636490193)
    ·
      refine ⟨327389014940633406477367645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436518686587511208636490193 327389014940633406477367645)
      ·
        refine ⟨122770880602737527429012867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327389014940633406477367645 122770880602737527429012867)
        ·
          refine ⟨184156320904106291143519301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122770880602737527429012867 184156320904106291143519301)
          ·
            refine ⟨34529310169519929589409869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184156320904106291143519301 34529310169519929589409869)
            ·
              refine ⟨12948491313569973596028701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34529310169519929589409869 12948491313569973596028701)
              ·
                refine ⟨4855684242588740098510763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12948491313569973596028701 4855684242588740098510763)
                ·
                  refine ⟨7283526363883110147766145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855684242588740098510763 7283526363883110147766145)
                  ·
                    refine ⟨5462644772912332610824609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283526363883110147766145 5462644772912332610824609)
                    ·
                      refine ⟨4096983579684249458118457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462644772912332610824609 4096983579684249458118457)
                      ·
                        rfl

theorem cell23_7978847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_7978847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978847 prefixEnd_7978847 := by exact prefixLift 7978847
  have htrace : WordTrace (prefixWord ++ tailWord_7978847) baseStart_7978847 baseEnd_7978847 := by
    simpa [prefixWord, tailWord_7978847, baseEnd_7978847] using wordTrace_append hprefix tailTrace_7978847
  have hstable : (prefixWord ++ tailWord_7978847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978847).length < 2 ^ (prefixWord ++ tailWord_7978847).sum := by decide
  have hdescent : baseEnd_7978847 < baseStart_7978847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978850 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7978850 : Nat := 118140960795 + 7978850 * 2 ^ 59
def prefixEnd_7978850 : Nat := 4983230072969 + 3 ^ 40 * 7978850 * 2
def baseEnd_7978850 : Nat := 4096985120126212946380943

theorem tailTrace_7978850 : CollatzResearch.WordTrace tailWord_7978850 prefixEnd_7978850 4096985120126212946380943 := by
  unfold tailWord_7978850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72753141785999150984171501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194008378095997735957790669 72753141785999150984171501)
  ·
    refine ⟨27282428169749681619064313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72753141785999150984171501 27282428169749681619064313)
    ·
      refine ⟨20461821127312261214298235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27282428169749681619064313 20461821127312261214298235)
      ·
        refine ⟨30692731690968391821447353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20461821127312261214298235 30692731690968391821447353)
        ·
          refine ⟨23019548768226293866085515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30692731690968391821447353 23019548768226293866085515)
          ·
            refine ⟨34529323152339440799128273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23019548768226293866085515 34529323152339440799128273)
            ·
              refine ⟨25896992364254580599346205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34529323152339440799128273 25896992364254580599346205)
              ·
                refine ⟨9711372136595467724754827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25896992364254580599346205 9711372136595467724754827)
                ·
                  refine ⟨14567058204893201587132241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9711372136595467724754827 14567058204893201587132241)
                  ·
                    refine ⟨10925293653669901190349181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14567058204893201587132241 10925293653669901190349181)
                    ·
                      refine ⟨4096985120126212946380943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925293653669901190349181 4096985120126212946380943)
                      ·
                        rfl

theorem cell23_7978850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7978850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978850 prefixEnd_7978850 := by exact prefixLift 7978850
  have htrace : WordTrace (prefixWord ++ tailWord_7978850) baseStart_7978850 baseEnd_7978850 := by
    simpa [prefixWord, tailWord_7978850, baseEnd_7978850] using wordTrace_append hprefix tailTrace_7978850
  have hstable : (prefixWord ++ tailWord_7978850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978850).length < 2 ^ (prefixWord ++ tailWord_7978850).sum := by decide
  have hdescent : baseEnd_7978850 < baseStart_7978850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978859 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_7978859 : Nat := 118140960795 + 7978859 * 2 ^ 59
def prefixEnd_7978859 : Nat := 4983230072969 + 3 ^ 40 * 7978859 * 2
def baseEnd_7978859 : Nat := 4096989741452103411168401

theorem tailTrace_7978859 : CollatzResearch.WordTrace tailWord_7978859 prefixEnd_7978859 4096989741452103411168401 := by
  unfold tailWord_7978859
  simp only [CollatzResearch.WordTrace]
  refine ⟨291012895400963998473763631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194008596933975998982509087 291012895400963998473763631)
  ·
    refine ⟨436519343101445997710645447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291012895400963998473763631 436519343101445997710645447)
    ·
      refine ⟨654779014652168996565968171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436519343101445997710645447 654779014652168996565968171)
      ·
        refine ⟨982168521978253494848952257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654779014652168996565968171 982168521978253494848952257)
        ·
          refine ⟨736626391483690121136714193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982168521978253494848952257 736626391483690121136714193)
          ·
            refine ⟨552469793612767590852535645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736626391483690121136714193 552469793612767590852535645)
            ·
              refine ⟨207176172604787846569700867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552469793612767590852535645 207176172604787846569700867)
              ·
                refine ⟨310764258907181769854551301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207176172604787846569700867 310764258907181769854551301)
                ·
                  refine ⟨58268298545096581847728369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310764258907181769854551301 58268298545096581847728369)
                  ·
                    refine ⟨43701223908822436385796277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58268298545096581847728369 43701223908822436385796277)
                    ·
                      refine ⟨4096989741452103411168401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43701223908822436385796277 4096989741452103411168401)
                      ·
                        rfl

theorem cell23_7978859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_7978859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978859 prefixEnd_7978859 := by exact prefixLift 7978859
  have htrace : WordTrace (prefixWord ++ tailWord_7978859) baseStart_7978859 baseEnd_7978859 := by
    simpa [prefixWord, tailWord_7978859, baseEnd_7978859] using wordTrace_append hprefix tailTrace_7978859
  have hstable : (prefixWord ++ tailWord_7978859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978859).length < 2 ^ (prefixWord ++ tailWord_7978859).sum := by decide
  have hdescent : baseEnd_7978859 < baseStart_7978859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978873 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 3, 3, 2]
def baseStart_7978873 : Nat := 118140960795 + 7978873 * 2 ^ 59
def prefixEnd_7978873 : Nat := 4983230072969 + 3 ^ 40 * 7978873 * 2
def baseEnd_7978873 : Nat := 4096996930181266356393337

theorem tailTrace_7978873 : CollatzResearch.WordTrace tailWord_7978873 prefixEnd_7978873 4096996930181266356393337 := by
  unfold tailWord_7978873
  simp only [CollatzResearch.WordTrace]
  refine ⟨291013406022913278864773273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194008937348608852576515515 291013406022913278864773273)
  ·
    refine ⟨218260054517184959148579955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291013406022913278864773273 218260054517184959148579955)
    ·
      refine ⟨327390081775777438722869933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218260054517184959148579955 327390081775777438722869933)
      ·
        refine ⟨122771280665916539521076225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327390081775777438722869933 122771280665916539521076225)
        ·
          refine ⟨92078460499437404640807169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122771280665916539521076225 92078460499437404640807169)
          ·
            refine ⟨69058845374578053480605377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92078460499437404640807169 69058845374578053480605377)
            ·
              refine ⟨51794134030933540110454033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69058845374578053480605377 51794134030933540110454033)
              ·
                refine ⟨38845600523200155082840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51794134030933540110454033 38845600523200155082840525)
                ·
                  refine ⟨14567100196200058156065197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38845600523200155082840525 14567100196200058156065197)
                  ·
                    refine ⟨5462662573575021808524449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14567100196200058156065197 5462662573575021808524449)
                    ·
                      refine ⟨4096996930181266356393337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462662573575021808524449 4096996930181266356393337)
                      ·
                        rfl

theorem cell23_7978873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_7978873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978873 prefixEnd_7978873 := by exact prefixLift 7978873
  have htrace : WordTrace (prefixWord ++ tailWord_7978873) baseStart_7978873 baseEnd_7978873 := by
    simpa [prefixWord, tailWord_7978873, baseEnd_7978873] using wordTrace_append hprefix tailTrace_7978873
  have hstable : (prefixWord ++ tailWord_7978873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978873).length < 2 ^ (prefixWord ++ tailWord_7978873).sum := by decide
  have hdescent : baseEnd_7978873 < baseStart_7978873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978879 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 8]
def baseStart_7978879 : Nat := 118140960795 + 7978879 * 2 ^ 59
def prefixEnd_7978879 : Nat := 4983230072969 + 3 ^ 40 * 7978879 * 2
def baseEnd_7978879 : Nat := 1365666670355064444306103

theorem tailTrace_7978879 : CollatzResearch.WordTrace tailWord_7978879 prefixEnd_7978879 1365666670355064444306103 := by
  unfold tailWord_7978879
  simp only [CollatzResearch.WordTrace]
  refine ⟨291013624860891541889491691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194009083240594361259661127 291013624860891541889491691)
  ·
    refine ⟨436520437291337312834237537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291013624860891541889491691 436520437291337312834237537)
    ·
      refine ⟨327390327968502984625678153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436520437291337312834237537 327390327968502984625678153)
      ·
        refine ⟨245542745976377238469258615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327390327968502984625678153 245542745976377238469258615)
        ·
          refine ⟨368314118964565857703887923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245542745976377238469258615 368314118964565857703887923)
          ·
            refine ⟨552471178446848786555831885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368314118964565857703887923 552471178446848786555831885)
            ·
              refine ⟨207176691917568294958436957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552471178446848786555831885 207176691917568294958436957)
              ·
                refine ⟨77691259469088110609413859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207176691917568294958436957 77691259469088110609413859)
                ·
                  refine ⟨116536889203632165914120789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77691259469088110609413859 116536889203632165914120789)
                  ·
                    refine ⟨1365666670355064444306103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116536889203632165914120789 1365666670355064444306103)
                    ·
                      rfl

theorem cell23_7978879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_7978879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978879 prefixEnd_7978879 := by exact prefixLift 7978879
  have htrace : WordTrace (prefixWord ++ tailWord_7978879) baseStart_7978879 baseEnd_7978879 := by
    simpa [prefixWord, tailWord_7978879, baseEnd_7978879] using wordTrace_append hprefix tailTrace_7978879
  have hstable : (prefixWord ++ tailWord_7978879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978879).length < 2 ^ (prefixWord ++ tailWord_7978879).sum := by decide
  have hdescent : baseEnd_7978879 < baseStart_7978879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978899 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_7978899 : Nat := 118140960795 + 7978899 * 2 ^ 59
def prefixEnd_7978899 : Nat := 4983230072969 + 3 ^ 40 * 7978899 * 2
def baseEnd_7978899 : Nat := 4097010280678283254668217

theorem tailTrace_7978899 : CollatzResearch.WordTrace tailWord_7978899 prefixEnd_7978899 4097010280678283254668217 := by
  unfold tailWord_7978899
  simp only [CollatzResearch.WordTrace]
  refine ⟨291014354320819085305219751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194009569547212723536813167 291014354320819085305219751)
  ·
    refine ⟨436521531481228627957829627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291014354320819085305219751 436521531481228627957829627)
    ·
      refine ⟨654782297221842941936744441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436521531481228627957829627 654782297221842941936744441)
      ·
        refine ⟨491086722916382206452558331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654782297221842941936744441 491086722916382206452558331)
        ·
          refine ⟨736630084374573309678837497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491086722916382206452558331 736630084374573309678837497)
          ·
            refine ⟨552472563280929982259128123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736630084374573309678837497 552472563280929982259128123)
            ·
              refine ⟨828708844921394973388692185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552472563280929982259128123 828708844921394973388692185)
              ·
                refine ⟨621531633691046230041519139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828708844921394973388692185 621531633691046230041519139)
                ·
                  refine ⟨932297450536569345062278709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621531633691046230041519139 932297450536569345062278709)
                  ·
                    refine ⟨87402885987803376099588629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 932297450536569345062278709 87402885987803376099588629)
                    ·
                      refine ⟨4097010280678283254668217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87402885987803376099588629 4097010280678283254668217)
                      ·
                        rfl

theorem cell23_7978899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_7978899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978899 prefixEnd_7978899 := by exact prefixLift 7978899
  have htrace : WordTrace (prefixWord ++ tailWord_7978899) baseStart_7978899 baseEnd_7978899 := by
    simpa [prefixWord, tailWord_7978899, baseEnd_7978899] using wordTrace_append hprefix tailTrace_7978899
  have hstable : (prefixWord ++ tailWord_7978899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978899).length < 2 ^ (prefixWord ++ tailWord_7978899).sum := by decide
  have hdescent : baseEnd_7978899 < baseStart_7978899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978903 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7978903 : Nat := 118140960795 + 7978903 * 2 ^ 59
def prefixEnd_7978903 : Nat := 4983230072969 + 3 ^ 40 * 7978903 * 2
def baseEnd_7978903 : Nat := 4097012334600901239018199

theorem tailTrace_7978903 : CollatzResearch.WordTrace tailWord_7978903 prefixEnd_7978903 4097012334600901239018199 := by
  unfold tailWord_7978903
  simp only [CollatzResearch.WordTrace]
  refine ⟨291014500212804593988365363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194009666808536395992243575 291014500212804593988365363)
  ·
    refine ⟨436521750319206890982548045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291014500212804593988365363 436521750319206890982548045)
    ·
      refine ⟨163695656369702584118455517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436521750319206890982548045 163695656369702584118455517)
      ·
        refine ⟨61385871138638469044420819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163695656369702584118455517 61385871138638469044420819)
        ·
          refine ⟨92078806707957703566631229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61385871138638469044420819 92078806707957703566631229)
          ·
            refine ⟨34529552515484138837486711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92078806707957703566631229 34529552515484138837486711)
            ·
              refine ⟨51794328773226208256230067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34529552515484138837486711 51794328773226208256230067)
              ·
                refine ⟨77691493159839312384345101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51794328773226208256230067 77691493159839312384345101)
                ·
                  refine ⟨29134309934939742144129413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77691493159839312384345101 29134309934939742144129413)
                  ·
                    refine ⟨5462683112801201652024265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29134309934939742144129413 5462683112801201652024265)
                    ·
                      refine ⟨4097012334600901239018199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462683112801201652024265 4097012334600901239018199)
                      ·
                        rfl

theorem cell23_7978903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7978903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978903 prefixEnd_7978903 := by exact prefixLift 7978903
  have htrace : WordTrace (prefixWord ++ tailWord_7978903) baseStart_7978903 baseEnd_7978903 := by
    simpa [prefixWord, tailWord_7978903, baseEnd_7978903] using wordTrace_append hprefix tailTrace_7978903
  have hstable : (prefixWord ++ tailWord_7978903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978903).length < 2 ^ (prefixWord ++ tailWord_7978903).sum := by decide
  have hdescent : baseEnd_7978903 < baseStart_7978903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7978933 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7978933 : Nat := 118140960795 + 7978933 * 2 ^ 59
def prefixEnd_7978933 : Nat := 4983230072969 + 3 ^ 40 * 7978933 * 2
def baseEnd_7978933 : Nat := 4097027739020536121643061

theorem tailTrace_7978933 : CollatzResearch.WordTrace tailWord_7978933 prefixEnd_7978933 4097027739020536121643061 := by
  unfold tailWord_7978933
  simp only [CollatzResearch.WordTrace]
  refine ⟨291015594402695909111957453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194010396268463939407971635 291015594402695909111957453)
  ·
    refine ⟨109130847901010965916984045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291015594402695909111957453 109130847901010965916984045)
    ·
      refine ⟨40924067962879112218869017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109130847901010965916984045 40924067962879112218869017)
      ·
        refine ⟨30693050972159334164151763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40924067962879112218869017 30693050972159334164151763)
        ·
          refine ⟨46039576458239001246227645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30693050972159334164151763 46039576458239001246227645)
          ·
            refine ⟨17264841171839625467335367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46039576458239001246227645 17264841171839625467335367)
            ·
              refine ⟨25897261757759438201003051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264841171839625467335367 25897261757759438201003051)
              ·
                refine ⟨38845892636639157301504577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25897261757759438201003051 38845892636639157301504577)
                ·
                  refine ⟨29134419477479367976128433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38845892636639157301504577 29134419477479367976128433)
                  ·
                    refine ⟨21850814608109525982096325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29134419477479367976128433 21850814608109525982096325)
                    ·
                      refine ⟨4097027739020536121643061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21850814608109525982096325 4097027739020536121643061)
                      ·
                        rfl

theorem cell23_7978933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7978933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7978933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7978933 prefixEnd_7978933 := by exact prefixLift 7978933
  have htrace : WordTrace (prefixWord ++ tailWord_7978933) baseStart_7978933 baseEnd_7978933 := by
    simpa [prefixWord, tailWord_7978933, baseEnd_7978933] using wordTrace_append hprefix tailTrace_7978933
  have hstable : (prefixWord ++ tailWord_7978933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7978933).length < 2 ^ (prefixWord ++ tailWord_7978933).sum := by decide
  have hdescent : baseEnd_7978933 < baseStart_7978933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7978933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979003 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 3, 4]
def baseStart_7979003 : Nat := 118140960795 + 7979003 * 2 ^ 59
def prefixEnd_7979003 : Nat := 4983230072969 + 3 ^ 40 * 7979003 * 2
def baseEnd_7979003 : Nat := 1365687894222116949255913

theorem tailTrace_7979003 : CollatzResearch.WordTrace tailWord_7979003 prefixEnd_7979003 1365687894222116949255913 := by
  unfold tailWord_7979003
  simp only [CollatzResearch.WordTrace]
  refine ⟨291018147512442311067005663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194012098341628207378003775 291018147512442311067005663)
  ·
    refine ⟨436527221268663466600508495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291018147512442311067005663 436527221268663466600508495)
    ·
      refine ⟨654790831902995199900762743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436527221268663466600508495 654790831902995199900762743)
      ·
        refine ⟨982186247854492799851144115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654790831902995199900762743 982186247854492799851144115)
        ·
          refine ⟨1473279371781739199776716173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982186247854492799851144115 1473279371781739199776716173)
          ·
            refine ⟨552479764418152199916268565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1473279371781739199776716173 552479764418152199916268565)
            ·
              refine ⟨25897488957100884371075089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 552479764418152199916268565 25897488957100884371075089)
              ·
                refine ⟨19423116717825663278306317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25897488957100884371075089 19423116717825663278306317)
                ·
                  refine ⟨7283668769184623729364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19423116717825663278306317 7283668769184623729364869)
                  ·
                    refine ⟨1365687894222116949255913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283668769184623729364869 1365687894222116949255913)
                    ·
                      rfl

theorem cell23_7979003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 4].length) (baseStart_7979003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979003 prefixEnd_7979003 := by exact prefixLift 7979003
  have htrace : WordTrace (prefixWord ++ tailWord_7979003) baseStart_7979003 baseEnd_7979003 := by
    simpa [prefixWord, tailWord_7979003, baseEnd_7979003] using wordTrace_append hprefix tailTrace_7979003
  have hstable : (prefixWord ++ tailWord_7979003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979003).length < 2 ^ (prefixWord ++ tailWord_7979003).sum := by decide
  have hdescent : baseEnd_7979003 < baseStart_7979003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979013 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_7979013 : Nat := 118140960795 + 7979013 * 2 ^ 59
def prefixEnd_7979013 : Nat := 4983230072969 + 3 ^ 40 * 7979013 * 2
def baseEnd_7979013 : Nat := 4097068817472895808642693

theorem tailTrace_7979013 : CollatzResearch.WordTrace tailWord_7979013 prefixEnd_7979013 4097068817472895808642693 := by
  unfold tailWord_7979013
  simp only [CollatzResearch.WordTrace]
  refine ⟨291018512242406082774869693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194012341494937388516579795 291018512242406082774869693)
  ·
    refine ⟨109131942090902281040576135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291018512242406082774869693 109131942090902281040576135)
    ·
      refine ⟨163697913136353421560864203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109131942090902281040576135 163697913136353421560864203)
      ·
        refine ⟨245546869704530132341296305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163697913136353421560864203 245546869704530132341296305)
        ·
          refine ⟨184160152278397599255972229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245546869704530132341296305 184160152278397599255972229)
          ·
            refine ⟨34530028552199549860494793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184160152278397599255972229 34530028552199549860494793)
            ·
              refine ⟨25897521414149662395371095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34530028552199549860494793 25897521414149662395371095)
              ·
                refine ⟨38846282121224493593056643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25897521414149662395371095 38846282121224493593056643)
                ·
                  refine ⟨58269423181836740389584965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38846282121224493593056643 58269423181836740389584965)
                  ·
                    refine ⟨10925516846594388823047181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58269423181836740389584965 10925516846594388823047181)
                    ·
                      refine ⟨4097068817472895808642693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925516846594388823047181 4097068817472895808642693)
                      ·
                        rfl

theorem cell23_7979013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_7979013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979013 prefixEnd_7979013 := by exact prefixLift 7979013
  have htrace : WordTrace (prefixWord ++ tailWord_7979013) baseStart_7979013 baseEnd_7979013 := by
    simpa [prefixWord, tailWord_7979013, baseEnd_7979013] using wordTrace_append hprefix tailTrace_7979013
  have hstable : (prefixWord ++ tailWord_7979013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979013).length < 2 ^ (prefixWord ++ tailWord_7979013).sum := by decide
  have hdescent : baseEnd_7979013 < baseStart_7979013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979016 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 10]
def baseStart_7979016 : Nat := 118140960795 + 7979016 * 2 ^ 59
def prefixEnd_7979016 : Nat := 4983230072969 + 3 ^ 40 * 7979016 * 2
def baseEnd_7979016 : Nat := 455230039768317699656131

theorem tailTrace_7979016 : CollatzResearch.WordTrace tailWord_7979016 prefixEnd_7979016 455230039768317699656131 := by
  unfold tailWord_7979016
  simp only [CollatzResearch.WordTrace]
  refine ⟨145509310830697607143614451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194012414440930142858152601 145509310830697607143614451)
  ·
    refine ⟨218263966246046410715421677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145509310830697607143614451 218263966246046410715421677)
    ·
      refine ⟨81848987342267404018283129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218263966246046410715421677 81848987342267404018283129)
      ·
        refine ⟨61386740506700553013712347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81848987342267404018283129 61386740506700553013712347)
        ·
          refine ⟨92080110760050829520568521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61386740506700553013712347 92080110760050829520568521)
          ·
            refine ⟨69060083070038122140426391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92080110760050829520568521 69060083070038122140426391)
            ·
              refine ⟨103590124605057183210639587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69060083070038122140426391 103590124605057183210639587)
              ·
                refine ⟨155385186907585774815959381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103590124605057183210639587 155385186907585774815959381)
                ·
                  refine ⟨455230039768317699656131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155385186907585774815959381 455230039768317699656131)
                  ·
                    rfl

theorem cell23_7979016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_7979016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979016 prefixEnd_7979016 := by exact prefixLift 7979016
  have htrace : WordTrace (prefixWord ++ tailWord_7979016) baseStart_7979016 baseEnd_7979016 := by
    simpa [prefixWord, tailWord_7979016, baseEnd_7979016] using wordTrace_append hprefix tailTrace_7979016
  have hstable : (prefixWord ++ tailWord_7979016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979016).length < 2 ^ (prefixWord ++ tailWord_7979016).sum := by decide
  have hdescent : baseEnd_7979016 < baseStart_7979016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979037 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7979037 : Nat := 118140960795 + 7979037 * 2 ^ 59
def prefixEnd_7979037 : Nat := 4983230072969 + 3 ^ 40 * 7979037 * 2
def baseEnd_7979037 : Nat := 1365693713669534571580861

theorem tailTrace_7979037 : CollatzResearch.WordTrace tailWord_7979037 prefixEnd_7979037 1365693713669534571580861 := by
  unfold tailWord_7979037
  simp only [CollatzResearch.WordTrace]
  refine ⟨291019387594319134873743365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194012925062879423249162243 291019387594319134873743365)
  ·
    refine ⟨54566135173934837788826881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291019387594319134873743365 54566135173934837788826881)
    ·
      refine ⟨40924601380451128341620161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54566135173934837788826881 40924601380451128341620161)
      ·
        refine ⟨30693451035338346256215121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40924601380451128341620161 30693451035338346256215121)
        ·
          refine ⟨23020088276503759692161341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30693451035338346256215121 23020088276503759692161341)
          ·
            refine ⟨8632533103688909884560503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23020088276503759692161341 8632533103688909884560503)
            ·
              refine ⟨12948799655533364826840755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632533103688909884560503 12948799655533364826840755)
              ·
                refine ⟨19423199483300047240261133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948799655533364826840755 19423199483300047240261133)
                ·
                  refine ⟨7283699806237517715097925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19423199483300047240261133 7283699806237517715097925)
                  ·
                    refine ⟨1365693713669534571580861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283699806237517715097925 1365693713669534571580861)
                    ·
                      rfl

theorem cell23_7979037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7979037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979037 prefixEnd_7979037 := by exact prefixLift 7979037
  have htrace : WordTrace (prefixWord ++ tailWord_7979037) baseStart_7979037 baseEnd_7979037 := by
    simpa [prefixWord, tailWord_7979037, baseEnd_7979037] using wordTrace_append hprefix tailTrace_7979037
  have hstable : (prefixWord ++ tailWord_7979037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979037).length < 2 ^ (prefixWord ++ tailWord_7979037).sum := by decide
  have hdescent : baseEnd_7979037 < baseStart_7979037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979050 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_7979050 : Nat := 118140960795 + 7979050 * 2 ^ 59
def prefixEnd_7979050 : Nat := 4983230072969 + 3 ^ 40 * 7979050 * 2
def baseEnd_7979050 : Nat := 455231979584123573764447

theorem tailTrace_7979050 : CollatzResearch.WordTrace tailWord_7979050 prefixEnd_7979050 455231979584123573764447 := by
  unfold tailWord_7979050
  simp only [CollatzResearch.WordTrace]
  refine ⟨72754965435818009523491651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194013241162181358729311069 72754965435818009523491651)
  ·
    refine ⟨109132448153727014285237477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72754965435818009523491651 109132448153727014285237477)
    ·
      refine ⟨20462334028823815178482027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109132448153727014285237477 20462334028823815178482027)
      ·
        refine ⟨30693501043235722767723041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20462334028823815178482027 30693501043235722767723041)
        ·
          refine ⟨23020125782426792075792281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30693501043235722767723041 23020125782426792075792281)
          ·
            refine ⟨17265094336820094056844211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23020125782426792075792281 17265094336820094056844211)
            ·
              refine ⟨25897641505230141085266317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17265094336820094056844211 25897641505230141085266317)
              ·
                refine ⟨9711615564461302906974869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25897641505230141085266317 9711615564461302906974869)
                ·
                  refine ⟨455231979584123573764447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9711615564461302906974869 455231979584123573764447)
                  ·
                    rfl

theorem cell23_7979050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_7979050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979050 prefixEnd_7979050 := by exact prefixLift 7979050
  have htrace : WordTrace (prefixWord ++ tailWord_7979050) baseStart_7979050 baseEnd_7979050 := by
    simpa [prefixWord, tailWord_7979050, baseEnd_7979050] using wordTrace_append hprefix tailTrace_7979050
  have hstable : (prefixWord ++ tailWord_7979050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979050).length < 2 ^ (prefixWord ++ tailWord_7979050).sum := by decide
  have hdescent : baseEnd_7979050 < baseStart_7979050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979077 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 1, 1, 3]
def baseStart_7979077 : Nat := 118140960795 + 7979077 * 2 ^ 59
def prefixEnd_7979077 : Nat := 4983230072969 + 3 ^ 40 * 7979077 * 2
def baseEnd_7979077 : Nat := 4097101680234783558242399

theorem tailTrace_7979077 : CollatzResearch.WordTrace tailWord_7979077 prefixEnd_7979077 4097101680234783558242399 := by
  unfold tailWord_7979077
  simp only [CollatzResearch.WordTrace]
  refine ⟨291020846514174221705199485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194013897676116147803466323 291020846514174221705199485)
  ·
    refine ⟨109132817442815333139449807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291020846514174221705199485 109132817442815333139449807)
    ·
      refine ⟨163699226164222999709174711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109132817442815333139449807 163699226164222999709174711)
      ·
        refine ⟨245548839246334499563762067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163699226164222999709174711 245548839246334499563762067)
        ·
          refine ⟨368323258869501749345643101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245548839246334499563762067 368323258869501749345643101)
          ·
            refine ⟨138121222076063156004616163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368323258869501749345643101 138121222076063156004616163)
            ·
              refine ⟨207181833114094734006924245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138121222076063156004616163 207181833114094734006924245)
              ·
                refine ⟨4855824213611595328287287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207181833114094734006924245 4855824213611595328287287)
                ·
                  refine ⟨7283736320417392992430931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855824213611595328287287 7283736320417392992430931)
                  ·
                    refine ⟨10925604480626089488646397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283736320417392992430931 10925604480626089488646397)
                    ·
                      refine ⟨4097101680234783558242399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925604480626089488646397 4097101680234783558242399)
                      ·
                        rfl

theorem cell23_7979077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_7979077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979077 prefixEnd_7979077 := by exact prefixLift 7979077
  have htrace : WordTrace (prefixWord ++ tailWord_7979077) baseStart_7979077 baseEnd_7979077 := by
    simpa [prefixWord, tailWord_7979077, baseEnd_7979077] using wordTrace_append hprefix tailTrace_7979077
  have hstable : (prefixWord ++ tailWord_7979077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979077).length < 2 ^ (prefixWord ++ tailWord_7979077).sum := by decide
  have hdescent : baseEnd_7979077 < baseStart_7979077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979100 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7979100 : Nat := 118140960795 + 7979100 * 2 ^ 59
def prefixEnd_7979100 : Nat := 4983230072969 + 3 ^ 40 * 7979100 * 2
def baseEnd_7979100 : Nat := 4097113490289836968254793

theorem tailTrace_7979100 : CollatzResearch.WordTrace tailWord_7979100 prefixEnd_7979100 4097113490289836968254793 := by
  unfold tailWord_7979100
  simp only [CollatzResearch.WordTrace]
  refine ⟨145510842696545448316643377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194014456928727264422191169 145510842696545448316643377)
  ·
    refine ⟨109133132022409086237482533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145510842696545448316643377 109133132022409086237482533)
    ·
      refine ⟨20462462254201703669527975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109133132022409086237482533 20462462254201703669527975)
      ·
        refine ⟨30693693381302555504291963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20462462254201703669527975 30693693381302555504291963)
        ·
          refine ⟨46040540071953833256437945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30693693381302555504291963 46040540071953833256437945)
          ·
            refine ⟨34530405053965374942328459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46040540071953833256437945 34530405053965374942328459)
            ·
              refine ⟨51795607580948062413492689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34530405053965374942328459 51795607580948062413492689)
              ·
                refine ⟨38846705685711046810119517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51795607580948062413492689 38846705685711046810119517)
                ·
                  refine ⟨14567514632141642553794819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38846705685711046810119517 14567514632141642553794819)
                  ·
                    refine ⟨21851271948212463830692229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14567514632141642553794819 21851271948212463830692229)
                    ·
                      refine ⟨4097113490289836968254793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21851271948212463830692229 4097113490289836968254793)
                      ·
                        rfl

theorem cell23_7979100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7979100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979100 prefixEnd_7979100 := by exact prefixLift 7979100
  have htrace : WordTrace (prefixWord ++ tailWord_7979100) baseStart_7979100 baseEnd_7979100 := by
    simpa [prefixWord, tailWord_7979100, baseEnd_7979100] using wordTrace_append hprefix tailTrace_7979100
  have hstable : (prefixWord ++ tailWord_7979100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979100).length < 2 ^ (prefixWord ++ tailWord_7979100).sum := by decide
  have hdescent : baseEnd_7979100 < baseStart_7979100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979120 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_7979120 : Nat := 118140960795 + 7979120 * 2 ^ 59
def prefixEnd_7979120 : Nat := 4983230072969 + 3 ^ 40 * 7979120 * 2
def baseEnd_7979120 : Nat := 4097123759902926890004701

theorem tailTrace_7979120 : CollatzResearch.WordTrace tailWord_7979120 prefixEnd_7979120 4097123759902926890004701 := by
  unfold tailWord_7979120
  simp only [CollatzResearch.WordTrace]
  refine ⟨145511207426509220024507407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194014943235345626699343209 145511207426509220024507407)
  ·
    refine ⟨218266811139763830036761111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145511207426509220024507407 218266811139763830036761111)
    ·
      refine ⟨327400216709645745055141667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218266811139763830036761111 327400216709645745055141667)
      ·
        refine ⟨491100325064468617582712501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327400216709645745055141667 491100325064468617582712501)
        ·
          refine ⟨46040655474793932898379297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491100325064468617582712501 46040655474793932898379297)
          ·
            refine ⟨34530491606095449673784473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46040655474793932898379297 34530491606095449673784473)
            ·
              refine ⟨25897868704571587255338355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34530491606095449673784473 25897868704571587255338355)
              ·
                refine ⟨38846803056857380883007533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25897868704571587255338355 38846803056857380883007533)
                ·
                  refine ⟨14567551146321517831127825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38846803056857380883007533 14567551146321517831127825)
                  ·
                    refine ⟨10925663359741138373345869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14567551146321517831127825 10925663359741138373345869)
                    ·
                      refine ⟨4097123759902926890004701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925663359741138373345869 4097123759902926890004701)
                      ·
                        rfl

theorem cell23_7979120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_7979120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979120 prefixEnd_7979120 := by exact prefixLift 7979120
  have htrace : WordTrace (prefixWord ++ tailWord_7979120) baseStart_7979120 baseEnd_7979120 := by
    simpa [prefixWord, tailWord_7979120, baseEnd_7979120] using wordTrace_append hprefix tailTrace_7979120
  have hstable : (prefixWord ++ tailWord_7979120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979120).length < 2 ^ (prefixWord ++ tailWord_7979120).sum := by decide
  have hdescent : baseEnd_7979120 < baseStart_7979120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979144 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_7979144 : Nat := 118140960795 + 7979144 * 2 ^ 59
def prefixEnd_7979144 : Nat := 4983230072969 + 3 ^ 40 * 7979144 * 2
def baseEnd_7979144 : Nat := 1365712027812878265368197

theorem tailTrace_7979144 : CollatzResearch.WordTrace tailWord_7979144 prefixEnd_7979144 1365712027812878265368197 := by
  unfold tailWord_7979144
  simp only [CollatzResearch.WordTrace]
  refine ⟨145511645102465746073944243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194015526803287661431925657 145511645102465746073944243)
  ·
    refine ⟨218267467653698619110916365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145511645102465746073944243 218267467653698619110916365)
    ·
      refine ⟨81850300370136982166593637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218267467653698619110916365 81850300370136982166593637)
      ·
        refine ⟨15346931319400684156236307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81850300370136982166593637 15346931319400684156236307)
        ·
          refine ⟨23020396979101026234354461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15346931319400684156236307 23020396979101026234354461)
          ·
            refine ⟨8632648867162884837882923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23020396979101026234354461 8632648867162884837882923)
            ·
              refine ⟨12948973300744327256824385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632648867162884837882923 12948973300744327256824385)
              ·
                refine ⟨9711729975558245442618289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12948973300744327256824385 9711729975558245442618289)
                ·
                  refine ⟨7283797481668684081963717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9711729975558245442618289 7283797481668684081963717)
                  ·
                    refine ⟨1365712027812878265368197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283797481668684081963717 1365712027812878265368197)
                    ·
                      rfl

theorem cell23_7979144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_7979144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979144 prefixEnd_7979144 := by exact prefixLift 7979144
  have htrace : WordTrace (prefixWord ++ tailWord_7979144) baseStart_7979144 baseEnd_7979144 := by
    simpa [prefixWord, tailWord_7979144, baseEnd_7979144] using wordTrace_append hprefix tailTrace_7979144
  have hstable : (prefixWord ++ tailWord_7979144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979144).length < 2 ^ (prefixWord ++ tailWord_7979144).sum := by decide
  have hdescent : baseEnd_7979144 < baseStart_7979144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979167 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7979167 : Nat := 118140960795 + 7979167 * 2 ^ 59
def prefixEnd_7979167 : Nat := 4983230072969 + 3 ^ 40 * 7979167 * 2
def baseEnd_7979167 : Nat := 4097147893493688206116985

theorem tailTrace_7979167 : CollatzResearch.WordTrace tailWord_7979167 prefixEnd_7979167 4097147893493688206116985 := by
  unfold tailWord_7979167
  simp only [CollatzResearch.WordTrace]
  refine ⟨291024129083848167075975755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194016086055898778050650503 291024129083848167075975755)
  ·
    refine ⟨436536193625772250613963633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291024129083848167075975755 436536193625772250613963633)
    ·
      refine ⟨327402145219329187960472725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436536193625772250613963633 327402145219329187960472725)
      ·
        refine ⟨15346975557156055685647159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 327402145219329187960472725 15346975557156055685647159)
        ·
          refine ⟨23020463335734083528470739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15346975557156055685647159 23020463335734083528470739)
          ·
            refine ⟨34530695003601125292706109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23020463335734083528470739 34530695003601125292706109)
            ·
              refine ⟨12949010626350421984764791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34530695003601125292706109 12949010626350421984764791)
              ·
                refine ⟨19423515939525632977147187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949010626350421984764791 19423515939525632977147187)
                ·
                  refine ⟨29135273909288449465720781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19423515939525632977147187 29135273909288449465720781)
                  ·
                    refine ⟨10925727715983168549645293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29135273909288449465720781 10925727715983168549645293)
                    ·
                      refine ⟨4097147893493688206116985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925727715983168549645293 4097147893493688206116985)
                      ·
                        rfl

theorem cell23_7979167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7979167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979167 prefixEnd_7979167 := by exact prefixLift 7979167
  have htrace : WordTrace (prefixWord ++ tailWord_7979167) baseStart_7979167 baseEnd_7979167 := by
    simpa [prefixWord, tailWord_7979167, baseEnd_7979167] using wordTrace_append hprefix tailTrace_7979167
  have hstable : (prefixWord ++ tailWord_7979167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979167).length < 2 ^ (prefixWord ++ tailWord_7979167).sum := by decide
  have hdescent : baseEnd_7979167 < baseStart_7979167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979185 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7979185 : Nat := 118140960795 + 7979185 * 2 ^ 59
def prefixEnd_7979185 : Nat := 4983230072969 + 3 ^ 40 * 7979185 * 2
def baseEnd_7979185 : Nat := 4097157136145469135691903

theorem tailTrace_7979185 : CollatzResearch.WordTrace tailWord_7979185 prefixEnd_7979185 4097157136145469135691903 := by
  unfold tailWord_7979185
  simp only [CollatzResearch.WordTrace]
  refine ⟨291024785597782956150131009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194016523731855304100087339 291024785597782956150131009)
  ·
    refine ⟨218268589198337217112598257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291024785597782956150131009 218268589198337217112598257)
    ·
      refine ⟨163701441898752912834448693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218268589198337217112598257 163701441898752912834448693)
      ·
        refine ⟨15347010178008085578229565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163701441898752912834448693 15347010178008085578229565)
        ·
          refine ⟨5755128816753032091836087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15347010178008085578229565 5755128816753032091836087)
          ·
            refine ⟨8632693225129548137754131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755128816753032091836087 8632693225129548137754131)
            ·
              refine ⟨12949039837694322206631197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632693225129548137754131 12949039837694322206631197)
              ·
                refine ⟨4855889939135370827486699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949039837694322206631197 4855889939135370827486699)
                ·
                  refine ⟨7283834908703056241230049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855889939135370827486699 7283834908703056241230049)
                  ·
                    refine ⟨5462876181527292180922537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283834908703056241230049 5462876181527292180922537)
                    ·
                      refine ⟨4097157136145469135691903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462876181527292180922537 4097157136145469135691903)
                      ·
                        rfl

theorem cell23_7979185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7979185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979185 prefixEnd_7979185 := by exact prefixLift 7979185
  have htrace : WordTrace (prefixWord ++ tailWord_7979185) baseStart_7979185 baseEnd_7979185 := by
    simpa [prefixWord, tailWord_7979185, baseEnd_7979185] using wordTrace_append hprefix tailTrace_7979185
  have hstable : (prefixWord ++ tailWord_7979185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979185).length < 2 ^ (prefixWord ++ tailWord_7979185).sum := by decide
  have hdescent : baseEnd_7979185 < baseStart_7979185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979202 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7979202 : Nat := 118140960795 + 7979202 * 2 ^ 59
def prefixEnd_7979202 : Nat := 4983230072969 + 3 ^ 40 * 7979202 * 2
def baseEnd_7979202 : Nat := 4097165865316595569179325

theorem tailTrace_7979202 : CollatzResearch.WordTrace tailWord_7979202 prefixEnd_7979202 4097165865316595569179325 := by
  unfold tailWord_7979202
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756351409680342013374965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194016937092480912035666573 72756351409680342013374965)
  ·
    refine ⟨6820907944657532063753903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72756351409680342013374965 6820907944657532063753903)
    ·
      refine ⟨10231361916986298095630855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820907944657532063753903 10231361916986298095630855)
      ·
        refine ⟨15347042875479447143446283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231361916986298095630855 15347042875479447143446283)
        ·
          refine ⟨23020564313219170715169425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347042875479447143446283 23020564313219170715169425)
          ·
            refine ⟨17265423234914378036377069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23020564313219170715169425 17265423234914378036377069)
            ·
              refine ⟨6474533713092891763641401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17265423234914378036377069 6474533713092891763641401)
              ·
                refine ⟨4855900284819668822731051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474533713092891763641401 4855900284819668822731051)
                ·
                  refine ⟨7283850427229503234096577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855900284819668822731051 7283850427229503234096577)
                  ·
                    refine ⟨5462887820422127425572433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283850427229503234096577 5462887820422127425572433)
                    ·
                      refine ⟨4097165865316595569179325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5462887820422127425572433 4097165865316595569179325)
                      ·
                        rfl

theorem cell23_7979202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7979202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979202 prefixEnd_7979202 := by exact prefixLift 7979202
  have htrace : WordTrace (prefixWord ++ tailWord_7979202) baseStart_7979202 baseEnd_7979202 := by
    simpa [prefixWord, tailWord_7979202, baseEnd_7979202] using wordTrace_append hprefix tailTrace_7979202
  have hstable : (prefixWord ++ tailWord_7979202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979202).length < 2 ^ (prefixWord ++ tailWord_7979202).sum := by decide
  have hdescent : baseEnd_7979202 < baseStart_7979202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979210 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_7979210 : Nat := 118140960795 + 7979210 * 2 ^ 59
def prefixEnd_7979210 : Nat := 4983230072969 + 3 ^ 40 * 7979210 * 2
def baseEnd_7979210 : Nat := 4097169973161831537879287

theorem tailTrace_7979210 : CollatzResearch.WordTrace tailWord_7979210 prefixEnd_7979210 4097169973161831537879287 := by
  unfold tailWord_7979210
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756424355673096354947771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194017131615128256946527389 72756424355673096354947771)
  ·
    refine ⟨109134636533509644532421657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72756424355673096354947771 109134636533509644532421657)
    ·
      refine ⟨81850977400132233399316243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109134636533509644532421657 81850977400132233399316243)
      ·
        refine ⟨122776466100198350098974365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81850977400132233399316243 122776466100198350098974365)
        ·
          refine ⟨46041174787574381287115387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122776466100198350098974365 46041174787574381287115387)
          ·
            refine ⟨69061762181361571930673081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46041174787574381287115387 69061762181361571930673081)
            ·
              refine ⟨51796321636021178948004811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69061762181361571930673081 51796321636021178948004811)
              ·
                refine ⟨77694482454031768422007217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51796321636021178948004811 77694482454031768422007217)
                ·
                  refine ⟨58270861840523826316505413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77694482454031768422007217 58270861840523826316505413)
                  ·
                    refine ⟨10925786595098217434344765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58270861840523826316505413 10925786595098217434344765)
                    ·
                      refine ⟨4097169973161831537879287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925786595098217434344765 4097169973161831537879287)
                      ·
                        rfl

theorem cell23_7979210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_7979210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979210 prefixEnd_7979210 := by exact prefixLift 7979210
  have htrace : WordTrace (prefixWord ++ tailWord_7979210) baseStart_7979210 baseEnd_7979210 := by
    simpa [prefixWord, tailWord_7979210, baseEnd_7979210] using wordTrace_append hprefix tailTrace_7979210
  have hstable : (prefixWord ++ tailWord_7979210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979210).length < 2 ^ (prefixWord ++ tailWord_7979210).sum := by decide
  have hdescent : baseEnd_7979210 < baseStart_7979210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979294 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7979294 : Nat := 118140960795 + 7979294 * 2 ^ 59
def prefixEnd_7979294 : Nat := 4983230072969 + 3 ^ 40 * 7979294 * 2
def baseEnd_7979294 : Nat := 1365737701845603069742967

theorem tailTrace_7979294 : CollatzResearch.WordTrace tailWord_7979294 prefixEnd_7979294 1365737701845603069742967 := by
  unfold tailWord_7979294
  simp only [CollatzResearch.WordTrace]
  refine ⟨36378595144298508470731117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194019174102925378510565957 36378595144298508470731117)
  ·
    refine ⟨13641973179111940676524169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36378595144298508470731117 13641973179111940676524169)
    ·
      refine ⟨10231479884333955507393127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13641973179111940676524169 10231479884333955507393127)
      ·
        refine ⟨15347219826500933261089691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231479884333955507393127 15347219826500933261089691)
        ·
          refine ⟨23020829739751399891634537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347219826500933261089691 23020829739751399891634537)
          ·
            refine ⟨17265622304813549918725903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23020829739751399891634537 17265622304813549918725903)
            ·
              refine ⟨25898433457220324878088855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17265622304813549918725903 25898433457220324878088855)
              ·
                refine ⟨38847650185830487317133283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25898433457220324878088855 38847650185830487317133283)
                ·
                  refine ⟨58271475278745730975699925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38847650185830487317133283 58271475278745730975699925)
                  ·
                    refine ⟨1365737701845603069742967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58271475278745730975699925 1365737701845603069742967)
                    ·
                      rfl

theorem cell23_7979294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7979294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979294 prefixEnd_7979294 := by exact prefixLift 7979294
  have htrace : WordTrace (prefixWord ++ tailWord_7979294) baseStart_7979294 baseEnd_7979294 := by
    simpa [prefixWord, tailWord_7979294, baseEnd_7979294] using wordTrace_append hprefix tailTrace_7979294
  have hstable : (prefixWord ++ tailWord_7979294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979294).length < 2 ^ (prefixWord ++ tailWord_7979294).sum := by decide
  have hdescent : baseEnd_7979294 < baseStart_7979294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979297 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7979297 : Nat := 118140960795 + 7979297 * 2 ^ 59
def prefixEnd_7979297 : Nat := 4983230072969 + 3 ^ 40 * 7979297 * 2
def baseEnd_7979297 : Nat := 4097214645978772697491387

theorem tailTrace_7979297 : CollatzResearch.WordTrace tailWord_7979297 prefixEnd_7979297 4097214645978772697491387 := by
  unfold tailWord_7979297
  simp only [CollatzResearch.WordTrace]
  refine ⟨291028870573377199278208145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194019247048918132852138763 291028870573377199278208145)
  ·
    refine ⟨218271652930032899458656109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291028870573377199278208145 218271652930032899458656109)
    ·
      refine ⟨81851869848762337296996041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218271652930032899458656109 81851869848762337296996041)
      ·
        refine ⟨61388902386571752972747031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81851869848762337296996041 61388902386571752972747031)
        ·
          refine ⟨92083353579857629459120547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61388902386571752972747031 92083353579857629459120547)
          ·
            refine ⟨138125030369786444188680821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92083353579857629459120547 138125030369786444188680821)
            ·
              refine ⟨12949221597167479142688827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138125030369786444188680821 12949221597167479142688827)
              ·
                refine ⟨19423832395751218714033241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949221597167479142688827 19423832395751218714033241)
                ·
                  refine ⟨14567874296813414035524931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19423832395751218714033241 14567874296813414035524931)
                  ·
                    refine ⟨21851811445220121053287397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14567874296813414035524931 21851811445220121053287397)
                    ·
                      refine ⟨4097214645978772697491387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21851811445220121053287397 4097214645978772697491387)
                      ·
                        rfl

theorem cell23_7979297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7979297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979297 prefixEnd_7979297 := by exact prefixLift 7979297
  have htrace : WordTrace (prefixWord ++ tailWord_7979297) baseStart_7979297 baseEnd_7979297 := by
    simpa [prefixWord, tailWord_7979297, baseEnd_7979297] using wordTrace_append hprefix tailTrace_7979297
  have hstable : (prefixWord ++ tailWord_7979297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979297).length < 2 ^ (prefixWord ++ tailWord_7979297).sum := by decide
  have hdescent : baseEnd_7979297 < baseStart_7979297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979317 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_7979317 : Nat := 118140960795 + 7979317 * 2 ^ 59
def prefixEnd_7979317 : Nat := 4983230072969 + 3 ^ 40 * 7979317 * 2
def baseEnd_7979317 : Nat := 4097224915591862619241295

theorem tailTrace_7979317 : CollatzResearch.WordTrace tailWord_7979317 prefixEnd_7979317 4097224915591862619241295 := by
  unfold tailWord_7979317
  simp only [CollatzResearch.WordTrace]
  refine ⟨291029600033304742693936205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194019733355536495129290803 291029600033304742693936205)
  ·
    refine ⟨109136100012489278510226077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291029600033304742693936205 109136100012489278510226077)
    ·
      refine ⟨40926037504683479441334779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109136100012489278510226077 40926037504683479441334779)
      ·
        refine ⟨61389056257025219162002169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40926037504683479441334779 61389056257025219162002169)
        ·
          refine ⟨46041792192768914371501627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61389056257025219162002169 46041792192768914371501627)
          ·
            refine ⟨69062688289153371557252441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46041792192768914371501627 69062688289153371557252441)
            ·
              refine ⟨51797016216865028667939331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69062688289153371557252441 51797016216865028667939331)
              ·
                refine ⟨77695524325297543001908997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51797016216865028667939331 77695524325297543001908997)
                ·
                  refine ⟨14567910810993289312857937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77695524325297543001908997 14567910810993289312857937)
                  ·
                    refine ⟨10925933108244966984643453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14567910810993289312857937 10925933108244966984643453)
                    ·
                      refine ⟨4097224915591862619241295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925933108244966984643453 4097224915591862619241295)
                      ·
                        rfl

theorem cell23_7979317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_7979317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979317 prefixEnd_7979317 := by exact prefixLift 7979317
  have htrace : WordTrace (prefixWord ++ tailWord_7979317) baseStart_7979317 baseEnd_7979317 := by
    simpa [prefixWord, tailWord_7979317, baseEnd_7979317] using wordTrace_append hprefix tailTrace_7979317
  have hstable : (prefixWord ++ tailWord_7979317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979317).length < 2 ^ (prefixWord ++ tailWord_7979317).sum := by decide
  have hdescent : baseEnd_7979317 < baseStart_7979317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979324 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_7979324 : Nat := 118140960795 + 7979324 * 2 ^ 59
def prefixEnd_7979324 : Nat := 4983230072969 + 3 ^ 40 * 7979324 * 2
def baseEnd_7979324 : Nat := 1365742836652148030617921

theorem tailTrace_7979324 : CollatzResearch.WordTrace tailWord_7979324 prefixEnd_7979324 1365742836652148030617921 := by
  unfold tailWord_7979324
  simp only [CollatzResearch.WordTrace]
  refine ⟨145514927672139691444720513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194019903562852921926294017 145514927672139691444720513)
  ·
    refine ⟨109136195754104768583540385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145514927672139691444720513 109136195754104768583540385)
    ·
      refine ⟨81852146815578576437655289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109136195754104768583540385 81852146815578576437655289)
      ·
        refine ⟨61389110111683932328241467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81852146815578576437655289 61389110111683932328241467)
        ·
          refine ⟨92083665167525898492362201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61389110111683932328241467 92083665167525898492362201)
          ·
            refine ⟨69062748875644423869271651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92083665167525898492362201 69062748875644423869271651)
            ·
              refine ⟨103594123313466635803907477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69062748875644423869271651 103594123313466635803907477)
              ·
                refine ⟨4855974530318748553308163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103594123313466635803907477 4855974530318748553308163)
                ·
                  refine ⟨7283961795478122829962245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855974530318748553308163 7283961795478122829962245)
                  ·
                    refine ⟨1365742836652148030617921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283961795478122829962245 1365742836652148030617921)
                    ·
                      rfl

theorem cell23_7979324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_7979324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979324 prefixEnd_7979324 := by exact prefixLift 7979324
  have htrace : WordTrace (prefixWord ++ tailWord_7979324) baseStart_7979324 baseEnd_7979324 := by
    simpa [prefixWord, tailWord_7979324, baseEnd_7979324] using wordTrace_append hprefix tailTrace_7979324
  have hstable : (prefixWord ++ tailWord_7979324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979324).length < 2 ^ (prefixWord ++ tailWord_7979324).sum := by decide
  have hdescent : baseEnd_7979324 < baseStart_7979324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979340 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7979340 : Nat := 118140960795 + 7979340 * 2 ^ 59
def prefixEnd_7979340 : Nat := 4983230072969 + 3 ^ 40 * 7979340 * 2
def baseEnd_7979340 : Nat := 4097236725646916029253689

theorem tailTrace_7979340 : CollatzResearch.WordTrace tailWord_7979340 prefixEnd_7979340 4097236725646916029253689 := by
  unfold tailWord_7979340
  simp only [CollatzResearch.WordTrace]
  refine ⟨145515219456110708811011737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194020292608147611748015649 145515219456110708811011737)
  ·
    refine ⟨109136414592083031608258803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145515219456110708811011737 109136414592083031608258803)
    ·
      refine ⟨163704621888124547412388205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109136414592083031608258803 163704621888124547412388205)
      ·
        refine ⟨61389233208046705279645577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163704621888124547412388205 61389233208046705279645577)
        ·
          refine ⟨46041924906035028959734183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61389233208046705279645577 46041924906035028959734183)
          ·
            refine ⟨69062887359052543439601275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46041924906035028959734183 69062887359052543439601275)
            ·
              refine ⟨103594331038578815159401913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69062887359052543439601275 103594331038578815159401913)
              ·
                refine ⟨77695748278934111369551435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103594331038578815159401913 77695748278934111369551435)
                ·
                  refine ⟨116543622418401167054327153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77695748278934111369551435 116543622418401167054327153)
                  ·
                    refine ⟨87407716813800875290745365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116543622418401167054327153 87407716813800875290745365)
                    ·
                      refine ⟨4097236725646916029253689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87407716813800875290745365 4097236725646916029253689)
                      ·
                        rfl

theorem cell23_7979340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7979340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979340 prefixEnd_7979340 := by exact prefixLift 7979340
  have htrace : WordTrace (prefixWord ++ tailWord_7979340) baseStart_7979340 baseEnd_7979340 := by
    simpa [prefixWord, tailWord_7979340, baseEnd_7979340] using wordTrace_append hprefix tailTrace_7979340
  have hstable : (prefixWord ++ tailWord_7979340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979340).length < 2 ^ (prefixWord ++ tailWord_7979340).sum := by decide
  have hdescent : baseEnd_7979340 < baseStart_7979340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979347 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 3]
def baseStart_7979347 : Nat := 118140960795 + 7979347 * 2 ^ 59
def prefixEnd_7979347 : Nat := 4983230072969 + 3 ^ 40 * 7979347 * 2
def baseEnd_7979347 : Nat := 4097240320011497501866157

theorem tailTrace_7979347 : CollatzResearch.WordTrace tailWord_7979347 prefixEnd_7979347 4097240320011497501866157 := by
  unfold tailWord_7979347
  simp only [CollatzResearch.WordTrace]
  refine ⟨291030694223196057817528295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194020462815464038545018863 291030694223196057817528295)
  ·
    refine ⟨436546041334794086726292443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291030694223196057817528295 436546041334794086726292443)
    ·
      refine ⟨654819062002191130089438665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436546041334794086726292443 654819062002191130089438665)
      ·
        refine ⟨491114296501643347567078999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654819062002191130089438665 491114296501643347567078999)
        ·
          refine ⟨736671444752465021350618499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491114296501643347567078999 736671444752465021350618499)
          ·
            refine ⟨1105007167128697532025927749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736671444752465021350618499 1105007167128697532025927749)
            ·
              refine ⟨207188843836630787254861453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1105007167128697532025927749 207188843836630787254861453)
              ·
                refine ⟨77695816438736545220573045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207188843836630787254861453 77695816438736545220573045)
                ·
                  refine ⟨7283982791131551114428723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77695816438736545220573045 7283982791131551114428723)
                  ·
                    refine ⟨10925974186697326671643085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7283982791131551114428723 10925974186697326671643085)
                    ·
                      refine ⟨4097240320011497501866157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10925974186697326671643085 4097240320011497501866157)
                      ·
                        rfl

theorem cell23_7979347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_7979347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979347 prefixEnd_7979347 := by exact prefixLift 7979347
  have htrace : WordTrace (prefixWord ++ tailWord_7979347) baseStart_7979347 baseEnd_7979347 := by
    simpa [prefixWord, tailWord_7979347, baseEnd_7979347] using wordTrace_append hprefix tailTrace_7979347
  have hstable : (prefixWord ++ tailWord_7979347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979347).length < 2 ^ (prefixWord ++ tailWord_7979347).sum := by decide
  have hdescent : baseEnd_7979347 < baseStart_7979347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979381 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7979381 : Nat := 118140960795 + 7979381 * 2 ^ 59
def prefixEnd_7979381 : Nat := 4983230072969 + 3 ^ 40 * 7979381 * 2
def baseEnd_7979381 : Nat := 4097257778353750368841001

theorem tailTrace_7979381 : CollatzResearch.WordTrace tailWord_7979381 prefixEnd_7979381 4097257778353750368841001 := by
  unfold tailWord_7979381
  simp only [CollatzResearch.WordTrace]
  refine ⟨291031934305072881624265997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194021289536715254416177331 291031934305072881624265997)
  ·
    refine ⟨109136975364402330609099749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291031934305072881624265997 109136975364402330609099749)
    ·
      refine ⟨20463182880825436989206203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109136975364402330609099749 20463182880825436989206203)
      ·
        refine ⟨30694774321238155483809305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463182880825436989206203 30694774321238155483809305)
        ·
          refine ⟨23021080740928616612856979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30694774321238155483809305 23021080740928616612856979)
          ·
            refine ⟨34531621111392924919285469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23021080740928616612856979 34531621111392924919285469)
            ·
              refine ⟨12949357916772346844732051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34531621111392924919285469 12949357916772346844732051)
              ·
                refine ⟨19424036875158520267098077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949357916772346844732051 19424036875158520267098077)
                ·
                  refine ⟨7284013828184445100161779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19424036875158520267098077 7284013828184445100161779)
                  ·
                    refine ⟨10926020742276667650242669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7284013828184445100161779 10926020742276667650242669)
                    ·
                      refine ⟨4097257778353750368841001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926020742276667650242669 4097257778353750368841001)
                      ·
                        rfl

theorem cell23_7979381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7979381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979381 prefixEnd_7979381 := by exact prefixLift 7979381
  have htrace : WordTrace (prefixWord ++ tailWord_7979381) baseStart_7979381 baseEnd_7979381 := by
    simpa [prefixWord, tailWord_7979381, baseEnd_7979381] using wordTrace_append hprefix tailTrace_7979381
  have hstable : (prefixWord ++ tailWord_7979381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979381).length < 2 ^ (prefixWord ++ tailWord_7979381).sum := by decide
  have hdescent : baseEnd_7979381 < baseStart_7979381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979404 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_7979404 : Nat := 118140960795 + 7979404 * 2 ^ 59
def prefixEnd_7979404 : Nat := 4983230072969 + 3 ^ 40 * 7979404 * 2
def baseEnd_7979404 : Nat := 4097269588408803778853395

theorem tailTrace_7979404 : CollatzResearch.WordTrace tailWord_7979404 prefixEnd_7979404 4097269588408803778853395 := by
  unfold tailWord_7979404
  simp only [CollatzResearch.WordTrace]
  refine ⟨145516386591994778276176633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194021848789326371034902177 145516386591994778276176633)
  ·
    refine ⟨109137289943996083707132475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145516386591994778276176633 109137289943996083707132475)
    ·
      refine ⟨163705934915994125560698713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109137289943996083707132475 163705934915994125560698713)
      ·
        refine ⟨122779451186995594170524035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163705934915994125560698713 122779451186995594170524035)
        ·
          refine ⟨184169176780493391255786053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122779451186995594170524035 184169176780493391255786053)
          ·
            refine ⟨34531720646342510860459885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184169176780493391255786053 34531720646342510860459885)
            ·
              refine ⟨12949395242378441572672457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34531720646342510860459885 12949395242378441572672457)
              ·
                refine ⟨9712046431783831179504343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12949395242378441572672457 9712046431783831179504343)
                ·
                  refine ⟨14568069647675746769256515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712046431783831179504343 14568069647675746769256515)
                  ·
                    refine ⟨21852104471513620153884773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14568069647675746769256515 21852104471513620153884773)
                    ·
                      refine ⟨4097269588408803778853395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21852104471513620153884773 4097269588408803778853395)
                      ·
                        rfl

theorem cell23_7979404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_7979404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979404 prefixEnd_7979404 := by exact prefixLift 7979404
  have htrace : WordTrace (prefixWord ++ tailWord_7979404) baseStart_7979404 baseEnd_7979404 := by
    simpa [prefixWord, tailWord_7979404, baseEnd_7979404] using wordTrace_append hprefix tailTrace_7979404
  have hstable : (prefixWord ++ tailWord_7979404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979404).length < 2 ^ (prefixWord ++ tailWord_7979404).sum := by decide
  have hdescent : baseEnd_7979404 < baseStart_7979404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979417 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_7979417 : Nat := 118140960795 + 7979417 * 2 ^ 59
def prefixEnd_7979417 : Nat := 4983230072969 + 3 ^ 40 * 7979417 * 2
def baseEnd_7979417 : Nat := 4097276263657312227990835

theorem tailTrace_7979417 : CollatzResearch.WordTrace tailWord_7979417 prefixEnd_7979417 4097276263657312227990835 := by
  unfold tailWord_7979417
  simp only [CollatzResearch.WordTrace]
  refine ⟨291033247332942459772576505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194022164888628306515051003 291033247332942459772576505)
  ·
    refine ⟨218274935499706844829432379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291033247332942459772576505 218274935499706844829432379)
    ·
      refine ⟨327412403249560267244148569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218274935499706844829432379 327412403249560267244148569)
      ·
        refine ⟨245559302437170200433111427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327412403249560267244148569 245559302437170200433111427)
        ·
          refine ⟨368338953655755300649667141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245559302437170200433111427 368338953655755300649667141)
          ·
            refine ⟨69063553810454118871812589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368338953655755300649667141 69063553810454118871812589)
            ·
              refine ⟨25898832678920294576929721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69063553810454118871812589 25898832678920294576929721)
              ·
                refine ⟨19424124509190220932697291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25898832678920294576929721 19424124509190220932697291)
                ·
                  refine ⟨29136186763785331399045937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19424124509190220932697291 29136186763785331399045937)
                  ·
                    refine ⟨21852140072838998549284453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29136186763785331399045937 21852140072838998549284453)
                    ·
                      refine ⟨4097276263657312227990835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21852140072838998549284453 4097276263657312227990835)
                      ·
                        rfl

theorem cell23_7979417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_7979417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979417 prefixEnd_7979417 := by exact prefixLift 7979417
  have htrace : WordTrace (prefixWord ++ tailWord_7979417) baseStart_7979417 baseEnd_7979417 := by
    simpa [prefixWord, tailWord_7979417, baseEnd_7979417] using wordTrace_append hprefix tailTrace_7979417
  have hstable : (prefixWord ++ tailWord_7979417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979417).length < 2 ^ (prefixWord ++ tailWord_7979417).sum := by decide
  have hdescent : baseEnd_7979417 < baseStart_7979417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979424 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_7979424 : Nat := 118140960795 + 7979424 * 2 ^ 59
def prefixEnd_7979424 : Nat := 4983230072969 + 3 ^ 40 * 7979424 * 2
def baseEnd_7979424 : Nat := 4097279858021893700603303

theorem tailTrace_7979424 : CollatzResearch.WordTrace tailWord_7979424 prefixEnd_7979424 4097279858021893700603303 := by
  unfold tailWord_7979424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145516751321958549984040663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194022335095944733312054217 145516751321958549984040663)
  ·
    refine ⟨218275126982937824976060995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145516751321958549984040663 218275126982937824976060995)
    ·
      refine ⟨327412690474406737464091493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218275126982937824976060995 327412690474406737464091493)
      ·
        refine ⟨61389879463951263274517155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327412690474406737464091493 61389879463951263274517155)
        ·
          refine ⟨92084819195926894911775733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61389879463951263274517155 92084819195926894911775733)
          ·
            refine ⟨8632951799618146397978975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92084819195926894911775733 8632951799618146397978975)
            ·
              refine ⟨12949427699427219596968463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632951799618146397978975 12949427699427219596968463)
              ·
                refine ⟨19424141549140829395452695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949427699427219596968463 19424141549140829395452695)
                ·
                  refine ⟨29136212323711244093179043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19424141549140829395452695 29136212323711244093179043)
                  ·
                    refine ⟨43704318485566866139768565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29136212323711244093179043 43704318485566866139768565)
                    ·
                      refine ⟨4097279858021893700603303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43704318485566866139768565 4097279858021893700603303)
                      ·
                        rfl

theorem cell23_7979424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_7979424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979424 prefixEnd_7979424 := by exact prefixLift 7979424
  have htrace : WordTrace (prefixWord ++ tailWord_7979424) baseStart_7979424 baseEnd_7979424 := by
    simpa [prefixWord, tailWord_7979424, baseEnd_7979424] using wordTrace_append hprefix tailTrace_7979424
  have hstable : (prefixWord ++ tailWord_7979424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979424).length < 2 ^ (prefixWord ++ tailWord_7979424).sum := by decide
  have hdescent : baseEnd_7979424 < baseStart_7979424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979431 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7979431 : Nat := 118140960795 + 7979431 * 2 ^ 59
def prefixEnd_7979431 : Nat := 4983230072969 + 3 ^ 40 * 7979431 * 2
def baseEnd_7979431 : Nat := 1365761150795491724405257

theorem tailTrace_7979431 : CollatzResearch.WordTrace tailWord_7979431 prefixEnd_7979431 1365761150795491724405257 := by
  unfold tailWord_7979431
  simp only [CollatzResearch.WordTrace]
  refine ⟨291033757954891740163586147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194022505303261160109057431 291033757954891740163586147)
  ·
    refine ⟨436550636932337610245379221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291033757954891740163586147 436550636932337610245379221)
    ·
      refine ⟨20463311106203325480252151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 436550636932337610245379221 20463311106203325480252151)
      ·
        refine ⟨30694966659304988220378227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463311106203325480252151 30694966659304988220378227)
        ·
          refine ⟨46042449988957482330567341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30694966659304988220378227 46042449988957482330567341)
          ·
            refine ⟨17265918745859055873962753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46042449988957482330567341 17265918745859055873962753)
            ·
              refine ⟨12949439059394291905472065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17265918745859055873962753 12949439059394291905472065)
              ·
                refine ⟨9712079294545718929104049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12949439059394291905472065 9712079294545718929104049)
                ·
                  refine ⟨7284059470909289196828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712079294545718929104049 7284059470909289196828037)
                  ·
                    refine ⟨1365761150795491724405257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284059470909289196828037 1365761150795491724405257)
                    ·
                      rfl

theorem cell23_7979431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7979431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979431 prefixEnd_7979431 := by exact prefixLift 7979431
  have htrace : WordTrace (prefixWord ++ tailWord_7979431) baseStart_7979431 baseEnd_7979431 := by
    simpa [prefixWord, tailWord_7979431, baseEnd_7979431] using wordTrace_append hprefix tailTrace_7979431
  have hstable : (prefixWord ++ tailWord_7979431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979431).length < 2 ^ (prefixWord ++ tailWord_7979431).sum := by decide
  have hdescent : baseEnd_7979431 < baseStart_7979431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979432 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7979432 : Nat := 118140960795 + 7979432 * 2 ^ 59
def prefixEnd_7979432 : Nat := 4983230072969 + 3 ^ 40 * 7979432 * 2
def baseEnd_7979432 : Nat := 4097283965867129669303267

theorem tailTrace_7979432 : CollatzResearch.WordTrace tailWord_7979432 prefixEnd_7979432 4097283965867129669303267 := by
  unfold tailWord_7979432
  simp only [CollatzResearch.WordTrace]
  refine ⟨145516897213944058667186275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194022529618592078222915033 145516897213944058667186275)
  ·
    refine ⟨218275345820916088000779413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145516897213944058667186275 218275345820916088000779413)
    ·
      refine ⟨10231656835355441625036535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218275345820916088000779413 10231656835355441625036535)
      ·
        refine ⟨15347485253033162437554803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231656835355441625036535 15347485253033162437554803)
        ·
          refine ⟨23021227879549743656332205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347485253033162437554803 23021227879549743656332205)
          ·
            refine ⟨8632960454831153871124577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23021227879549743656332205 8632960454831153871124577)
            ·
              refine ⟨6474720341123365403343433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8632960454831153871124577 6474720341123365403343433)
              ·
                refine ⟨4856040255842524052507575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474720341123365403343433 4856040255842524052507575)
                ·
                  refine ⟨7284060383763786078761363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856040255842524052507575 7284060383763786078761363)
                  ·
                    refine ⟨10926090575645679118142045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7284060383763786078761363 10926090575645679118142045)
                    ·
                      refine ⟨4097283965867129669303267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926090575645679118142045 4097283965867129669303267)
                      ·
                        rfl

theorem cell23_7979432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7979432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979432 prefixEnd_7979432 := by exact prefixLift 7979432
  have htrace : WordTrace (prefixWord ++ tailWord_7979432) baseStart_7979432 baseEnd_7979432 := by
    simpa [prefixWord, tailWord_7979432, baseEnd_7979432] using wordTrace_append hprefix tailTrace_7979432
  have hstable : (prefixWord ++ tailWord_7979432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979432).length < 2 ^ (prefixWord ++ tailWord_7979432).sum := by decide
  have hdescent : baseEnd_7979432 < baseStart_7979432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979454 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_7979454 : Nat := 118140960795 + 7979454 * 2 ^ 59
def prefixEnd_7979454 : Nat := 4983230072969 + 3 ^ 40 * 7979454 * 2
def baseEnd_7979454 : Nat := 4097295262441528583228165

theorem tailTrace_7979454 : CollatzResearch.WordTrace tailWord_7979454 prefixEnd_7979454 4097295262441528583228165 := by
  unfold tailWord_7979454
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379324604226051886459177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194023064555872276727782277 36379324604226051886459177)
  ·
    refine ⟨27284493453169538914844383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36379324604226051886459177 27284493453169538914844383)
    ·
      refine ⟨40926740179754308372266575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27284493453169538914844383 40926740179754308372266575)
      ·
        refine ⟨61390110269631462558399863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40926740179754308372266575 61390110269631462558399863)
        ·
          refine ⟨92085165404447193837599795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61390110269631462558399863 92085165404447193837599795)
          ·
            refine ⟨138127748106670790756399693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92085165404447193837599795 138127748106670790756399693)
            ·
              refine ⟨51797905540001546533649885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138127748106670790756399693 51797905540001546533649885)
              ·
                refine ⟨19424214577500579950118707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51797905540001546533649885 19424214577500579950118707)
                ·
                  refine ⟨29136321866250869925178061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19424214577500579950118707 29136321866250869925178061)
                  ·
                    refine ⟨10926120699844076221941773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29136321866250869925178061 10926120699844076221941773)
                    ·
                      refine ⟨4097295262441528583228165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926120699844076221941773 4097295262441528583228165)
                      ·
                        rfl

theorem cell23_7979454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_7979454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979454 prefixEnd_7979454 := by exact prefixLift 7979454
  have htrace : WordTrace (prefixWord ++ tailWord_7979454) baseStart_7979454 baseEnd_7979454 := by
    simpa [prefixWord, tailWord_7979454, baseEnd_7979454] using wordTrace_append hprefix tailTrace_7979454
  have hstable : (prefixWord ++ tailWord_7979454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979454).length < 2 ^ (prefixWord ++ tailWord_7979454).sum := by decide
  have hdescent : baseEnd_7979454 < baseStart_7979454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979481 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 1, 3, 2]
def baseStart_7979481 : Nat := 118140960795 + 7979481 * 2 ^ 59
def prefixEnd_7979481 : Nat := 4983230072969 + 3 ^ 40 * 7979481 * 2
def baseEnd_7979481 : Nat := 4097309126419199977590541

theorem tailTrace_7979481 : CollatzResearch.WordTrace tailWord_7979481 prefixEnd_7979481 4097309126419199977590541 := by
  unfold tailWord_7979481
  simp only [CollatzResearch.WordTrace]
  refine ⟨291035581604710598702906297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194023721069807065801937531 291035581604710598702906297)
  ·
    refine ⟨218276686203532949027179723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291035581604710598702906297 218276686203532949027179723)
    ·
      refine ⟨327415029305299423540769585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218276686203532949027179723 327415029305299423540769585)
      ·
        refine ⟨245561271978974567655577189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327415029305299423540769585 245561271978974567655577189)
        ·
          refine ⟨46042738496057731435420723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245561271978974567655577189 46042738496057731435420723)
          ·
            refine ⟨69064107744086597153131085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46042738496057731435420723 69064107744086597153131085)
            ·
              refine ⟨25899040404032473932424157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69064107744086597153131085 25899040404032473932424157)
              ·
                refine ⟨9712140151512177724659059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25899040404032473932424157 9712140151512177724659059)
                ·
                  refine ⟨14568210227268266586988589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712140151512177724659059 14568210227268266586988589)
                  ·
                    refine ⟨5463078835225599970120721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14568210227268266586988589 5463078835225599970120721)
                    ·
                      refine ⟨4097309126419199977590541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463078835225599970120721 4097309126419199977590541)
                      ·
                        rfl

theorem cell23_7979481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_7979481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979481 prefixEnd_7979481 := by exact prefixLift 7979481
  have htrace : WordTrace (prefixWord ++ tailWord_7979481) baseStart_7979481 baseEnd_7979481 := by
    simpa [prefixWord, tailWord_7979481, baseEnd_7979481] using wordTrace_append hprefix tailTrace_7979481
  have hstable : (prefixWord ++ tailWord_7979481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979481).length < 2 ^ (prefixWord ++ tailWord_7979481).sum := by decide
  have hdescent : baseEnd_7979481 < baseStart_7979481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979487 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 2, 6]
def baseStart_7979487 : Nat := 118140960795 + 7979487 * 2 ^ 59
def prefixEnd_7979487 : Nat := 4983230072969 + 3 ^ 40 * 7979487 * 2
def baseEnd_7979487 : Nat := 1365770735767708984705171

theorem tailTrace_7979487 : CollatzResearch.WordTrace tailWord_7979487 prefixEnd_7979487 1365770735767708984705171 := by
  unfold tailWord_7979487
  simp only [CollatzResearch.WordTrace]
  refine ⟨291035800442688861727624715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194023866961792574485083143 291035800442688861727624715)
  ·
    refine ⟨436553700664033292591437073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291035800442688861727624715 436553700664033292591437073)
    ·
      refine ⟨327415275498024969443577805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436553700664033292591437073 327415275498024969443577805)
      ·
        refine ⟨122780728311759363541341677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327415275498024969443577805 122780728311759363541341677)
        ·
          refine ⟨46042773116909761328003129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122780728311759363541341677 46042773116909761328003129)
          ·
            refine ⟨34532079837682320996002347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46042773116909761328003129 34532079837682320996002347)
            ·
              refine ⟨51798119756523481494003521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34532079837682320996002347 51798119756523481494003521)
              ·
                refine ⟨38848589817392611120502641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51798119756523481494003521 38848589817392611120502641)
                ·
                  refine ⟨29136442363044458340376981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38848589817392611120502641 29136442363044458340376981)
                  ·
                    refine ⟨1365770735767708984705171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29136442363044458340376981 1365770735767708984705171)
                    ·
                      rfl

theorem cell23_7979487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_7979487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979487 prefixEnd_7979487 := by exact prefixLift 7979487
  have htrace : WordTrace (prefixWord ++ tailWord_7979487) baseStart_7979487 baseEnd_7979487 := by
    simpa [prefixWord, tailWord_7979487, baseEnd_7979487] using wordTrace_append hprefix tailTrace_7979487
  have hstable : (prefixWord ++ tailWord_7979487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979487).length < 2 ^ (prefixWord ++ tailWord_7979487).sum := by decide
  have hdescent : baseEnd_7979487 < baseStart_7979487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979497 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_7979497 : Nat := 118140960795 + 7979497 * 2 ^ 59
def prefixEnd_7979497 : Nat := 4983230072969 + 3 ^ 40 * 7979497 * 2
def baseEnd_7979497 : Nat := 4097317342109671914990467

theorem tailTrace_7979497 : CollatzResearch.WordTrace tailWord_7979497 prefixEnd_7979497 4097317342109671914990467 := by
  unfold tailWord_7979497
  simp only [CollatzResearch.WordTrace]
  refine ⟨291036165172652633435488745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194024110115101755623659163 291036165172652633435488745)
  ·
    refine ⟨218277123879489475076616559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291036165172652633435488745 218277123879489475076616559)
    ·
      refine ⟨327415685819234212614924839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218277123879489475076616559 327415685819234212614924839)
      ·
        refine ⟨491123528728851318922387259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327415685819234212614924839 491123528728851318922387259)
        ·
          refine ⟨736685293093276978383580889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491123528728851318922387259 736685293093276978383580889)
          ·
            refine ⟨552513969819957733787685667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736685293093276978383580889 552513969819957733787685667)
            ·
              refine ⟨828770954729936600681528501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552513969819957733787685667 828770954729936600681528501)
              ·
                refine ⟨77697277005931556313893297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 828770954729936600681528501 77697277005931556313893297)
                ·
                  refine ⟨58272957754448667235419973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77697277005931556313893297 58272957754448667235419973)
                  ·
                    refine ⟨10926179578959125106641245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58272957754448667235419973 10926179578959125106641245)
                    ·
                      refine ⟨4097317342109671914990467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926179578959125106641245 4097317342109671914990467)
                      ·
                        rfl

theorem cell23_7979497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_7979497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979497 prefixEnd_7979497 := by exact prefixLift 7979497
  have htrace : WordTrace (prefixWord ++ tailWord_7979497) baseStart_7979497 baseEnd_7979497 := by
    simpa [prefixWord, tailWord_7979497, baseEnd_7979497] using wordTrace_append hprefix tailTrace_7979497
  have hstable : (prefixWord ++ tailWord_7979497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979497).length < 2 ^ (prefixWord ++ tailWord_7979497).sum := by decide
  have hdescent : baseEnd_7979497 < baseStart_7979497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979507 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_7979507 : Nat := 118140960795 + 7979507 * 2 ^ 59
def prefixEnd_7979507 : Nat := 4983230072969 + 3 ^ 40 * 7979507 * 2
def baseEnd_7979507 : Nat := 4097322476916216875865421

theorem tailTrace_7979507 : CollatzResearch.WordTrace tailWord_7979507 prefixEnd_7979507 4097322476916216875865421 := by
  unfold tailWord_7979507
  simp only [CollatzResearch.WordTrace]
  refine ⟨291036529902616405143352775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194024353268410936762235183 291036529902616405143352775)
  ·
    refine ⟨436554794853924607715029163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291036529902616405143352775 436554794853924607715029163)
    ·
      refine ⟨654832192280886911572543745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436554794853924607715029163 654832192280886911572543745)
      ·
        refine ⟨491124144210665183679407809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654832192280886911572543745 491124144210665183679407809)
        ·
          refine ⟨368343108157998887759555857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491124144210665183679407809 368343108157998887759555857)
          ·
            refine ⟨276257331118499165819666893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368343108157998887759555857 276257331118499165819666893)
            ·
              refine ⟨103596499169437187182375085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276257331118499165819666893 103596499169437187182375085)
              ·
                refine ⟨38848687188538945193390657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103596499169437187182375085 38848687188538945193390657)
                ·
                  refine ⟨29136515391404208895042993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38848687188538945193390657 29136515391404208895042993)
                  ·
                    refine ⟨21852386543553156671282245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29136515391404208895042993 21852386543553156671282245)
                    ·
                      refine ⟨4097322476916216875865421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21852386543553156671282245 4097322476916216875865421)
                      ·
                        rfl

theorem cell23_7979507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_7979507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979507 prefixEnd_7979507 := by exact prefixLift 7979507
  have htrace : WordTrace (prefixWord ++ tailWord_7979507) baseStart_7979507 baseEnd_7979507 := by
    simpa [prefixWord, tailWord_7979507, baseEnd_7979507] using wordTrace_append hprefix tailTrace_7979507
  have hstable : (prefixWord ++ tailWord_7979507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979507).length < 2 ^ (prefixWord ++ tailWord_7979507).sum := by decide
  have hdescent : baseEnd_7979507 < baseStart_7979507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979517 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 7]
def baseStart_7979517 : Nat := 118140960795 + 7979517 * 2 ^ 59
def prefixEnd_7979517 : Nat := 4983230072969 + 3 ^ 40 * 7979517 * 2
def baseEnd_7979517 : Nat := 455258623524751315193375

theorem tailTrace_7979517 : CollatzResearch.WordTrace tailWord_7979517 prefixEnd_7979517 455258623524751315193375 := by
  unfold tailWord_7979517
  simp only [CollatzResearch.WordTrace]
  refine ⟨291036894632580176851216805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194024596421720117900811203 291036894632580176851216805)
  ·
    refine ⟨54569417743608783159603151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291036894632580176851216805 54569417743608783159603151)
    ·
      refine ⟨81854126615413174739404727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54569417743608783159603151 81854126615413174739404727)
      ·
        refine ⟨122781189923119762109107091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81854126615413174739404727 122781189923119762109107091)
        ·
          refine ⟨184171784884679643163660637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122781189923119762109107091 184171784884679643163660637)
          ·
            refine ⟨69064419331754866186372739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184171784884679643163660637 69064419331754866186372739)
            ·
              refine ⟨103596628997632299279559109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69064419331754866186372739 103596628997632299279559109)
              ·
                refine ⟨19424367937056056114917333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103596628997632299279559109 19424367937056056114917333)
                ·
                  refine ⟨455258623524751315193375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19424367937056056114917333 455258623524751315193375)
                  ·
                    rfl

theorem cell23_7979517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_7979517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979517 prefixEnd_7979517 := by exact prefixLift 7979517
  have htrace : WordTrace (prefixWord ++ tailWord_7979517) baseStart_7979517 baseEnd_7979517 := by
    simpa [prefixWord, tailWord_7979517, baseEnd_7979517] using wordTrace_append hprefix tailTrace_7979517
  have hstable : (prefixWord ++ tailWord_7979517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979517).length < 2 ^ (prefixWord ++ tailWord_7979517).sum := by decide
  have hdescent : baseEnd_7979517 < baseStart_7979517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979557 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_7979557 : Nat := 118140960795 + 7979557 * 2 ^ 59
def prefixEnd_7979557 : Nat := 4983230072969 + 3 ^ 40 * 7979557 * 2
def baseEnd_7979557 : Nat := 4097348150948941680240191

theorem tailTrace_7979557 : CollatzResearch.WordTrace tailWord_7979557 prefixEnd_7979557 4097348150948941680240191 := by
  unfold tailWord_7979557
  simp only [CollatzResearch.WordTrace]
  refine ⟨291038353552435263682672925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194025569034956842455115283 291038353552435263682672925)
  ·
    refine ⟨109139382582163223881002347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291038353552435263682672925 109139382582163223881002347)
    ·
      refine ⟨163709073873244835821503521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109139382582163223881002347 163709073873244835821503521)
      ·
        refine ⟨122781805404933626866127641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163709073873244835821503521 122781805404933626866127641)
        ·
          refine ⟨92086354053700220149595731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122781805404933626866127641 92086354053700220149595731)
          ·
            refine ⟨138129531080550330224393597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92086354053700220149595731 138129531080550330224393597)
            ·
              refine ⟨51798574155206373834147599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138129531080550330224393597 51798574155206373834147599)
              ·
                refine ⟨77697861232809560751221399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51798574155206373834147599 77697861232809560751221399)
                ·
                  refine ⟨116546791849214341126832099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77697861232809560751221399 116546791849214341126832099)
                  ·
                    refine ⟨174820187773821511690248149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116546791849214341126832099 174820187773821511690248149)
                    ·
                      refine ⟨4097348150948941680240191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174820187773821511690248149 4097348150948941680240191)
                      ·
                        rfl

theorem cell23_7979557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_7979557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979557 prefixEnd_7979557 := by exact prefixLift 7979557
  have htrace : WordTrace (prefixWord ++ tailWord_7979557) baseStart_7979557 baseEnd_7979557 := by
    simpa [prefixWord, tailWord_7979557, baseEnd_7979557] using wordTrace_append hprefix tailTrace_7979557
  have hstable : (prefixWord ++ tailWord_7979557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979557).length < 2 ^ (prefixWord ++ tailWord_7979557).sum := by decide
  have hdescent : baseEnd_7979557 < baseStart_7979557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979562 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7979562 : Nat := 118140960795 + 7979562 * 2 ^ 59
def prefixEnd_7979562 : Nat := 4983230072969 + 3 ^ 40 * 7979562 * 2
def baseEnd_7979562 : Nat := 4097350718352214160677669

theorem tailTrace_7979562 : CollatzResearch.WordTrace tailWord_7979562 prefixEnd_7979562 4097350718352214160677669 := by
  unfold tailWord_7979562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72759633979354287384151235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194025690611611433024403293 72759633979354287384151235)
  ·
    refine ⟨109139450969031431076226853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72759633979354287384151235 109139450969031431076226853)
    ·
      refine ⟨20463647056693393326792535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109139450969031431076226853 20463647056693393326792535)
      ·
        refine ⟨30695470585040089990188803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463647056693393326792535 30695470585040089990188803)
        ·
          refine ⟨46043205877560134985283205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30695470585040089990188803 46043205877560134985283205)
          ·
            refine ⟨8633101102042525309740601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46043205877560134985283205 8633101102042525309740601)
            ·
              refine ⟨6474825826531893982305451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633101102042525309740601 6474825826531893982305451)
              ·
                refine ⟨9712238739797840973458177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6474825826531893982305451 9712238739797840973458177)
                ·
                  refine ⟨7284179054848380730093633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712238739797840973458177 7284179054848380730093633)
                  ·
                    refine ⟨5463134291136285547570225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7284179054848380730093633 5463134291136285547570225)
                    ·
                      refine ⟨4097350718352214160677669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463134291136285547570225 4097350718352214160677669)
                      ·
                        rfl

theorem cell23_7979562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7979562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979562 prefixEnd_7979562 := by exact prefixLift 7979562
  have htrace : WordTrace (prefixWord ++ tailWord_7979562) baseStart_7979562 baseEnd_7979562 := by
    simpa [prefixWord, tailWord_7979562, baseEnd_7979562] using wordTrace_append hprefix tailTrace_7979562
  have hstable : (prefixWord ++ tailWord_7979562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979562).length < 2 ^ (prefixWord ++ tailWord_7979562).sum := by decide
  have hdescent : baseEnd_7979562 < baseStart_7979562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979581 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_7979581 : Nat := 118140960795 + 7979581 * 2 ^ 59
def prefixEnd_7979581 : Nat := 4983230072969 + 3 ^ 40 * 7979581 * 2
def baseEnd_7979581 : Nat := 1365786824828216528780027

theorem tailTrace_7979581 : CollatzResearch.WordTrace tailWord_7979581 prefixEnd_7979581 1365786824828216528780027 := by
  unfold tailWord_7979581
  simp only [CollatzResearch.WordTrace]
  refine ⟨291039228904348315781546597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194026152602898877187697731 291039228904348315781546597)
  ·
    refine ⟨54569855419565309209039987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291039228904348315781546597 54569855419565309209039987)
    ·
      refine ⟨81854783129347963813559981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54569855419565309209039987 81854783129347963813559981)
      ·
        refine ⟨30695543673505486430084993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81854783129347963813559981 30695543673505486430084993)
        ·
          refine ⟨23021657755129114822563745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30695543673505486430084993 23021657755129114822563745)
          ·
            refine ⟨17266243316346836116922809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23021657755129114822563745 17266243316346836116922809)
            ·
              refine ⟨12949682487260127087692107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17266243316346836116922809 12949682487260127087692107)
              ·
                refine ⟨19424523730890190631538161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949682487260127087692107 19424523730890190631538161)
                ·
                  refine ⟨14568392798167642973653621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19424523730890190631538161 14568392798167642973653621)
                  ·
                    refine ⟨1365786824828216528780027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14568392798167642973653621 1365786824828216528780027)
                    ·
                      rfl

theorem cell23_7979581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_7979581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979581 prefixEnd_7979581 := by exact prefixLift 7979581
  have htrace : WordTrace (prefixWord ++ tailWord_7979581) baseStart_7979581 baseEnd_7979581 := by
    simpa [prefixWord, tailWord_7979581, baseEnd_7979581] using wordTrace_append hprefix tailTrace_7979581
  have hstable : (prefixWord ++ tailWord_7979581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979581).length < 2 ^ (prefixWord ++ tailWord_7979581).sum := by decide
  have hdescent : baseEnd_7979581 < baseStart_7979581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979584 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_7979584 : Nat := 118140960795 + 7979584 * 2 ^ 59
def prefixEnd_7979584 : Nat := 4983230072969 + 3 ^ 40 * 7979584 * 2
def baseEnd_7979584 : Nat := 4097362014926613074602567

theorem tailTrace_7979584 : CollatzResearch.WordTrace tailWord_7979584 prefixEnd_7979584 4097362014926613074602567 := by
  unfold tailWord_7979584
  simp only [CollatzResearch.WordTrace]
  refine ⟨145519669161668723646952903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194026225548891631529270537 145519669161668723646952903)
  ·
    refine ⟨218279503742503085470429355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145519669161668723646952903 218279503742503085470429355)
    ·
      refine ⟨327419255613754628205644033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218279503742503085470429355 327419255613754628205644033)
      ·
        refine ⟨245564441710315971154233025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327419255613754628205644033 245564441710315971154233025)
        ·
          refine ⟨184173331282736978365674769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245564441710315971154233025 184173331282736978365674769)
          ·
            refine ⟨138129998462052733774256077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184173331282736978365674769 138129998462052733774256077)
            ·
              refine ⟨51798749423269775165346029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138129998462052733774256077 51798749423269775165346029)
              ·
                refine ⟨19424531033726165687004761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51798749423269775165346029 19424531033726165687004761)
                ·
                  refine ⟨14568398275294624265253571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19424531033726165687004761 14568398275294624265253571)
                  ·
                    refine ⟨21852597412941936397880357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14568398275294624265253571 21852597412941936397880357)
                    ·
                      refine ⟨4097362014926613074602567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21852597412941936397880357 4097362014926613074602567)
                      ·
                        rfl

theorem cell23_7979584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_7979584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979584 prefixEnd_7979584 := by exact prefixLift 7979584
  have htrace : WordTrace (prefixWord ++ tailWord_7979584) baseStart_7979584 baseEnd_7979584 := by
    simpa [prefixWord, tailWord_7979584, baseEnd_7979584] using wordTrace_append hprefix tailTrace_7979584
  have hstable : (prefixWord ++ tailWord_7979584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979584).length < 2 ^ (prefixWord ++ tailWord_7979584).sum := by decide
  have hdescent : baseEnd_7979584 < baseStart_7979584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979627 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_7979627 : Nat := 118140960795 + 7979627 * 2 ^ 59
def prefixEnd_7979627 : Nat := 4983230072969 + 3 ^ 40 * 7979627 * 2
def baseEnd_7979627 : Nat := 4097384094594756406364869

theorem tailTrace_7979627 : CollatzResearch.WordTrace tailWord_7979627 prefixEnd_7979627 4097384094594756406364869 := by
  unfold tailWord_7979627
  simp only [CollatzResearch.WordTrace]
  refine ⟨291040906662181665637721135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194027271108121110425147423 291040906662181665637721135)
  ·
    refine ⟨436561359993272498456581703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291040906662181665637721135 436561359993272498456581703)
    ·
      refine ⟨654842039989908747684872555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436561359993272498456581703 654842039989908747684872555)
      ·
        refine ⟨982263059984863121527308833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654842039989908747684872555 982263059984863121527308833)
        ·
          refine ⟨736697294988647341145481625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982263059984863121527308833 736697294988647341145481625)
          ·
            refine ⟨552522971241485505859111219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736697294988647341145481625 552522971241485505859111219)
            ·
              refine ⟨828784456862228258788666829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552522971241485505859111219 828784456862228258788666829)
              ·
                refine ⟨310794171323335597045750061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828784456862228258788666829 310794171323335597045750061)
                ·
                  refine ⟨116547814246250848892156273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310794171323335597045750061 116547814246250848892156273)
                  ·
                    refine ⟨87410860684688136669117205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116547814246250848892156273 87410860684688136669117205)
                    ·
                      refine ⟨4097384094594756406364869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87410860684688136669117205 4097384094594756406364869)
                      ·
                        rfl

theorem cell23_7979627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_7979627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979627 prefixEnd_7979627 := by exact prefixLift 7979627
  have htrace : WordTrace (prefixWord ++ tailWord_7979627) baseStart_7979627 baseEnd_7979627 := by
    simpa [prefixWord, tailWord_7979627, baseEnd_7979627] using wordTrace_append hprefix tailTrace_7979627
  have hstable : (prefixWord ++ tailWord_7979627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979627).length < 2 ^ (prefixWord ++ tailWord_7979627).sum := by decide
  have hdescent : baseEnd_7979627 < baseStart_7979627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979638 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7979638 : Nat := 118140960795 + 7979638 * 2 ^ 59
def prefixEnd_7979638 : Nat := 4983230072969 + 3 ^ 40 * 7979638 * 2
def baseEnd_7979638 : Nat := 4097389742881955863327319

theorem tailTrace_7979638 : CollatzResearch.WordTrace tailWord_7979638 prefixEnd_7979638 4097389742881955863327319 := by
  unfold tailWord_7979638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190081741571363407273223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194027538576761209677581045 18190081741571363407273223)
  ·
    refine ⟨27285122612357045110909835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190081741571363407273223 27285122612357045110909835)
    ·
      refine ⟨40927683918535567666364753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27285122612357045110909835 40927683918535567666364753)
      ·
        refine ⟨30695762938901675749773565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40927683918535567666364753 30695762938901675749773565)
        ·
          refine ⟨11510911102088128406165087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30695762938901675749773565 11510911102088128406165087)
          ·
            refine ⟨17266366653132192609247631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11510911102088128406165087 17266366653132192609247631)
            ·
              refine ⟨25899549979698288913871447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17266366653132192609247631 25899549979698288913871447)
              ·
                refine ⟨38849324969547433370807171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25899549979698288913871447 38849324969547433370807171)
                ·
                  refine ⟨58273987454321150056210757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38849324969547433370807171 58273987454321150056210757)
                  ·
                    refine ⟨10926372647685215635539517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58273987454321150056210757 10926372647685215635539517)
                    ·
                      refine ⟨4097389742881955863327319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926372647685215635539517 4097389742881955863327319)
                      ·
                        rfl

theorem cell23_7979638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7979638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979638 prefixEnd_7979638 := by exact prefixLift 7979638
  have htrace : WordTrace (prefixWord ++ tailWord_7979638) baseStart_7979638 baseEnd_7979638 := by
    simpa [prefixWord, tailWord_7979638, baseEnd_7979638] using wordTrace_append hprefix tailTrace_7979638
  have hstable : (prefixWord ++ tailWord_7979638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979638).length < 2 ^ (prefixWord ++ tailWord_7979638).sum := by decide
  have hdescent : baseEnd_7979638 < baseStart_7979638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979645 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_7979645 : Nat := 118140960795 + 7979645 * 2 ^ 59
def prefixEnd_7979645 : Nat := 4983230072969 + 3 ^ 40 * 7979645 * 2
def baseEnd_7979645 : Nat := 1365797779082179111979929

theorem tailTrace_7979645 : CollatzResearch.WordTrace tailWord_7979645 prefixEnd_7979645 1365797779082179111979929 := by
  unfold tailWord_7979645
  simp only [CollatzResearch.WordTrace]
  refine ⟨291041563176116454711876389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194027708784077636474584259 291041563176116454711876389)
  ·
    refine ⟨54570293095521835258476823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291041563176116454711876389 54570293095521835258476823)
    ·
      refine ⟨81855439643282752887715235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54570293095521835258476823 81855439643282752887715235)
      ·
        refine ⟨122783159464924129331572853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81855439643282752887715235 122783159464924129331572853)
        ·
          refine ⟨11510921199836637124834955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122783159464924129331572853 11510921199836637124834955)
          ·
            refine ⟨17266381799754955687252433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11510921199836637124834955 17266381799754955687252433)
            ·
              refine ⟨12949786349816216765439325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17266381799754955687252433 12949786349816216765439325)
              ·
                refine ⟨4856169881181081287039747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949786349816216765439325 4856169881181081287039747)
                ·
                  refine ⟨7284254821771621930559621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856169881181081287039747 7284254821771621930559621)
                  ·
                    refine ⟨1365797779082179111979929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284254821771621930559621 1365797779082179111979929)
                    ·
                      rfl

theorem cell23_7979645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_7979645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979645 prefixEnd_7979645 := by exact prefixLift 7979645
  have htrace : WordTrace (prefixWord ++ tailWord_7979645) baseStart_7979645 baseEnd_7979645 := by
    simpa [prefixWord, tailWord_7979645, baseEnd_7979645] using wordTrace_append hprefix tailTrace_7979645
  have hstable : (prefixWord ++ tailWord_7979645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979645).length < 2 ^ (prefixWord ++ tailWord_7979645).sum := by decide
  have hdescent : baseEnd_7979645 < baseStart_7979645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979658 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_7979658 : Nat := 118140960795 + 7979658 * 2 ^ 59
def prefixEnd_7979658 : Nat := 4983230072969 + 3 ^ 40 * 7979658 * 2
def baseEnd_7979658 : Nat := 455266668055005087230803

theorem tailTrace_7979658 : CollatzResearch.WordTrace tailWord_7979658 prefixEnd_7979658 455266668055005087230803 := by
  unfold tailWord_7979658
  simp only [CollatzResearch.WordTrace]
  refine ⟨72760509331267339483024907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194028024883379571954733085 72760509331267339483024907)
  ·
    refine ⟨109140763996901009224537361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72760509331267339483024907 109140763996901009224537361)
    ·
      refine ⟨81855572997675756918403021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109140763996901009224537361 81855572997675756918403021)
      ·
        refine ⟨30695839874128408844401133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81855572997675756918403021 30695839874128408844401133)
        ·
          refine ⟨11510939952798153316650425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30695839874128408844401133 11510939952798153316650425)
          ·
            refine ⟨8633204964598614987487819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11510939952798153316650425 8633204964598614987487819)
            ·
              refine ⟨12949807446897922481231729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633204964598614987487819 12949807446897922481231729)
              ·
                refine ⟨9712355585173441860923797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12949807446897922481231729 9712355585173441860923797)
                ·
                  refine ⟨455266668055005087230803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9712355585173441860923797 455266668055005087230803)
                  ·
                    rfl

theorem cell23_7979658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_7979658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979658 prefixEnd_7979658 := by exact prefixLift 7979658
  have htrace : WordTrace (prefixWord ++ tailWord_7979658) baseStart_7979658 baseEnd_7979658 := by
    simpa [prefixWord, tailWord_7979658, baseEnd_7979658] using wordTrace_append hprefix tailTrace_7979658
  have hstable : (prefixWord ++ tailWord_7979658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979658).length < 2 ^ (prefixWord ++ tailWord_7979658).sum := by decide
  have hdescent : baseEnd_7979658 < baseStart_7979658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979678 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7979678 : Nat := 118140960795 + 7979678 * 2 ^ 59
def prefixEnd_7979678 : Nat := 4983230072969 + 3 ^ 40 * 7979678 * 2
def baseEnd_7979678 : Nat := 4097410282108135706827135

theorem tailTrace_7979678 : CollatzResearch.WordTrace tailWord_7979678 prefixEnd_7979678 4097410282108135706827135 := by
  unfold tailWord_7979678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36380345848124612668478461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194028511189997934231885125 36380345848124612668478461)
  ·
    refine ⟨13642629693046729750679423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36380345848124612668478461 13642629693046729750679423)
    ·
      refine ⟨20463944539570094626019135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642629693046729750679423 20463944539570094626019135)
      ·
        refine ⟨30695916809355141939028703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463944539570094626019135 30695916809355141939028703)
        ·
          refine ⟨46043875214032712908543055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30695916809355141939028703 46043875214032712908543055)
          ·
            refine ⟨69065812821049069362814583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46043875214032712908543055 69065812821049069362814583)
            ·
              refine ⟨103598719231573604044221875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69065812821049069362814583 103598719231573604044221875)
              ·
                refine ⟨155398078847360406066332813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103598719231573604044221875 155398078847360406066332813)
                ·
                  refine ⟨58274279567760152274874805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155398078847360406066332813 58274279567760152274874805)
                  ·
                    refine ⟨5463213709477514275769513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58274279567760152274874805 5463213709477514275769513)
                    ·
                      refine ⟨4097410282108135706827135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463213709477514275769513 4097410282108135706827135)
                      ·
                        rfl

theorem cell23_7979678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7979678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979678 prefixEnd_7979678 := by exact prefixLift 7979678
  have htrace : WordTrace (prefixWord ++ tailWord_7979678) baseStart_7979678 baseEnd_7979678 := by
    simpa [prefixWord, tailWord_7979678, baseEnd_7979678] using wordTrace_append hprefix tailTrace_7979678
  have hstable : (prefixWord ++ tailWord_7979678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979678).length < 2 ^ (prefixWord ++ tailWord_7979678).sum := by decide
  have hdescent : baseEnd_7979678 < baseStart_7979678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979711 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_7979711 : Nat := 118140960795 + 7979711 * 2 ^ 59
def prefixEnd_7979711 : Nat := 4983230072969 + 3 ^ 40 * 7979711 * 2
def baseEnd_7979711 : Nat := 4097427226969734077714483

theorem tailTrace_7979711 : CollatzResearch.WordTrace tailWord_7979711 prefixEnd_7979711 4097427226969734077714483 := by
  unfold tailWord_7979711
  simp only [CollatzResearch.WordTrace]
  refine ⟨291043970393877347983778987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194029313595918231989185991 291043970393877347983778987)
  ·
    refine ⟨436565955590816021975668481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291043970393877347983778987 436565955590816021975668481)
    ·
      refine ⟨327424466693112016481751361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436565955590816021975668481 327424466693112016481751361)
      ·
        refine ⟨245568350019834012361313521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327424466693112016481751361 245568350019834012361313521)
        ·
          refine ⟨184176262514875509270985141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245568350019834012361313521 184176262514875509270985141)
          ·
            refine ⟨17266524610769578994154857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184176262514875509270985141 17266524610769578994154857)
            ·
              refine ⟨12949893458077184245616143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17266524610769578994154857 12949893458077184245616143)
              ·
                refine ⟨19424840187115776368424215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949893458077184245616143 19424840187115776368424215)
                ·
                  refine ⟨29137260280673664552636323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19424840187115776368424215 29137260280673664552636323)
                  ·
                    refine ⟨43705890421010496828954485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29137260280673664552636323 43705890421010496828954485)
                    ·
                      refine ⟨4097427226969734077714483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43705890421010496828954485 4097427226969734077714483)
                      ·
                        rfl

theorem cell23_7979711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_7979711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979711 prefixEnd_7979711 := by exact prefixLift 7979711
  have htrace : WordTrace (prefixWord ++ tailWord_7979711) baseStart_7979711 baseEnd_7979711 := by
    simpa [prefixWord, tailWord_7979711, baseEnd_7979711] using wordTrace_append hprefix tailTrace_7979711
  have hstable : (prefixWord ++ tailWord_7979711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979711).length < 2 ^ (prefixWord ++ tailWord_7979711).sum := by decide
  have hdescent : baseEnd_7979711 < baseStart_7979711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979735 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 2, 4]
def baseStart_7979735 : Nat := 118140960795 + 7979735 * 2 ^ 59
def prefixEnd_7979735 : Nat := 4983230072969 + 3 ^ 40 * 7979735 * 2
def baseEnd_7979735 : Nat := 1365813183501813994604791

theorem tailTrace_7979735 : CollatzResearch.WordTrace tailWord_7979735 prefixEnd_7979735 1365813183501813994604791 := by
  unfold tailWord_7979735
  simp only [CollatzResearch.WordTrace]
  refine ⟨291044845745790400082652659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194029897163860266721768439 291044845745790400082652659)
  ·
    refine ⟨436567268618685600123978989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291044845745790400082652659 436567268618685600123978989)
    ·
      refine ⟨163712725732007100046492121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436567268618685600123978989 163712725732007100046492121)
      ·
        refine ⟨122784544299005325034869091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163712725732007100046492121 122784544299005325034869091)
        ·
          refine ⟨184176816448507987552303637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122784544299005325034869091 184176816448507987552303637)
          ·
            refine ⟨8633288271023811916514233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184176816448507987552303637 8633288271023811916514233)
            ·
              refine ⟨6474966203267858937385675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633288271023811916514233 6474966203267858937385675)
              ·
                refine ⟨9712449304901788406078513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6474966203267858937385675 9712449304901788406078513)
                ·
                  refine ⟨7284336978676341304558885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712449304901788406078513 7284336978676341304558885)
                  ·
                    refine ⟨1365813183501813994604791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284336978676341304558885 1365813183501813994604791)
                    ·
                      rfl

theorem cell23_7979735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_7979735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979735 prefixEnd_7979735 := by exact prefixLift 7979735
  have htrace : WordTrace (prefixWord ++ tailWord_7979735) baseStart_7979735 baseEnd_7979735 := by
    simpa [prefixWord, tailWord_7979735, baseEnd_7979735] using wordTrace_append hprefix tailTrace_7979735
  have hstable : (prefixWord ++ tailWord_7979735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979735).length < 2 ^ (prefixWord ++ tailWord_7979735).sum := by decide
  have hdescent : baseEnd_7979735 < baseStart_7979735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979745 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_7979745 : Nat := 118140960795 + 7979745 * 2 ^ 59
def prefixEnd_7979745 : Nat := 4983230072969 + 3 ^ 40 * 7979745 * 2
def baseEnd_7979745 : Nat := 4097444685311986944689327

theorem tailTrace_7979745 : CollatzResearch.WordTrace tailWord_7979745 prefixEnd_7979745 4097444685311986944689327 := by
  unfold tailWord_7979745
  simp only [CollatzResearch.WordTrace]
  refine ⟨291045210475754171790516689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194030140317169447860344459 291045210475754171790516689)
  ·
    refine ⟨218283907856815628842887517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291045210475754171790516689 218283907856815628842887517)
    ·
      refine ⟨81856465446305860816082819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218283907856815628842887517 81856465446305860816082819)
      ·
        refine ⟨122784698169458791224124229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81856465446305860816082819 122784698169458791224124229)
        ·
          refine ⟨23022130906773523354523293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122784698169458791224124229 23022130906773523354523293)
          ·
            refine ⟨8633299090040071257946235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23022130906773523354523293 8633299090040071257946235)
            ·
              refine ⟨12949948635060106886919353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633299090040071257946235 12949948635060106886919353)
              ·
                refine ⟨9712461476295080165189515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12949948635060106886919353 9712461476295080165189515)
                ·
                  refine ⟨14568692214442620247784273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712461476295080165189515 14568692214442620247784273)
                  ·
                    refine ⟨10926519160831965185838205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14568692214442620247784273 10926519160831965185838205)
                    ·
                      refine ⟨4097444685311986944689327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926519160831965185838205 4097444685311986944689327)
                      ·
                        rfl

theorem cell23_7979745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_7979745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979745 prefixEnd_7979745 := by exact prefixLift 7979745
  have htrace : WordTrace (prefixWord ++ tailWord_7979745) baseStart_7979745 baseEnd_7979745 := by
    simpa [prefixWord, tailWord_7979745, baseEnd_7979745] using wordTrace_append hprefix tailTrace_7979745
  have hstable : (prefixWord ++ tailWord_7979745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979745).length < 2 ^ (prefixWord ++ tailWord_7979745).sum := by decide
  have hdescent : baseEnd_7979745 < baseStart_7979745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979758 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_7979758 : Nat := 118140960795 + 7979758 * 2 ^ 59
def prefixEnd_7979758 : Nat := 4983230072969 + 3 ^ 40 * 7979758 * 2
def baseEnd_7979758 : Nat := 4097451360560495393826767

theorem tailTrace_7979758 : CollatzResearch.WordTrace tailWord_7979758 prefixEnd_7979758 4097451360560495393826767 := by
  unfold tailWord_7979758
  simp only [CollatzResearch.WordTrace]
  refine ⟨36380710578088384376342491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194030456416471383340493285 36380710578088384376342491)
  ·
    refine ⟨54571065867132576564513737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36380710578088384376342491 54571065867132576564513737)
    ·
      refine ⟨40928299400349432423385303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54571065867132576564513737 40928299400349432423385303)
      ·
        refine ⟨61392449100524148635077955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40928299400349432423385303 61392449100524148635077955)
        ·
          refine ⟨92088673650786222952616933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61392449100524148635077955 92088673650786222952616933)
          ·
            refine ⟨17266626309522416803615675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92088673650786222952616933 17266626309522416803615675)
            ·
              refine ⟨25899939464283625205423513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17266626309522416803615675 25899939464283625205423513)
              ·
                refine ⟨19424954598212718904067635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25899939464283625205423513 19424954598212718904067635)
                ·
                  refine ⟨29137431897319078356101453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19424954598212718904067635 29137431897319078356101453)
                  ·
                    refine ⟨10926536961494654383538045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29137431897319078356101453 10926536961494654383538045)
                    ·
                      refine ⟨4097451360560495393826767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926536961494654383538045 4097451360560495393826767)
                      ·
                        rfl

theorem cell23_7979758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_7979758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979758 prefixEnd_7979758 := by exact prefixLift 7979758
  have htrace : WordTrace (prefixWord ++ tailWord_7979758) baseStart_7979758 baseEnd_7979758 := by
    simpa [prefixWord, tailWord_7979758, baseEnd_7979758] using wordTrace_append hprefix tailTrace_7979758
  have hstable : (prefixWord ++ tailWord_7979758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979758).length < 2 ^ (prefixWord ++ tailWord_7979758).sum := by decide
  have hdescent : baseEnd_7979758 < baseStart_7979758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979765 : List Nat := [1, 3, 6, 1, 2, 10]
def baseStart_7979765 : Nat := 118140960795 + 7979765 * 2 ^ 59
def prefixEnd_7979765 : Nat := 4983230072969 + 3 ^ 40 * 7979765 * 2
def baseEnd_7979765 : Nat := 16861954547016777228145

theorem tailTrace_7979765 : CollatzResearch.WordTrace tailWord_7979765 prefixEnd_7979765 16861954547016777228145 := by
  unfold tailWord_7979765
  simp only [CollatzResearch.WordTrace]
  refine ⟨291045939935681715206244749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194030626623787810137496499 291045939935681715206244749)
  ·
    refine ⟨109142227475880643202341781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291045939935681715206244749 109142227475880643202341781)
    ·
      refine ⟨5116041912931905150109771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109142227475880643202341781 5116041912931905150109771)
      ·
        refine ⟨7674062869397857725164657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116041912931905150109771 7674062869397857725164657)
        ·
          refine ⟨5755547152048393293873493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7674062869397857725164657 5755547152048393293873493)
          ·
            refine ⟨16861954547016777228145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5755547152048393293873493 16861954547016777228145)
            ·
              rfl

theorem cell23_7979765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 10].length) (baseStart_7979765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979765 prefixEnd_7979765 := by exact prefixLift 7979765
  have htrace : WordTrace (prefixWord ++ tailWord_7979765) baseStart_7979765 baseEnd_7979765 := by
    simpa [prefixWord, tailWord_7979765, baseEnd_7979765] using wordTrace_append hprefix tailTrace_7979765
  have hstable : (prefixWord ++ tailWord_7979765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979765).length < 2 ^ (prefixWord ++ tailWord_7979765).sum := by decide
  have hdescent : baseEnd_7979765 < baseStart_7979765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979831 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_7979831 : Nat := 118140960795 + 7979831 * 2 ^ 59
def prefixEnd_7979831 : Nat := 4983230072969 + 3 ^ 40 * 7979831 * 2
def baseEnd_7979831 : Nat := 4097488844648273608213931

theorem tailTrace_7979831 : CollatzResearch.WordTrace tailWord_7979831 prefixEnd_7979831 4097488844648273608213931 := by
  unfold tailWord_7979831
  simp only [CollatzResearch.WordTrace]
  refine ⟨291048347153442608478147347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194032231435628405652098231 291048347153442608478147347)
  ·
    refine ⟨436572520730163912717221021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291048347153442608478147347 436572520730163912717221021)
    ·
      refine ⟨163714695273811467268957883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436572520730163912717221021 163714695273811467268957883)
      ·
        refine ⟨245572042910717200903436825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163714695273811467268957883 245572042910717200903436825)
        ·
          refine ⟨184179032183037900677577619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245572042910717200903436825 184179032183037900677577619)
          ·
            refine ⟨276268548274556851016366429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184179032183037900677577619 276268548274556851016366429)
            ·
              refine ⟨103600705602958819131137411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276268548274556851016366429 103600705602958819131137411)
              ·
                refine ⟨155401058404438228696706117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103600705602958819131137411 155401058404438228696706117)
                ·
                  refine ⟨29137698450832167880632397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155401058404438228696706117 29137698450832167880632397)
                  ·
                    refine ⟨10926636919062062955237149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29137698450832167880632397 10926636919062062955237149)
                    ·
                      refine ⟨4097488844648273608213931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926636919062062955237149 4097488844648273608213931)
                      ·
                        rfl

theorem cell23_7979831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_7979831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979831 prefixEnd_7979831 := by exact prefixLift 7979831
  have htrace : WordTrace (prefixWord ++ tailWord_7979831) baseStart_7979831 baseEnd_7979831 := by
    simpa [prefixWord, tailWord_7979831, baseEnd_7979831] using wordTrace_append hprefix tailTrace_7979831
  have hstable : (prefixWord ++ tailWord_7979831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979831).length < 2 ^ (prefixWord ++ tailWord_7979831).sum := by decide
  have hdescent : baseEnd_7979831 < baseStart_7979831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979868 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7979868 : Nat := 118140960795 + 7979868 * 2 ^ 59
def prefixEnd_7979868 : Nat := 4983230072969 + 3 ^ 40 * 7979868 * 2
def baseEnd_7979868 : Nat := 1365835947810829987817087

theorem tailTrace_7979868 : CollatzResearch.WordTrace tailWord_7979868 prefixEnd_7979868 1365835947810829987817087 := by
  unfold tailWord_7979868
  simp only [CollatzResearch.WordTrace]
  refine ⟨145524848327154281898622129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194033131102872375864829505 145524848327154281898622129)
  ·
    refine ⟨109143636245365711423966597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145524848327154281898622129 109143636245365711423966597)
    ·
      refine ⟨20464431796006070891993737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109143636245365711423966597 20464431796006070891993737)
      ·
        refine ⟨15348323847004553168995303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20464431796006070891993737 15348323847004553168995303)
        ·
          refine ⟨23022485770506829753492955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348323847004553168995303 23022485770506829753492955)
          ·
            refine ⟨34533728655760244630239433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23022485770506829753492955 34533728655760244630239433)
            ·
              refine ⟨25900296491820183472679575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34533728655760244630239433 25900296491820183472679575)
              ·
                refine ⟨38850444737730275209019363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25900296491820183472679575 38850444737730275209019363)
                ·
                  refine ⟨58275667106595412813529045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38850444737730275209019363 58275667106595412813529045)
                  ·
                    refine ⟨1365835947810829987817087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58275667106595412813529045 1365835947810829987817087)
                    ·
                      rfl

theorem cell23_7979868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7979868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979868 prefixEnd_7979868 := by exact prefixLift 7979868
  have htrace : WordTrace (prefixWord ++ tailWord_7979868) baseStart_7979868 baseEnd_7979868 := by
    simpa [prefixWord, tailWord_7979868, baseEnd_7979868] using wordTrace_append hprefix tailTrace_7979868
  have hstable : (prefixWord ++ tailWord_7979868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979868).length < 2 ^ (prefixWord ++ tailWord_7979868).sum := by decide
  have hdescent : baseEnd_7979868 < baseStart_7979868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979871 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_7979871 : Nat := 118140960795 + 7979871 * 2 ^ 59
def prefixEnd_7979871 : Nat := 4983230072969 + 3 ^ 40 * 7979871 * 2
def baseEnd_7979871 : Nat := 4097509383874453451713747

theorem tailTrace_7979871 : CollatzResearch.WordTrace tailWord_7979871 prefixEnd_7979871 4097509383874453451713747 := by
  unfold tailWord_7979871
  simp only [CollatzResearch.WordTrace]
  refine ⟨291049806073297695309603467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194033204048865130206402311 291049806073297695309603467)
  ·
    refine ⟨436574709109946542964405201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291049806073297695309603467 436574709109946542964405201)
    ·
      refine ⟨327431031832459907223303901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436574709109946542964405201 327431031832459907223303901)
      ·
        refine ⟨122786636937172465208738963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327431031832459907223303901 122786636937172465208738963)
        ·
          refine ⟨184179955405758697813108445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122786636937172465208738963 184179955405758697813108445)
          ·
            refine ⟨69067483277159511679915667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184179955405758697813108445 69067483277159511679915667)
            ·
              refine ⟨103601224915739267519873501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69067483277159511679915667 103601224915739267519873501)
              ·
                refine ⟨38850459343402225319952563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103601224915739267519873501 38850459343402225319952563)
                ·
                  refine ⟨58275689015103337979928845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38850459343402225319952563 58275689015103337979928845)
                  ·
                    refine ⟨21853383380663751742473317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58275689015103337979928845 21853383380663751742473317)
                    ·
                      refine ⟨4097509383874453451713747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21853383380663751742473317 4097509383874453451713747)
                      ·
                        rfl

theorem cell23_7979871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_7979871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979871 prefixEnd_7979871 := by exact prefixLift 7979871
  have htrace : WordTrace (prefixWord ++ tailWord_7979871) baseStart_7979871 baseEnd_7979871 := by
    simpa [prefixWord, tailWord_7979871, baseEnd_7979871] using wordTrace_append hprefix tailTrace_7979871
  have hstable : (prefixWord ++ tailWord_7979871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979871).length < 2 ^ (prefixWord ++ tailWord_7979871).sum := by decide
  have hdescent : baseEnd_7979871 < baseStart_7979871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979888 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2]
def baseStart_7979888 : Nat := 118140960795 + 7979888 * 2 ^ 59
def prefixEnd_7979888 : Nat := 4983230072969 + 3 ^ 40 * 7979888 * 2
def baseEnd_7979888 : Nat := 4097518113045579885201169

theorem tailTrace_7979888 : CollatzResearch.WordTrace tailWord_7979888 prefixEnd_7979888 4097518113045579885201169 := by
  unfold tailWord_7979888
  simp only [CollatzResearch.WordTrace]
  refine ⟨145525213057118053606486159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194033617409490738141981545 145525213057118053606486159)
  ·
    refine ⟨218287819585677080409729239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145525213057118053606486159 218287819585677080409729239)
    ·
      refine ⟨327431729378515620614593859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218287819585677080409729239 327431729378515620614593859)
      ·
        refine ⟨491147594067773430921890789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327431729378515620614593859 491147594067773430921890789)
        ·
          refine ⟨92090173887707518297854523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 491147594067773430921890789 92090173887707518297854523)
          ·
            refine ⟨138135260831561277446781785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92090173887707518297854523 138135260831561277446781785)
            ·
              refine ⟨103601445623670958085086339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138135260831561277446781785 103601445623670958085086339)
              ·
                refine ⟨155402168435506437127629509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103601445623670958085086339 155402168435506437127629509)
                ·
                  refine ⟨29137906581657456961430533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155402168435506437127629509 29137906581657456961430533)
                  ·
                    refine ⟨5463357484060773180268225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29137906581657456961430533 5463357484060773180268225)
                    ·
                      refine ⟨4097518113045579885201169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463357484060773180268225 4097518113045579885201169)
                      ·
                        rfl

theorem cell23_7979888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 4, 2].length) (baseStart_7979888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979888 prefixEnd_7979888 := by exact prefixLift 7979888
  have htrace : WordTrace (prefixWord ++ tailWord_7979888) baseStart_7979888 baseEnd_7979888 := by
    simpa [prefixWord, tailWord_7979888, baseEnd_7979888] using wordTrace_append hprefix tailTrace_7979888
  have hstable : (prefixWord ++ tailWord_7979888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979888).length < 2 ^ (prefixWord ++ tailWord_7979888).sum := by decide
  have hdescent : baseEnd_7979888 < baseStart_7979888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979901 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_7979901 : Nat := 118140960795 + 7979901 * 2 ^ 59
def prefixEnd_7979901 : Nat := 4983230072969 + 3 ^ 40 * 7979901 * 2
def baseEnd_7979901 : Nat := 4097524788294088334338609

theorem tailTrace_7979901 : CollatzResearch.WordTrace tailWord_7979901 prefixEnd_7979901 4097524788294088334338609 := by
  unfold tailWord_7979901
  simp only [CollatzResearch.WordTrace]
  refine ⟨291050900263189010433195557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194033933508792673622130371 291050900263189010433195557)
  ·
    refine ⟨54572043799347939456224167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291050900263189010433195557 54572043799347939456224167)
    ·
      refine ⟨81858065699021909184336251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54572043799347939456224167 81858065699021909184336251)
      ·
        refine ⟨122787098548532863776504377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81858065699021909184336251 122787098548532863776504377)
        ·
          refine ⟨92090323911399647832378283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122787098548532863776504377 92090323911399647832378283)
          ·
            refine ⟨138135485867099471748567425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92090323911399647832378283 138135485867099471748567425)
            ·
              refine ⟨103601614400324603811425569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138135485867099471748567425 103601614400324603811425569)
              ·
                refine ⟨77701210800243452858569177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103601614400324603811425569 77701210800243452858569177)
                ·
                  refine ⟨58275908100182589643926883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77701210800243452858569177 58275908100182589643926883)
                  ·
                    refine ⟨87413862150273884465890325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58275908100182589643926883 87413862150273884465890325)
                    ·
                      refine ⟨4097524788294088334338609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87413862150273884465890325 4097524788294088334338609)
                      ·
                        rfl

theorem cell23_7979901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_7979901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979901 prefixEnd_7979901 := by exact prefixLift 7979901
  have htrace : WordTrace (prefixWord ++ tailWord_7979901) baseStart_7979901 baseEnd_7979901 := by
    simpa [prefixWord, tailWord_7979901, baseEnd_7979901] using wordTrace_append hprefix tailTrace_7979901
  have hstable : (prefixWord ++ tailWord_7979901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979901).length < 2 ^ (prefixWord ++ tailWord_7979901).sum := by decide
  have hdescent : baseEnd_7979901 < baseStart_7979901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979908 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_7979908 : Nat := 118140960795 + 7979908 * 2 ^ 59
def prefixEnd_7979908 : Nat := 4983230072969 + 3 ^ 40 * 7979908 * 2
def baseEnd_7979908 : Nat := 4097528382658669806951077

theorem tailTrace_7979908 : CollatzResearch.WordTrace tailWord_7979908 prefixEnd_7979908 4097528382658669806951077 := by
  unfold tailWord_7979908
  simp only [CollatzResearch.WordTrace]
  refine ⟨145525577787081825314350189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194034103716109100419133585 145525577787081825314350189)
  ·
    refine ⟨54572091670155684492881321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145525577787081825314350189 54572091670155684492881321)
    ·
      refine ⟨40929068752616763369660991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54572091670155684492881321 40929068752616763369660991)
      ·
        refine ⟨61393603128925145054491487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40929068752616763369660991 61393603128925145054491487)
        ·
          refine ⟨92090404693387717581737231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61393603128925145054491487 92090404693387717581737231)
          ·
            refine ⟨138135607040081576372605847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92090404693387717581737231 138135607040081576372605847)
            ·
              refine ⟨207203410560122364558908771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138135607040081576372605847 207203410560122364558908771)
              ·
                refine ⟨310805115840183546838363157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207203410560122364558908771 310805115840183546838363157)
                ·
                  refine ⟨14568989805008603758048273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310805115840183546838363157 14568989805008603758048273)
                  ·
                    refine ⟨10926742353756452818536205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14568989805008603758048273 10926742353756452818536205)
                    ·
                      refine ⟨4097528382658669806951077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926742353756452818536205 4097528382658669806951077)
                      ·
                        rfl

theorem cell23_7979908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_7979908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979908 prefixEnd_7979908 := by exact prefixLift 7979908
  have htrace : WordTrace (prefixWord ++ tailWord_7979908) baseStart_7979908 baseEnd_7979908 := by
    simpa [prefixWord, tailWord_7979908, baseEnd_7979908] using wordTrace_append hprefix tailTrace_7979908
  have hstable : (prefixWord ++ tailWord_7979908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979908).length < 2 ^ (prefixWord ++ tailWord_7979908).sum := by decide
  have hdescent : baseEnd_7979908 < baseStart_7979908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979922 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7979922 : Nat := 118140960795 + 7979922 * 2 ^ 59
def prefixEnd_7979922 : Nat := 4983230072969 + 3 ^ 40 * 7979922 * 2
def baseEnd_7979922 : Nat := 4097535571387832752176013

theorem tailTrace_7979922 : CollatzResearch.WordTrace tailWord_7979922 prefixEnd_7979922 4097535571387832752176013 := by
  unfold tailWord_7979922
  simp only [CollatzResearch.WordTrace]
  refine ⟨72762916549028232754927505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194034444130741954013140013 72762916549028232754927505)
  ·
    refine ⟨54572187411771174566195629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72762916549028232754927505 54572187411771174566195629)
    ·
      refine ⟨20464570279414190462323361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54572187411771174566195629 20464570279414190462323361)
      ·
        refine ⟨15348427709560642846742521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20464570279414190462323361 15348427709560642846742521)
        ·
          refine ⟨11511320782170482135056891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15348427709560642846742521 11511320782170482135056891)
          ·
            refine ⟨17266981173255723202585337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11511320782170482135056891 17266981173255723202585337)
            ·
              refine ⟨12950235879941792401939003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17266981173255723202585337 12950235879941792401939003)
              ·
                refine ⟨19425353819912688602908505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950235879941792401939003 19425353819912688602908505)
                ·
                  refine ⟨14569015364934516452181379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19425353819912688602908505 14569015364934516452181379)
                  ·
                    refine ⟨21853523047401774678272069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14569015364934516452181379 21853523047401774678272069)
                    ·
                      refine ⟨4097535571387832752176013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21853523047401774678272069 4097535571387832752176013)
                      ·
                        rfl

theorem cell23_7979922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7979922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979922 prefixEnd_7979922 := by exact prefixLift 7979922
  have htrace : WordTrace (prefixWord ++ tailWord_7979922) baseStart_7979922 baseEnd_7979922 := by
    simpa [prefixWord, tailWord_7979922, baseEnd_7979922] using wordTrace_append hprefix tailTrace_7979922
  have hstable : (prefixWord ++ tailWord_7979922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979922).length < 2 ^ (prefixWord ++ tailWord_7979922).sum := by decide
  have hdescent : baseEnd_7979922 < baseStart_7979922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979925 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_7979925 : Nat := 118140960795 + 7979925 * 2 ^ 59
def prefixEnd_7979925 : Nat := 4983230072969 + 3 ^ 40 * 7979925 * 2
def baseEnd_7979925 : Nat := 4097537111829796240438499

theorem tailTrace_7979925 : CollatzResearch.WordTrace tailWord_7979925 prefixEnd_7979925 4097537111829796240438499 := by
  unfold tailWord_7979925
  simp only [CollatzResearch.WordTrace]
  refine ⟨291051775615102062532069229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194034517076734708354712819 291051775615102062532069229)
  ·
    refine ⟨109144415855663273449525961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291051775615102062532069229 109144415855663273449525961)
    ·
      refine ⟨81858311891747455087144471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109144415855663273449525961 81858311891747455087144471)
      ·
        refine ⟨122787467837621182630716707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81858311891747455087144471 122787467837621182630716707)
        ·
          refine ⟨184181201756431773946075061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122787467837621182630716707 184181201756431773946075061)
          ·
            refine ⟨17266987664665478807444537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184181201756431773946075061 17266987664665478807444537)
            ·
              refine ⟨12950240748499109105583403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17266987664665478807444537 12950240748499109105583403)
              ·
                refine ⟨19425361122748663658375105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950240748499109105583403 19425361122748663658375105)
                ·
                  refine ⟨14569020842061497743781329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19425361122748663658375105 14569020842061497743781329)
                  ·
                    refine ⟨10926765631546123307835997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14569020842061497743781329 10926765631546123307835997)
                    ·
                      refine ⟨4097537111829796240438499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10926765631546123307835997 4097537111829796240438499)
                      ·
                        rfl

theorem cell23_7979925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_7979925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979925 prefixEnd_7979925 := by exact prefixLift 7979925
  have htrace : WordTrace (prefixWord ++ tailWord_7979925) baseStart_7979925 baseEnd_7979925 := by
    simpa [prefixWord, tailWord_7979925, baseEnd_7979925] using wordTrace_append hprefix tailTrace_7979925
  have hstable : (prefixWord ++ tailWord_7979925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979925).length < 2 ^ (prefixWord ++ tailWord_7979925).sum := by decide
  have hdescent : baseEnd_7979925 < baseStart_7979925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979971 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 5, 6]
def baseStart_7979971 : Nat := 118140960795 + 7979971 * 2 ^ 59
def prefixEnd_7979971 : Nat := 4983230072969 + 3 ^ 40 * 7979971 * 2
def baseEnd_7979971 : Nat := 1365853577313301020154429

theorem tailTrace_7979971 : CollatzResearch.WordTrace tailWord_7979971 prefixEnd_7979971 1365853577313301020154429 := by
  unfold tailWord_7979971
  simp only [CollatzResearch.WordTrace]
  refine ⟨291053453372935412388243767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194035635581956941592162511 291053453372935412388243767)
  ·
    refine ⟨436580180059403118582365651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291053453372935412388243767 436580180059403118582365651)
    ·
      refine ⟨654870270089104677873548477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436580180059403118582365651 654870270089104677873548477)
      ·
        refine ⟨245576351283414254202580679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654870270089104677873548477 245576351283414254202580679)
        ·
          refine ⟨368364526925121381303871019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245576351283414254202580679 368364526925121381303871019)
          ·
            refine ⟨552546790387682071955806529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368364526925121381303871019 552546790387682071955806529)
            ·
              refine ⟨414410092790761553966854897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552546790387682071955806529 414410092790761553966854897)
              ·
                refine ⟨310807569593071165475141173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414410092790761553966854897 310807569593071165475141173)
                ·
                  refine ⟨29138209649350421763294485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310807569593071165475141173 29138209649350421763294485)
                  ·
                    refine ⟨1365853577313301020154429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29138209649350421763294485 1365853577313301020154429)
                    ·
                      rfl

theorem cell23_7979971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_7979971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979971 prefixEnd_7979971 := by exact prefixLift 7979971
  have htrace : WordTrace (prefixWord ++ tailWord_7979971) baseStart_7979971 baseEnd_7979971 := by
    simpa [prefixWord, tailWord_7979971, baseEnd_7979971] using wordTrace_append hprefix tailTrace_7979971
  have hstable : (prefixWord ++ tailWord_7979971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979971).length < 2 ^ (prefixWord ++ tailWord_7979971).sum := by decide
  have hdescent : baseEnd_7979971 < baseStart_7979971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979982 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_7979982 : Nat := 118140960795 + 7979982 * 2 ^ 59
def prefixEnd_7979982 : Nat := 4983230072969 + 3 ^ 40 * 7979982 * 2
def baseEnd_7979982 : Nat := 4097566380227102517425737

theorem tailTrace_7979982 : CollatzResearch.WordTrace tailWord_7979982 prefixEnd_7979982 4097566380227102517425737 := by
  unfold tailWord_7979982
  simp only [CollatzResearch.WordTrace]
  refine ⟨36381731821986945158361775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194035903050597040844596133 36381731821986945158361775)
  ·
    refine ⟨54572597732980417737542663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36381731821986945158361775 54572597732980417737542663)
    ·
      refine ⟨81858896599470626606313995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54572597732980417737542663 81858896599470626606313995)
      ·
        refine ⟨122788344899205939909470993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81858896599470626606313995 122788344899205939909470993)
        ·
          refine ⟨92091258674404454932103245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122788344899205939909470993 92091258674404454932103245)
          ·
            refine ⟨34534222002901670599538717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92091258674404454932103245 34534222002901670599538717)
            ·
              refine ⟨12950333251088126474827019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34534222002901670599538717 12950333251088126474827019)
              ·
                refine ⟨19425499876632189712240529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950333251088126474827019 19425499876632189712240529)
                ·
                  refine ⟨14569124907474142284180397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19425499876632189712240529 14569124907474142284180397)
                  ·
                    refine ⟨5463421840302803356567649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14569124907474142284180397 5463421840302803356567649)
                    ·
                      refine ⟨4097566380227102517425737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463421840302803356567649 4097566380227102517425737)
                      ·
                        rfl

theorem cell23_7979982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_7979982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979982 prefixEnd_7979982 := by exact prefixLift 7979982
  have htrace : WordTrace (prefixWord ++ tailWord_7979982) baseStart_7979982 baseEnd_7979982 := by
    simpa [prefixWord, tailWord_7979982, baseEnd_7979982] using wordTrace_append hprefix tailTrace_7979982
  have hstable : (prefixWord ++ tailWord_7979982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979982).length < 2 ^ (prefixWord ++ tailWord_7979982).sum := by decide
  have hdescent : baseEnd_7979982 < baseStart_7979982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7979992 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 1, 5]
def baseStart_7979992 : Nat := 118140960795 + 7979992 * 2 ^ 59
def prefixEnd_7979992 : Nat := 4983230072969 + 3 ^ 40 * 7979992 * 2
def baseEnd_7979992 : Nat := 1365857171677882492766897

theorem tailTrace_7979992 : CollatzResearch.WordTrace tailWord_7979992 prefixEnd_7979992 1365857171677882492766897 := by
  unfold tailWord_7979992
  simp only [CollatzResearch.WordTrace]
  refine ⟨145527109652929666487379115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194036146203906221983172153 145527109652929666487379115)
  ·
    refine ⟨218290664479394499731068673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145527109652929666487379115 218290664479394499731068673)
    ·
      refine ⟨163717998359545874798301505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218290664479394499731068673 163717998359545874798301505)
      ·
        refine ⟨122788498769659406098726129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163717998359545874798301505 122788498769659406098726129)
        ·
          refine ⟨92091374077244554574044597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122788498769659406098726129 92091374077244554574044597)
          ·
            refine ⟨8633566319741676991316681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92091374077244554574044597 8633566319741676991316681)
            ·
              refine ⟨6475174739806257743487511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633566319741676991316681 6475174739806257743487511)
              ·
                refine ⟨9712762109709386615231267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475174739806257743487511 9712762109709386615231267)
                ·
                  refine ⟨14569143164564079922846901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712762109709386615231267 14569143164564079922846901)
                  ·
                    refine ⟨1365857171677882492766897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14569143164564079922846901 1365857171677882492766897)
                    ·
                      rfl

theorem cell23_7979992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_7979992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7979992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7979992 prefixEnd_7979992 := by exact prefixLift 7979992
  have htrace : WordTrace (prefixWord ++ tailWord_7979992) baseStart_7979992 baseEnd_7979992 := by
    simpa [prefixWord, tailWord_7979992, baseEnd_7979992] using wordTrace_append hprefix tailTrace_7979992
  have hstable : (prefixWord ++ tailWord_7979992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7979992).length < 2 ^ (prefixWord ++ tailWord_7979992).sum := by decide
  have hdescent : baseEnd_7979992 < baseStart_7979992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7979992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980008 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7980008 : Nat := 118140960795 + 7980008 * 2 ^ 59
def prefixEnd_7980008 : Nat := 4983230072969 + 3 ^ 40 * 7980008 * 2
def baseEnd_7980008 : Nat := 4097579730724119415700617

theorem tailTrace_7980008 : CollatzResearch.WordTrace tailWord_7980008 prefixEnd_7980008 4097579730724119415700617 := by
  unfold tailWord_7980008
  simp only [CollatzResearch.WordTrace]
  refine ⟨145527401436900683853670339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194036535249200911804893785 145527401436900683853670339)
  ·
    refine ⟨218291102155351025780505509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145527401436900683853670339 218291102155351025780505509)
    ·
      refine ⟨40929581654128317333844783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218291102155351025780505509 40929581654128317333844783)
      ·
        refine ⟨61394372481192476000767175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40929581654128317333844783 61394372481192476000767175)
        ·
          refine ⟨92091558721788714001150763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61394372481192476000767175 92091558721788714001150763)
          ·
            refine ⟨138137338082683071001726145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92091558721788714001150763 138137338082683071001726145)
            ·
              refine ⟨103603003562012303251294609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138137338082683071001726145 103603003562012303251294609)
              ·
                refine ⟨77702252671509227438470957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103603003562012303251294609 77702252671509227438470957)
                ·
                  refine ⟨29138344751815960289426609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77702252671509227438470957 29138344751815960289426609)
                  ·
                    refine ⟨21853758563861970217069957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29138344751815960289426609 21853758563861970217069957)
                    ·
                      refine ⟨4097579730724119415700617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21853758563861970217069957 4097579730724119415700617)
                      ·
                        rfl

theorem cell23_7980008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7980008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980008 prefixEnd_7980008 := by exact prefixLift 7980008
  have htrace : WordTrace (prefixWord ++ tailWord_7980008) baseStart_7980008 baseEnd_7980008 := by
    simpa [prefixWord, tailWord_7980008, baseEnd_7980008] using wordTrace_append hprefix tailTrace_7980008
  have hstable : (prefixWord ++ tailWord_7980008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980008).length < 2 ^ (prefixWord ++ tailWord_7980008).sum := by decide
  have hdescent : baseEnd_7980008 < baseStart_7980008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980011 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_7980011 : Nat := 118140960795 + 7980011 * 2 ^ 59
def prefixEnd_7980011 : Nat := 4983230072969 + 3 ^ 40 * 7980011 * 2
def baseEnd_7980011 : Nat := 4097581271166082903963103

theorem tailTrace_7980011 : CollatzResearch.WordTrace tailWord_7980011 prefixEnd_7980011 4097581271166082903963103 := by
  unfold tailWord_7980011
  simp only [CollatzResearch.WordTrace]
  refine ⟨291054912292790499219699887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194036608195193666146466591 291054912292790499219699887)
  ·
    refine ⟨436582368439185748829549831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291054912292790499219699887 436582368439185748829549831)
    ·
      refine ⟨654873552658778623244324747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436582368439185748829549831 654873552658778623244324747)
      ·
        refine ⟨982310328988167934866487121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654873552658778623244324747 982310328988167934866487121)
        ·
          refine ⟨736732746741125951149865341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982310328988167934866487121 736732746741125951149865341)
          ·
            refine ⟨276274780027922231681199503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736732746741125951149865341 276274780027922231681199503)
            ·
              refine ⟨414412170041883347521799255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276274780027922231681199503 414412170041883347521799255)
              ·
                refine ⟨621618255062825021282698883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414412170041883347521799255 621618255062825021282698883)
                ·
                  refine ⟨932427382594237531924048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621618255062825021282698883 932427382594237531924048325)
                  ·
                    refine ⟨174830134236419537235759061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 932427382594237531924048325 174830134236419537235759061)
                    ·
                      refine ⟨4097581271166082903963103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174830134236419537235759061 4097581271166082903963103)
                      ·
                        rfl

theorem cell23_7980011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_7980011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980011 prefixEnd_7980011 := by exact prefixLift 7980011
  have htrace : WordTrace (prefixWord ++ tailWord_7980011) baseStart_7980011 baseEnd_7980011 := by
    simpa [prefixWord, tailWord_7980011, baseEnd_7980011] using wordTrace_append hprefix tailTrace_7980011
  have hstable : (prefixWord ++ tailWord_7980011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980011).length < 2 ^ (prefixWord ++ tailWord_7980011).sum := by decide
  have hdescent : baseEnd_7980011 < baseStart_7980011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980022 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_7980022 : Nat := 118140960795 + 7980022 * 2 ^ 59
def prefixEnd_7980022 : Nat := 4983230072969 + 3 ^ 40 * 7980022 * 2
def baseEnd_7980022 : Nat := 1365862306484427453641851

theorem tailTrace_7980022 : CollatzResearch.WordTrace tailWord_7980022 prefixEnd_7980022 1365862306484427453641851 := by
  unfold tailWord_7980022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190957093484415506146895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194036875663833765398900213 18190957093484415506146895)
  ·
    refine ⟨27286435640226623259220343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190957093484415506146895 27286435640226623259220343)
    ·
      refine ⟨40929653460339934888830515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27286435640226623259220343 40929653460339934888830515)
      ·
        refine ⟨61394480190509902333245773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40929653460339934888830515 61394480190509902333245773)
        ·
          refine ⟨23022930071441213374967165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61394480190509902333245773 23022930071441213374967165)
          ·
            refine ⟨8633598776790455015612687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23022930071441213374967165 8633598776790455015612687)
            ·
              refine ⟨12950398165185682523419031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633598776790455015612687 12950398165185682523419031)
              ·
                refine ⟨19425597247778523785128547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950398165185682523419031 19425597247778523785128547)
                ·
                  refine ⟨29138395871667785677692821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19425597247778523785128547 29138395871667785677692821)
                  ·
                    refine ⟨1365862306484427453641851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29138395871667785677692821 1365862306484427453641851)
                    ·
                      rfl

theorem cell23_7980022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_7980022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980022 prefixEnd_7980022 := by exact prefixLift 7980022
  have htrace : WordTrace (prefixWord ++ tailWord_7980022) baseStart_7980022 baseEnd_7980022 := by
    simpa [prefixWord, tailWord_7980022, baseEnd_7980022] using wordTrace_append hprefix tailTrace_7980022
  have hstable : (prefixWord ++ tailWord_7980022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980022).length < 2 ^ (prefixWord ++ tailWord_7980022).sum := by decide
  have hdescent : baseEnd_7980022 < baseStart_7980022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980046 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7980046 : Nat := 118140960795 + 7980046 * 2 ^ 59
def prefixEnd_7980046 : Nat := 4983230072969 + 3 ^ 40 * 7980046 * 2
def baseEnd_7980046 : Nat := 4097599242988990267025443

theorem tailTrace_7980046 : CollatzResearch.WordTrace tailWord_7980046 prefixEnd_7980046 4097599242988990267025443 := by
  unfold tailWord_7980046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36382023605957962524652999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194037459231775800131482661 36382023605957962524652999)
  ·
    refine ⟨54573035408936943786979499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36382023605957962524652999 54573035408936943786979499)
    ·
      refine ⟨81859553113405415680469249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54573035408936943786979499 81859553113405415680469249)
      ·
        refine ⟨61394664835054061760351937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81859553113405415680469249 61394664835054061760351937)
        ·
          refine ⟨46045998626290546320263953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61394664835054061760351937 46045998626290546320263953)
          ·
            refine ⟨34534498969717909740197965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46045998626290546320263953 34534498969717909740197965)
            ·
              refine ⟨12950437113644216152574237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34534498969717909740197965 12950437113644216152574237)
              ·
                refine ⟨4856413917616581057215339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12950437113644216152574237 4856413917616581057215339)
                ·
                  refine ⟨7284620876424871585823009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856413917616581057215339 7284620876424871585823009)
                  ·
                    refine ⟨5463465657318653689367257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7284620876424871585823009 5463465657318653689367257)
                    ·
                      refine ⟨4097599242988990267025443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463465657318653689367257 4097599242988990267025443)
                      ·
                        rfl

theorem cell23_7980046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7980046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980046 prefixEnd_7980046 := by exact prefixLift 7980046
  have htrace : WordTrace (prefixWord ++ tailWord_7980046) baseStart_7980046 baseEnd_7980046 := by
    simpa [prefixWord, tailWord_7980046, baseEnd_7980046] using wordTrace_append hprefix tailTrace_7980046
  have hstable : (prefixWord ++ tailWord_7980046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980046).length < 2 ^ (prefixWord ++ tailWord_7980046).sum := by decide
  have hdescent : baseEnd_7980046 < baseStart_7980046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980058 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_7980058 : Nat := 118140960795 + 7980058 * 2 ^ 59
def prefixEnd_7980058 : Nat := 4983230072969 + 3 ^ 40 * 7980058 * 2
def baseEnd_7980058 : Nat := 4097605404756844220075387

theorem tailTrace_7980058 : CollatzResearch.WordTrace tailWord_7980058 prefixEnd_7980058 4097605404756844220075387 := by
  unfold tailWord_7980058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72764156630905056561665207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194037751015746817497773885 72764156630905056561665207)
  ·
    refine ⟨109146234946357584842497811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72764156630905056561665207 109146234946357584842497811)
    ·
      refine ⟨163719352419536377263746717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109146234946357584842497811 163719352419536377263746717)
      ·
        refine ⟨61394757157326141473905019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163719352419536377263746717 61394757157326141473905019)
        ·
          refine ⟨92092135735989212210857529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61394757157326141473905019 92092135735989212210857529)
          ·
            refine ⟨69069101801991909158143147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92092135735989212210857529 69069101801991909158143147)
            ·
              refine ⟨103603652702987863737214721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69069101801991909158143147 103603652702987863737214721)
              ·
                refine ⟨77702739527240897802911041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103603652702987863737214721 77702739527240897802911041)
                ·
                  refine ⟨58277054645430673352183281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77702739527240897802911041 58277054645430673352183281)
                  ·
                    refine ⟨43707790984073005014137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58277054645430673352183281 43707790984073005014137461)
                    ·
                      refine ⟨4097605404756844220075387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43707790984073005014137461 4097605404756844220075387)
                      ·
                        rfl

theorem cell23_7980058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_7980058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980058 prefixEnd_7980058 := by exact prefixLift 7980058
  have htrace : WordTrace (prefixWord ++ tailWord_7980058) baseStart_7980058 baseEnd_7980058 := by
    simpa [prefixWord, tailWord_7980058, baseEnd_7980058] using wordTrace_append hprefix tailTrace_7980058
  have hstable : (prefixWord ++ tailWord_7980058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980058).length < 2 ^ (prefixWord ++ tailWord_7980058).sum := by decide
  have hdescent : baseEnd_7980058 < baseStart_7980058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980089 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7980089 : Nat := 118140960795 + 7980089 * 2 ^ 59
def prefixEnd_7980089 : Nat := 4983230072969 + 3 ^ 40 * 7980089 * 2
def baseEnd_7980089 : Nat := 4097621322657133598787745

theorem tailTrace_7980089 : CollatzResearch.WordTrace tailWord_7980089 prefixEnd_7980089 4097621322657133598787745 := by
  unfold tailWord_7980089
  simp only [CollatzResearch.WordTrace]
  refine ⟨291057757186507918541039321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194038504791005279027359547 291057757186507918541039321)
  ·
    refine ⟨218293317889880938905779491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291057757186507918541039321 218293317889880938905779491)
    ·
      refine ⟨327439976834821408358669237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218293317889880938905779491 327439976834821408358669237)
      ·
        refine ⟨30697497828264507033625241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327439976834821408358669237 30697497828264507033625241)
        ·
          refine ⟨23023123371198380275218931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30697497828264507033625241 23023123371198380275218931)
          ·
            refine ⟨34534685056797570412828397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23023123371198380275218931 34534685056797570412828397)
            ·
              refine ⟨12950506896299088904810649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34534685056797570412828397 12950506896299088904810649)
              ·
                refine ⟨9712880172224316678607987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12950506896299088904810649 9712880172224316678607987)
                ·
                  refine ⟨14569320258336475017911981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712880172224316678607987 14569320258336475017911981)
                  ·
                    refine ⟨5463495096876178131716993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14569320258336475017911981 5463495096876178131716993)
                    ·
                      refine ⟨4097621322657133598787745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463495096876178131716993 4097621322657133598787745)
                      ·
                        rfl

theorem cell23_7980089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7980089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980089 prefixEnd_7980089 := by exact prefixLift 7980089
  have htrace : WordTrace (prefixWord ++ tailWord_7980089) baseStart_7980089 baseEnd_7980089 := by
    simpa [prefixWord, tailWord_7980089, baseEnd_7980089] using wordTrace_append hprefix tailTrace_7980089
  have hstable : (prefixWord ++ tailWord_7980089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980089).length < 2 ^ (prefixWord ++ tailWord_7980089).sum := by decide
  have hdescent : baseEnd_7980089 < baseStart_7980089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980135 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_7980135 : Nat := 118140960795 + 7980135 * 2 ^ 59
def prefixEnd_7980135 : Nat := 4983230072969 + 3 ^ 40 * 7980135 * 2
def baseEnd_7980135 : Nat := 4097644942767240418812533

theorem tailTrace_7980135 : CollatzResearch.WordTrace tailWord_7980135 prefixEnd_7980135 4097644942767240418812533 := by
  unfold tailWord_7980135
  simp only [CollatzResearch.WordTrace]
  refine ⟨291059434944341268397213859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194039623296227512264809239 291059434944341268397213859)
  ·
    refine ⟨436589152416511902595820789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291059434944341268397213859 436589152416511902595820789)
    ·
      refine ⟨40930233039047990868358199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436589152416511902595820789 40930233039047990868358199)
      ·
        refine ⟨61395349558571986302537299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40930233039047990868358199 61395349558571986302537299)
        ·
          refine ⟨92093024337857979453805949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61395349558571986302537299 92093024337857979453805949)
          ·
            refine ⟨34534884126696742295177231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92093024337857979453805949 34534884126696742295177231)
            ·
              refine ⟨51802326190045113442765847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34534884126696742295177231 51802326190045113442765847)
              ·
                refine ⟨77703489285067670164148771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51802326190045113442765847 77703489285067670164148771)
                ·
                  refine ⟨116555233927601505246223157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77703489285067670164148771 116555233927601505246223157)
                  ·
                    refine ⟨10927053180712641116833421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116555233927601505246223157 10927053180712641116833421)
                    ·
                      refine ⟨4097644942767240418812533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10927053180712641116833421 4097644942767240418812533)
                      ·
                        rfl

theorem cell23_7980135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_7980135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980135 prefixEnd_7980135 := by exact prefixLift 7980135
  have htrace : WordTrace (prefixWord ++ tailWord_7980135) baseStart_7980135 baseEnd_7980135 := by
    simpa [prefixWord, tailWord_7980135, baseEnd_7980135] using wordTrace_append hprefix tailTrace_7980135
  have hstable : (prefixWord ++ tailWord_7980135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980135).length < 2 ^ (prefixWord ++ tailWord_7980135).sum := by decide
  have hdescent : baseEnd_7980135 < baseStart_7980135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980136 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7980136 : Nat := 118140960795 + 7980136 * 2 ^ 59
def prefixEnd_7980136 : Nat := 4983230072969 + 3 ^ 40 * 7980136 * 2
def baseEnd_7980136 : Nat := 4097645456247894914900029

theorem tailTrace_7980136 : CollatzResearch.WordTrace tailWord_7980136 prefixEnd_7980136 4097645456247894914900029 := by
  unfold tailWord_7980136
  simp only [CollatzResearch.WordTrace]
  refine ⟨145529735708668822784000131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194039647611558430378666841 145529735708668822784000131)
  ·
    refine ⟨218294603563003234176000197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145529735708668822784000131 218294603563003234176000197)
    ·
      refine ⟨40930238168063106408000037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218294603563003234176000197 40930238168063106408000037)
      ·
        refine ⟨7674419656511832451500007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40930238168063106408000037 7674419656511832451500007)
        ·
          refine ⟨11511629484767748677250011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674419656511832451500007 11511629484767748677250011)
          ·
            refine ⟨17267444227151623015875017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11511629484767748677250011 17267444227151623015875017)
            ·
              refine ⟨12950583170363717261906263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17267444227151623015875017 12950583170363717261906263)
              ·
                refine ⟨19425874755545575892859395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950583170363717261906263 19425874755545575892859395)
                ·
                  refine ⟨29138812133318363839289093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19425874755545575892859395 29138812133318363839289093)
                  ·
                    refine ⟨5463527274997193219866705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29138812133318363839289093 5463527274997193219866705)
                    ·
                      refine ⟨4097645456247894914900029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463527274997193219866705 4097645456247894914900029)
                      ·
                        rfl

theorem cell23_7980136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7980136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980136 prefixEnd_7980136 := by exact prefixLift 7980136
  have htrace : WordTrace (prefixWord ++ tailWord_7980136) baseStart_7980136 baseEnd_7980136 := by
    simpa [prefixWord, tailWord_7980136, baseEnd_7980136] using wordTrace_append hprefix tailTrace_7980136
  have hstable : (prefixWord ++ tailWord_7980136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980136).length < 2 ^ (prefixWord ++ tailWord_7980136).sum := by decide
  have hdescent : baseEnd_7980136 < baseStart_7980136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980192 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2]
def baseStart_7980192 : Nat := 118140960795 + 7980192 * 2 ^ 59
def prefixEnd_7980192 : Nat := 4983230072969 + 3 ^ 40 * 7980192 * 2
def baseEnd_7980192 : Nat := 4097674211164546695799771

theorem tailTrace_7980192 : CollatzResearch.WordTrace tailWord_7980192 prefixEnd_7980192 4097674211164546695799771 := by
  unfold tailWord_7980192
  simp only [CollatzResearch.WordTrace]
  refine ⟨145530756952567383566019415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194041009270089844754692553 145530756952567383566019415)
  ·
    refine ⟨218296135428851075349029123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145530756952567383566019415 218296135428851075349029123)
    ·
      refine ⟨327444203143276613023543685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218296135428851075349029123 327444203143276613023543685)
      ·
        refine ⟨61395788089364364941914441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327444203143276613023543685 61395788089364364941914441)
        ·
          refine ⟨46046841067023273706435831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61395788089364364941914441 46046841067023273706435831)
          ·
            refine ⟨69070261600534910559653747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46046841067023273706435831 69070261600534910559653747)
            ·
              refine ⟨103605392400802365839480621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69070261600534910559653747 103605392400802365839480621)
              ·
                refine ⟨38852022150300887189805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103605392400802365839480621 38852022150300887189805233)
                ·
                  refine ⟨29139016612725665392353925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38852022150300887189805233 29139016612725665392353925)
                  ·
                    refine ⟨5463565614886062261066361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29139016612725665392353925 5463565614886062261066361)
                    ·
                      refine ⟨4097674211164546695799771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463565614886062261066361 4097674211164546695799771)
                      ·
                        rfl

theorem cell23_7980192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_7980192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980192 prefixEnd_7980192 := by exact prefixLift 7980192
  have htrace : WordTrace (prefixWord ++ tailWord_7980192) baseStart_7980192 baseEnd_7980192 := by
    simpa [prefixWord, tailWord_7980192, baseEnd_7980192] using wordTrace_append hprefix tailTrace_7980192
  have hstable : (prefixWord ++ tailWord_7980192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980192).length < 2 ^ (prefixWord ++ tailWord_7980192).sum := by decide
  have hdescent : baseEnd_7980192 < baseStart_7980192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980275 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 3, 6]
def baseStart_7980275 : Nat := 118140960795 + 7980275 * 2 ^ 59
def prefixEnd_7980275 : Nat := 4983230072969 + 3 ^ 40 * 7980275 * 2
def baseEnd_7980275 : Nat := 1365905610019623290353963

theorem tailTrace_7980275 : CollatzResearch.WordTrace tailWord_7980275 prefixEnd_7980275 1365905610019623290353963 := by
  unfold tailWord_7980275
  simp only [CollatzResearch.WordTrace]
  refine ⟨291064541163834072307310279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194043027442556048204873519 291064541163834072307310279)
  ·
    refine ⟨436596811745751108460965419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291064541163834072307310279 436596811745751108460965419)
    ·
      refine ⟨654895217618626662691448129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436596811745751108460965419 654895217618626662691448129)
      ·
        refine ⟨491171413213969997018586097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654895217618626662691448129 491171413213969997018586097)
        ·
          refine ⟨368378559910477497763939573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491171413213969997018586097 368378559910477497763939573)
          ·
            refine ⟨34535489991607265415369335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368378559910477497763939573 34535489991607265415369335)
            ·
              refine ⟨51803234987410898123054003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34535489991607265415369335 51803234987410898123054003)
              ·
                refine ⟨77704852481116347184581005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51803234987410898123054003 77704852481116347184581005)
                ·
                  refine ⟨29139319680418630194217877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77704852481116347184581005 29139319680418630194217877)
                  ·
                    refine ⟨1365905610019623290353963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29139319680418630194217877 1365905610019623290353963)
                    ·
                      rfl

theorem cell23_7980275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_7980275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980275 prefixEnd_7980275 := by exact prefixLift 7980275
  have htrace : WordTrace (prefixWord ++ tailWord_7980275) baseStart_7980275 baseEnd_7980275 := by
    simpa [prefixWord, tailWord_7980275, baseEnd_7980275] using wordTrace_append hprefix tailTrace_7980275
  have hstable : (prefixWord ++ tailWord_7980275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980275).length < 2 ^ (prefixWord ++ tailWord_7980275).sum := by decide
  have hdescent : baseEnd_7980275 < baseStart_7980275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980286 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7980286 : Nat := 118140960795 + 7980286 * 2 ^ 59
def prefixEnd_7980286 : Nat := 4983230072969 + 3 ^ 40 * 7980286 * 2
def baseEnd_7980286 : Nat := 4097722478346069328024339

theorem tailTrace_7980286 : CollatzResearch.WordTrace tailWord_7980286 prefixEnd_7980286 4097722478346069328024339 := by
  unfold tailWord_7980286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383117795849277648245089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194043294911196147457307141 36383117795849277648245089)
  ·
    refine ⟨27287338346886958236183817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36383117795849277648245089 27287338346886958236183817)
    ·
      refine ⟨20465503760165218677137863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27287338346886958236183817 20465503760165218677137863)
      ·
        refine ⟨30698255640247828015706795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20465503760165218677137863 30698255640247828015706795)
        ·
          refine ⟨46047383460371742023560193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30698255640247828015706795 46047383460371742023560193)
          ·
            refine ⟨34535537595278806517670145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46047383460371742023560193 34535537595278806517670145)
            ·
              refine ⟨25901653196459104888252609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34535537595278806517670145 25901653196459104888252609)
              ·
                refine ⟨19426239897344328666189457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25901653196459104888252609 19426239897344328666189457)
                ·
                  refine ⟨14569679923008246499642093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19426239897344328666189457 14569679923008246499642093)
                  ·
                    refine ⟨5463629971128092437365785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14569679923008246499642093 5463629971128092437365785)
                    ·
                      refine ⟨4097722478346069328024339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463629971128092437365785 4097722478346069328024339)
                      ·
                        rfl

theorem cell23_7980286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7980286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980286 prefixEnd_7980286 := by exact prefixLift 7980286
  have htrace : WordTrace (prefixWord ++ tailWord_7980286) baseStart_7980286 baseEnd_7980286 := by
    simpa [prefixWord, tailWord_7980286, baseEnd_7980286] using wordTrace_append hprefix tailTrace_7980286
  have hstable : (prefixWord ++ tailWord_7980286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980286).length < 2 ^ (prefixWord ++ tailWord_7980286).sum := by decide
  have hdescent : baseEnd_7980286 < baseStart_7980286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980312 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_7980312 : Nat := 118140960795 + 7980312 * 2 ^ 59
def prefixEnd_7980312 : Nat := 4983230072969 + 3 ^ 40 * 7980312 * 2
def baseEnd_7980312 : Nat := 4097735828843086226299219

theorem tailTrace_7980312 : CollatzResearch.WordTrace tailWord_7980312 prefixEnd_7980312 4097735828843086226299219 := by
  unfold tailWord_7980312
  simp only [CollatzResearch.WordTrace]
  refine ⟨145532945332350013813203595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194043927109800018417604793 145532945332350013813203595)
  ·
    refine ⟨218299417998525020719805393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145532945332350013813203595 218299417998525020719805393)
    ·
      refine ⟨163724563498893765539854045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218299417998525020719805393 163724563498893765539854045)
      ·
        refine ⟨61396711312085162077445267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163724563498893765539854045 61396711312085162077445267)
        ·
          refine ⟨92095066968127743116167901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61396711312085162077445267 92095066968127743116167901)
          ·
            refine ⟨34535650113047903668562963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92095066968127743116167901 34535650113047903668562963)
            ·
              refine ⟨51803475169571855502844445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34535650113047903668562963 51803475169571855502844445)
              ·
                refine ⟨19426303188589445813566667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51803475169571855502844445 19426303188589445813566667)
                ·
                  refine ⟨29139454782884168720350001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19426303188589445813566667 29139454782884168720350001)
                  ·
                    refine ⟨21854591087163126540262501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29139454782884168720350001 21854591087163126540262501)
                    ·
                      refine ⟨4097735828843086226299219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21854591087163126540262501 4097735828843086226299219)
                      ·
                        rfl

theorem cell23_7980312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_7980312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980312 prefixEnd_7980312 := by exact prefixLift 7980312
  have htrace : WordTrace (prefixWord ++ tailWord_7980312) baseStart_7980312 baseEnd_7980312 := by
    simpa [prefixWord, tailWord_7980312, baseEnd_7980312] using wordTrace_append hprefix tailTrace_7980312
  have hstable : (prefixWord ++ tailWord_7980312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980312).length < 2 ^ (prefixWord ++ tailWord_7980312).sum := by decide
  have hdescent : baseEnd_7980312 < baseStart_7980312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980333 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7980333 : Nat := 118140960795 + 7980333 * 2 ^ 59
def prefixEnd_7980333 : Nat := 4983230072969 + 3 ^ 40 * 7980333 * 2
def baseEnd_7980333 : Nat := 4097746611936830644136623

theorem tailTrace_7980333 : CollatzResearch.WordTrace tailWord_7980333 prefixEnd_7980333 4097746611936830644136623 := by
  unfold tailWord_7980333
  simp only [CollatzResearch.WordTrace]
  refine ⟨291066656597623948212921653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194044437731749298808614435 291066656597623948212921653)
  ·
    refine ⟨27287499056027245144961405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291066656597623948212921653 27287499056027245144961405)
    ·
      refine ⟨10232812146010216929360527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27287499056027245144961405 10232812146010216929360527)
      ·
        refine ⟨15349218219015325394040791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232812146010216929360527 15349218219015325394040791)
        ·
          refine ⟨23023827328522988091061187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15349218219015325394040791 23023827328522988091061187)
          ·
            refine ⟨34535740992784482136591781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23023827328522988091061187 34535740992784482136591781)
            ·
              refine ⟨6475451436147090400610959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34535740992784482136591781 6475451436147090400610959)
              ·
                refine ⟨9713177154220635600916439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475451436147090400610959 9713177154220635600916439)
                ·
                  refine ⟨14569765731330953401374659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713177154220635600916439 14569765731330953401374659)
                  ·
                    refine ⟨21854648596996430102061989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14569765731330953401374659 21854648596996430102061989)
                    ·
                      refine ⟨4097746611936830644136623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21854648596996430102061989 4097746611936830644136623)
                      ·
                        rfl

theorem cell23_7980333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7980333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980333 prefixEnd_7980333 := by exact prefixLift 7980333
  have htrace : WordTrace (prefixWord ++ tailWord_7980333) baseStart_7980333 baseEnd_7980333 := by
    simpa [prefixWord, tailWord_7980333, baseEnd_7980333] using wordTrace_append hprefix tailTrace_7980333
  have hstable : (prefixWord ++ tailWord_7980333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980333).length < 2 ^ (prefixWord ++ tailWord_7980333).sum := by decide
  have hdescent : baseEnd_7980333 < baseStart_7980333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980376 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_7980376 : Nat := 118140960795 + 7980376 * 2 ^ 59
def prefixEnd_7980376 : Nat := 4983230072969 + 3 ^ 40 * 7980376 * 2
def baseEnd_7980376 : Nat := 4097768691604973975898925

theorem tailTrace_7980376 : CollatzResearch.WordTrace tailWord_7980376 prefixEnd_7980376 4097768691604973975898925 := by
  unfold tailWord_7980376
  simp only [CollatzResearch.WordTrace]
  refine ⟨145534112468234083278368491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194045483290978777704491321 145534112468234083278368491)
  ·
    refine ⟨218301168702351124917552737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145534112468234083278368491 218301168702351124917552737)
    ·
      refine ⟨163725876526763343688164553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218301168702351124917552737 163725876526763343688164553)
      ·
        refine ⟨122794407395072507766123415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163725876526763343688164553 122794407395072507766123415)
        ·
          refine ⟨184191611092608761649185123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122794407395072507766123415 184191611092608761649185123)
          ·
            refine ⟨276287416638913142473777685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184191611092608761649185123 276287416638913142473777685)
            ·
              refine ⟨12950972654949053553458329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276287416638913142473777685 12950972654949053553458329)
              ·
                refine ⟨9713229491211790165093747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12950972654949053553458329 9713229491211790165093747)
                ·
                  refine ⟨14569844236817685247640621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713229491211790165093747 14569844236817685247640621)
                  ·
                    refine ⟨5463691588806631967865233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14569844236817685247640621 5463691588806631967865233)
                    ·
                      refine ⟨4097768691604973975898925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463691588806631967865233 4097768691604973975898925)
                      ·
                        rfl

theorem cell23_7980376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_7980376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980376 prefixEnd_7980376 := by exact prefixLift 7980376
  have htrace : WordTrace (prefixWord ++ tailWord_7980376) baseStart_7980376 baseEnd_7980376 := by
    simpa [prefixWord, tailWord_7980376, baseEnd_7980376] using wordTrace_append hprefix tailTrace_7980376
  have hstable : (prefixWord ++ tailWord_7980376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980376).length < 2 ^ (prefixWord ++ tailWord_7980376).sum := by decide
  have hdescent : baseEnd_7980376 < baseStart_7980376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980389 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_7980389 : Nat := 118140960795 + 7980389 * 2 ^ 59
def prefixEnd_7980389 : Nat := 4983230072969 + 3 ^ 40 * 7980389 * 2
def baseEnd_7980389 : Nat := 4097775366853482425036365

theorem tailTrace_7980389 : CollatzResearch.WordTrace tailWord_7980389 prefixEnd_7980389 4097775366853482425036365 := by
  unfold tailWord_7980389
  simp only [CollatzResearch.WordTrace]
  refine ⟨291068699085421069776960221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194045799390280713184640147 291068699085421069776960221)
  ·
    refine ⟨109150762157032901166360083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291068699085421069776960221 109150762157032901166360083)
    ·
      refine ⟨163726143235549351749540125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109150762157032901166360083 163726143235549351749540125)
      ·
        refine ⟨61397303713331006906077547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163726143235549351749540125 61397303713331006906077547)
        ·
          refine ⟨92095955569996510359116321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61397303713331006906077547 92095955569996510359116321)
          ·
            refine ⟨69071966677497382769337241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92095955569996510359116321 69071966677497382769337241)
            ·
              refine ⟨51803975008123037077002931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69071966677497382769337241 51803975008123037077002931)
              ·
                refine ⟨77705962512184555615504397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51803975008123037077002931 77705962512184555615504397)
                ·
                  refine ⟨29139735942069208355814149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77705962512184555615504397 29139735942069208355814149)
                  ·
                    refine ⟨5463700489137976566715153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29139735942069208355814149 5463700489137976566715153)
                    ·
                      refine ⟨4097775366853482425036365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463700489137976566715153 4097775366853482425036365)
                      ·
                        rfl

theorem cell23_7980389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_7980389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980389 prefixEnd_7980389 := by exact prefixLift 7980389
  have htrace : WordTrace (prefixWord ++ tailWord_7980389) baseStart_7980389 baseEnd_7980389 := by
    simpa [prefixWord, tailWord_7980389, baseEnd_7980389] using wordTrace_append hprefix tailTrace_7980389
  have hstable : (prefixWord ++ tailWord_7980389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980389).length < 2 ^ (prefixWord ++ tailWord_7980389).sum := by decide
  have hdescent : baseEnd_7980389 < baseStart_7980389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980417 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7980417 : Nat := 118140960795 + 7980417 * 2 ^ 59
def prefixEnd_7980417 : Nat := 4983230072969 + 3 ^ 40 * 7980417 * 2
def baseEnd_7980417 : Nat := 4097789744311808315486237

theorem tailTrace_7980417 : CollatzResearch.WordTrace tailWord_7980417 prefixEnd_7980417 4097789744311808315486237 := by
  unfold tailWord_7980417
  simp only [CollatzResearch.WordTrace]
  refine ⟨291069720329319630558979505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194046480219546420372653003 291069720329319630558979505)
  ·
    refine ⟨218302290246989722919234629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291069720329319630558979505 218302290246989722919234629)
    ·
      refine ⟨40931679421310573047356493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218302290246989722919234629 40931679421310573047356493)
      ·
        refine ⟨15349379782991464892758685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40931679421310573047356493 15349379782991464892758685)
        ·
          refine ⟨5756017418621799334784507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15349379782991464892758685 5756017418621799334784507)
          ·
            refine ⟨8634026127932699002176761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756017418621799334784507 8634026127932699002176761)
            ·
              refine ⟨6475519595949524251632571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8634026127932699002176761 6475519595949524251632571)
              ·
                refine ⟨9713279393924286377448857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475519595949524251632571 9713279393924286377448857)
                ·
                  refine ⟨7284959545443214783086643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9713279393924286377448857 7284959545443214783086643)
                  ·
                    refine ⟨10927439318164822174629965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7284959545443214783086643 10927439318164822174629965)
                    ·
                      refine ⟨4097789744311808315486237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10927439318164822174629965 4097789744311808315486237)
                      ·
                        rfl

theorem cell23_7980417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7980417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980417 prefixEnd_7980417 := by exact prefixLift 7980417
  have htrace : WordTrace (prefixWord ++ tailWord_7980417) baseStart_7980417 baseEnd_7980417 := by
    simpa [prefixWord, tailWord_7980417, baseEnd_7980417] using wordTrace_append hprefix tailTrace_7980417
  have hstable : (prefixWord ++ tailWord_7980417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980417).length < 2 ^ (prefixWord ++ tailWord_7980417).sum := by decide
  have hdescent : baseEnd_7980417 < baseStart_7980417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980423 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_7980423 : Nat := 118140960795 + 7980423 * 2 ^ 59
def prefixEnd_7980423 : Nat := 4983230072969 + 3 ^ 40 * 7980423 * 2
def baseEnd_7980423 : Nat := 4097792825195735292011209

theorem tailTrace_7980423 : CollatzResearch.WordTrace tailWord_7980423 prefixEnd_7980423 4097792825195735292011209 := by
  unfold tailWord_7980423
  simp only [CollatzResearch.WordTrace]
  refine ⟨291069939167297893583697923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194046626111531929055798615 291069939167297893583697923)
  ·
    refine ⟨436604908750946840375546885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291069939167297893583697923 436604908750946840375546885)
    ·
      refine ⟨81863420390802532570415041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436604908750946840375546885 81863420390802532570415041)
      ·
        refine ⟨61397565293101899427811281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81863420390802532570415041 61397565293101899427811281)
        ·
          refine ⟨46048173969826424570858461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61397565293101899427811281 46048173969826424570858461)
          ·
            refine ⟨17268065238684909214071923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46048173969826424570858461 17268065238684909214071923)
            ·
              refine ⟨25902097858027363821107885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17268065238684909214071923 25902097858027363821107885)
              ·
                refine ⟨9713286696760261432915457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25902097858027363821107885 9713286696760261432915457)
                ·
                  refine ⟨7284965022570196074686593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9713286696760261432915457 7284965022570196074686593)
                  ·
                    refine ⟨5463723766927647056014945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7284965022570196074686593 5463723766927647056014945)
                    ·
                      refine ⟨4097792825195735292011209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463723766927647056014945 4097792825195735292011209)
                      ·
                        rfl

theorem cell23_7980423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_7980423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980423 prefixEnd_7980423 := by exact prefixLift 7980423
  have htrace : WordTrace (prefixWord ++ tailWord_7980423) baseStart_7980423 baseEnd_7980423 := by
    simpa [prefixWord, tailWord_7980423, baseEnd_7980423] using wordTrace_append hprefix tailTrace_7980423
  have hstable : (prefixWord ++ tailWord_7980423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980423).length < 2 ^ (prefixWord ++ tailWord_7980423).sum := by decide
  have hdescent : baseEnd_7980423 < baseStart_7980423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980469 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7980469 : Nat := 118140960795 + 7980469 * 2 ^ 59
def prefixEnd_7980469 : Nat := 4983230072969 + 3 ^ 40 * 7980469 * 2
def baseEnd_7980469 : Nat := 4097816445305842112035997

theorem tailTrace_7980469 : CollatzResearch.WordTrace tailWord_7980469 prefixEnd_7980469 4097816445305842112035997 := by
  unfold tailWord_7980469
  simp only [CollatzResearch.WordTrace]
  refine ⟨291071616925131243439872461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194047744616754162293248307 291071616925131243439872461)
  ·
    refine ⟨109151856346924216289952173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291071616925131243439872461 109151856346924216289952173)
    ·
      refine ⟨40931946130096581108732065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109151856346924216289952173 40931946130096581108732065)
      ·
        refine ⟨30698959597572435831549049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40931946130096581108732065 30698959597572435831549049)
        ·
          refine ⟨23024219698179326873661787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30698959597572435831549049 23024219698179326873661787)
          ·
            refine ⟨34536329547268990310492681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23024219698179326873661787 34536329547268990310492681)
            ·
              refine ⟨25902247160451742732869511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34536329547268990310492681 25902247160451742732869511)
              ·
                refine ⟨38853370740677614099304267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25902247160451742732869511 38853370740677614099304267)
                ·
                  refine ⟨58280056111016421148956401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38853370740677614099304267 58280056111016421148956401)
                  ·
                    refine ⟨43710042083262315861717301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58280056111016421148956401 43710042083262315861717301)
                    ·
                      refine ⟨4097816445305842112035997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43710042083262315861717301 4097816445305842112035997)
                      ·
                        rfl

theorem cell23_7980469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7980469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980469 prefixEnd_7980469 := by exact prefixLift 7980469
  have htrace : WordTrace (prefixWord ++ tailWord_7980469) baseStart_7980469 baseEnd_7980469 := by
    simpa [prefixWord, tailWord_7980469, baseEnd_7980469] using wordTrace_append hprefix tailTrace_7980469
  have hstable : (prefixWord ++ tailWord_7980469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980469).length < 2 ^ (prefixWord ++ tailWord_7980469).sum := by decide
  have hdescent : baseEnd_7980469 < baseStart_7980469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980509 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7980509 : Nat := 118140960795 + 7980509 * 2 ^ 59
def prefixEnd_7980509 : Nat := 4983230072969 + 3 ^ 40 * 7980509 * 2
def baseEnd_7980509 : Nat := 4097836984532021955535813

theorem tailTrace_7980509 : CollatzResearch.WordTrace tailWord_7980509 prefixEnd_7980509 4097836984532021955535813 := by
  unfold tailWord_7980509
  simp only [CollatzResearch.WordTrace]
  refine ⟨291073075844986330271328581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194048717229990886847552387 291073075844986330271328581)
  ·
    refine ⟨54576201720934936925874109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291073075844986330271328581 54576201720934936925874109)
    ·
      refine ⟨20466075645350601347202791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54576201720934936925874109 20466075645350601347202791)
      ·
        refine ⟨30699113468025902020804187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466075645350601347202791 30699113468025902020804187)
        ·
          refine ⟨46048670202038853031206281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699113468025902020804187 46048670202038853031206281)
          ·
            refine ⟨34536502651529139773404711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46048670202038853031206281 34536502651529139773404711)
            ·
              refine ⟨51804753977293709660107067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34536502651529139773404711 51804753977293709660107067)
              ·
                refine ⟨77707130965940564490160601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51804753977293709660107067 77707130965940564490160601)
                ·
                  refine ⟨58280348224455423367620451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77707130965940564490160601 58280348224455423367620451)
                  ·
                    refine ⟨87420522336683135051430677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58280348224455423367620451 87420522336683135051430677)
                    ·
                      refine ⟨4097836984532021955535813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87420522336683135051430677 4097836984532021955535813)
                      ·
                        rfl

theorem cell23_7980509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7980509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980509 prefixEnd_7980509 := by exact prefixLift 7980509
  have htrace : WordTrace (prefixWord ++ tailWord_7980509) baseStart_7980509 baseEnd_7980509 := by
    simpa [prefixWord, tailWord_7980509, baseEnd_7980509] using wordTrace_append hprefix tailTrace_7980509
  have hstable : (prefixWord ++ tailWord_7980509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980509).length < 2 ^ (prefixWord ++ tailWord_7980509).sum := by decide
  have hdescent : baseEnd_7980509 < baseStart_7980509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980519 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 8]
def baseStart_7980519 : Nat := 118140960795 + 7980519 * 2 ^ 59
def prefixEnd_7980519 : Nat := 4983230072969 + 3 ^ 40 * 7980519 * 2
def baseEnd_7980519 : Nat := 455315791037618546267863

theorem tailTrace_7980519 : CollatzResearch.WordTrace tailWord_7980519 prefixEnd_7980519 455315791037618546267863 := by
  unfold tailWord_7980519
  simp only [CollatzResearch.WordTrace]
  refine ⟨291073440574950101979192611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194048960383300067986128407 291073440574950101979192611)
  ·
    refine ⟨436610160862425152968788917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291073440574950101979192611 436610160862425152968788917)
    ·
      refine ⟨40932202580852358090823961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436610160862425152968788917 40932202580852358090823961)
      ·
        refine ⟨30699151935639268568117971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40932202580852358090823961 30699151935639268568117971)
        ·
          refine ⟨46048727903458902852176957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699151935639268568117971 46048727903458902852176957)
          ·
            refine ⟨17268272963797088569566359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46048727903458902852176957 17268272963797088569566359)
            ·
              refine ⟨25902409445695632854349539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17268272963797088569566359 25902409445695632854349539)
              ·
                refine ⟨38853614168543449281524309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25902409445695632854349539 38853614168543449281524309)
                ·
                  refine ⟨455315791037618546267863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38853614168543449281524309 455315791037618546267863)
                  ·
                    rfl

theorem cell23_7980519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 8].length) (baseStart_7980519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980519 prefixEnd_7980519 := by exact prefixLift 7980519
  have htrace : WordTrace (prefixWord ++ tailWord_7980519) baseStart_7980519 baseEnd_7980519 := by
    simpa [prefixWord, tailWord_7980519, baseEnd_7980519] using wordTrace_append hprefix tailTrace_7980519
  have hstable : (prefixWord ++ tailWord_7980519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980519).length < 2 ^ (prefixWord ++ tailWord_7980519).sum := by decide
  have hdescent : baseEnd_7980519 < baseStart_7980519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980536 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 6]
def baseStart_7980536 : Nat := 118140960795 + 7980536 * 2 ^ 59
def prefixEnd_7980536 : Nat := 4983230072969 + 3 ^ 40 * 7980536 * 2
def baseEnd_7980536 : Nat := 455316760945521483322021

theorem tailTrace_7980536 : CollatzResearch.WordTrace tailWord_7980536 prefixEnd_7980536 455316760945521483322021 := by
  unfold tailWord_7980536
  simp only [CollatzResearch.WordTrace]
  refine ⟨145537030307944256941280731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194049373743925675921707641 145537030307944256941280731)
  ·
    refine ⟨218305545461916385411921097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145537030307944256941280731 218305545461916385411921097)
    ·
      refine ⟨163729159096437289058940823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218305545461916385411921097 163729159096437289058940823)
      ·
        refine ⟨245593738644655933588411235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163729159096437289058940823 245593738644655933588411235)
        ·
          refine ⟨368390607966983900382616853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245593738644655933588411235 368390607966983900382616853)
          ·
            refine ⟨17268309748452370330435165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368390607966983900382616853 17268309748452370330435165)
            ·
              refine ⟨6475616155669638873913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17268309748452370330435165 6475616155669638873913187)
              ·
                refine ⟨9713424233504458310869781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475616155669638873913187 9713424233504458310869781)
                ·
                  refine ⟨455316760945521483322021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9713424233504458310869781 455316760945521483322021)
                  ·
                    rfl

theorem cell23_7980536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 6].length) (baseStart_7980536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980536 prefixEnd_7980536 := by exact prefixLift 7980536
  have htrace : WordTrace (prefixWord ++ tailWord_7980536) baseStart_7980536 baseEnd_7980536 := by
    simpa [prefixWord, tailWord_7980536, baseEnd_7980536] using wordTrace_append hprefix tailTrace_7980536
  have hstable : (prefixWord ++ tailWord_7980536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980536).length < 2 ^ (prefixWord ++ tailWord_7980536).sum := by decide
  have hdescent : baseEnd_7980536 < baseStart_7980536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980573 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_7980573 : Nat := 118140960795 + 7980573 * 2 ^ 59
def prefixEnd_7980573 : Nat := 4983230072969 + 3 ^ 40 * 7980573 * 2
def baseEnd_7980573 : Nat := 4097869847293909705135519

theorem tailTrace_7980573 : CollatzResearch.WordTrace tailWord_7980573 prefixEnd_7980573 4097869847293909705135519 := by
  unfold tailWord_7980573
  simp only [CollatzResearch.WordTrace]
  refine ⟨291075410116754469201658373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194050273411169646134438915 291075410116754469201658373)
  ·
    refine ⟨54576639396891462975310945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291075410116754469201658373 54576639396891462975310945)
    ·
      refine ⟨40932479547668597231483209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54576639396891462975310945 40932479547668597231483209)
      ·
        refine ⟨30699359660751447923612407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40932479547668597231483209 30699359660751447923612407)
        ·
          refine ⟨46049039491127171885418611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699359660751447923612407 46049039491127171885418611)
          ·
            refine ⟨69073559236690757828127917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46049039491127171885418611 69073559236690757828127917)
            ·
              refine ⟨25902584713759034185547969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69073559236690757828127917 25902584713759034185547969)
              ·
                refine ⟨19426938535319275639160977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25902584713759034185547969 19426938535319275639160977)
                ·
                  refine ⟨14570203901489456729370733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19426938535319275639160977 14570203901489456729370733)
                  ·
                    refine ⟨5463826463058546273514025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14570203901489456729370733 5463826463058546273514025)
                    ·
                      refine ⟨4097869847293909705135519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463826463058546273514025 4097869847293909705135519)
                      ·
                        rfl

theorem cell23_7980573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_7980573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980573 prefixEnd_7980573 := by exact prefixLift 7980573
  have htrace : WordTrace (prefixWord ++ tailWord_7980573) baseStart_7980573 baseEnd_7980573 := by
    simpa [prefixWord, tailWord_7980573, baseEnd_7980573] using wordTrace_append hprefix tailTrace_7980573
  have hstable : (prefixWord ++ tailWord_7980573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980573).length < 2 ^ (prefixWord ++ tailWord_7980573).sum := by decide
  have hdescent : baseEnd_7980573 < baseStart_7980573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980574 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7980574 : Nat := 118140960795 + 7980574 * 2 ^ 59
def prefixEnd_7980574 : Nat := 4983230072969 + 3 ^ 40 * 7980574 * 2
def baseEnd_7980574 : Nat := 1365956786924854733741005

theorem tailTrace_7980574 : CollatzResearch.WordTrace tailWord_7980574 prefixEnd_7980574 1365956786924854733741005 := by
  unfold tailWord_7980574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384430823718855796555597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194050297726500564248296517 36384430823718855796555597)
  ·
    refine ⟨13644161558894570923708349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36384430823718855796555597 13644161558894570923708349)
    ·
      refine ⟨5116560584585464096390631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13644161558894570923708349 5116560584585464096390631)
      ·
        refine ⟨7674840876878196144585947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116560584585464096390631 7674840876878196144585947)
        ·
          refine ⟨11512261315317294216878921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674840876878196144585947 11512261315317294216878921)
          ·
            refine ⟨8634195986487970662659191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11512261315317294216878921 8634195986487970662659191)
            ·
              refine ⟨12951293979731955993988787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634195986487970662659191 12951293979731955993988787)
              ·
                refine ⟨19426940969597933990983181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951293979731955993988787 19426940969597933990983181)
                ·
                  refine ⟨7285102863599225246618693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19426940969597933990983181 7285102863599225246618693)
                  ·
                    refine ⟨1365956786924854733741005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7285102863599225246618693 1365956786924854733741005)
                    ·
                      rfl

theorem cell23_7980574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7980574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980574 prefixEnd_7980574 := by exact prefixLift 7980574
  have htrace : WordTrace (prefixWord ++ tailWord_7980574) baseStart_7980574 baseEnd_7980574 := by
    simpa [prefixWord, tailWord_7980574, baseEnd_7980574] using wordTrace_append hprefix tailTrace_7980574
  have hstable : (prefixWord ++ tailWord_7980574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980574).length < 2 ^ (prefixWord ++ tailWord_7980574).sum := by decide
  have hdescent : baseEnd_7980574 < baseStart_7980574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980586 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7980586 : Nat := 118140960795 + 7980586 * 2 ^ 59
def prefixEnd_7980586 : Nat := 4983230072969 + 3 ^ 40 * 7980586 * 2
def baseEnd_7980586 : Nat := 4097876522542418154272959

theorem tailTrace_7980586 : CollatzResearch.WordTrace tailWord_7980586 prefixEnd_7980586 4097876522542418154272959 := by
  unfold tailWord_7980586
  simp only [CollatzResearch.WordTrace]
  refine ⟨72768971066426843105470403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194050589510471581614587741 72768971066426843105470403)
  ·
    refine ⟨109153456599640264658205605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72768971066426843105470403 109153456599640264658205605)
    ·
      refine ⟨20466273112432549623413551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109153456599640264658205605 20466273112432549623413551)
      ·
        refine ⟨30699409668648824435120327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466273112432549623413551 30699409668648824435120327)
        ·
          refine ⟨46049114502973236652680491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699409668648824435120327 46049114502973236652680491)
          ·
            refine ⟨69073671754459854979020737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46049114502973236652680491 69073671754459854979020737)
            ·
              refine ⟨51805253815844891234265553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69073671754459854979020737 51805253815844891234265553)
              ·
                refine ⟨38853940361883668425699165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51805253815844891234265553 38853940361883668425699165)
                ·
                  refine ⟨14570227635706375659637187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38853940361883668425699165 14570227635706375659637187)
                  ·
                    refine ⟨21855341453559563489455781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14570227635706375659637187 21855341453559563489455781)
                    ·
                      refine ⟨4097876522542418154272959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21855341453559563489455781 4097876522542418154272959)
                      ·
                        rfl

theorem cell23_7980586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7980586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980586 prefixEnd_7980586 := by exact prefixLift 7980586
  have htrace : WordTrace (prefixWord ++ tailWord_7980586) baseStart_7980586 baseEnd_7980586 := by
    simpa [prefixWord, tailWord_7980586, baseEnd_7980586] using wordTrace_append hprefix tailTrace_7980586
  have hstable : (prefixWord ++ tailWord_7980586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980586).length < 2 ^ (prefixWord ++ tailWord_7980586).sum := by decide
  have hdescent : baseEnd_7980586 < baseStart_7980586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980599 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_7980599 : Nat := 118140960795 + 7980599 * 2 ^ 59
def prefixEnd_7980599 : Nat := 4983230072969 + 3 ^ 40 * 7980599 * 2
def baseEnd_7980599 : Nat := 4097883197790926603410399

theorem tailTrace_7980599 : CollatzResearch.WordTrace tailWord_7980599 prefixEnd_7980599 4097883197790926603410399 := by
  unfold tailWord_7980599
  simp only [CollatzResearch.WordTrace]
  refine ⟨291076358414660275642104851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194050905609773517094736567 291076358414660275642104851)
  ·
    refine ⟨436614537621990413463157277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291076358414660275642104851 436614537621990413463157277)
    ·
      refine ⟨163730451608246405048683979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436614537621990413463157277 163730451608246405048683979)
      ·
        refine ⟨245595677412369607573025969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163730451608246405048683979 245595677412369607573025969)
        ·
          refine ⟨184196758059277205679769477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245595677412369607573025969 184196758059277205679769477)
          ·
            refine ⟨34536892136114476064956777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184196758059277205679769477 34536892136114476064956777)
            ·
              refine ⟨25902669102085857048717583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34536892136114476064956777 25902669102085857048717583)
              ·
                refine ⟨38854003653128785573076375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25902669102085857048717583 38854003653128785573076375)
                ·
                  refine ⟨58281005479693178359614563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38854003653128785573076375 58281005479693178359614563)
                  ·
                    refine ⟨87421508219539767539421845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58281005479693178359614563 87421508219539767539421845)
                    ·
                      refine ⟨4097883197790926603410399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87421508219539767539421845 4097883197790926603410399)
                      ·
                        rfl

theorem cell23_7980599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_7980599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980599 prefixEnd_7980599 := by exact prefixLift 7980599
  have htrace : WordTrace (prefixWord ++ tailWord_7980599) baseStart_7980599 baseEnd_7980599 := by
    simpa [prefixWord, tailWord_7980599, baseEnd_7980599] using wordTrace_append hprefix tailTrace_7980599
  have hstable : (prefixWord ++ tailWord_7980599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980599).length < 2 ^ (prefixWord ++ tailWord_7980599).sum := by decide
  have hdescent : baseEnd_7980599 < baseStart_7980599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980609 : List Nat := [1, 2, 5, 1, 1, 1, 1, 11]
def baseStart_7980609 : Nat := 118140960795 + 7980609 * 2 ^ 59
def prefixEnd_7980609 : Nat := 4983230072969 + 3 ^ 40 * 7980609 * 2
def baseEnd_7980609 : Nat := 151773641948054502380939

theorem tailTrace_7980609 : CollatzResearch.WordTrace tailWord_7980609 prefixEnd_7980609 151773641948054502380939 := by
  unfold tailWord_7980609
  simp only [CollatzResearch.WordTrace]
  refine ⟨291076723144624047349968881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194051148763082698233312587 291076723144624047349968881)
  ·
    refine ⟨218307542358468035512476661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291076723144624047349968881 218307542358468035512476661)
    ·
      refine ⟨20466332096106378329294687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218307542358468035512476661 20466332096106378329294687)
      ·
        refine ⟨30699498144159567493942031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466332096106378329294687 30699498144159567493942031)
        ·
          refine ⟨46049247216239351240913047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699498144159567493942031 46049247216239351240913047)
          ·
            refine ⟨69073870824359026861369571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46049247216239351240913047 69073870824359026861369571)
            ·
              refine ⟨103610806236538540292054357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69073870824359026861369571 103610806236538540292054357)
              ·
                refine ⟨151773641948054502380939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103610806236538540292054357 151773641948054502380939)
                ·
                  rfl

theorem cell23_7980609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 11].length) (baseStart_7980609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980609 prefixEnd_7980609 := by exact prefixLift 7980609
  have htrace : WordTrace (prefixWord ++ tailWord_7980609) baseStart_7980609 baseEnd_7980609 := by
    simpa [prefixWord, tailWord_7980609, baseEnd_7980609] using wordTrace_append hprefix tailTrace_7980609
  have hstable : (prefixWord ++ tailWord_7980609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980609).length < 2 ^ (prefixWord ++ tailWord_7980609).sum := by decide
  have hdescent : baseEnd_7980609 < baseStart_7980609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980663 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_7980663 : Nat := 118140960795 + 7980663 * 2 ^ 59
def prefixEnd_7980663 : Nat := 4983230072969 + 3 ^ 40 * 7980663 * 2
def baseEnd_7980663 : Nat := 4097916060552814353010105

theorem tailTrace_7980663 : CollatzResearch.WordTrace tailWord_7980663 prefixEnd_7980663 4097916060552814353010105 := by
  unfold tailWord_7980663
  simp only [CollatzResearch.WordTrace]
  refine ⟨291078692686428414572434643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194052461790952276381623095 291078692686428414572434643)
  ·
    refine ⟨436618039029642621858651965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291078692686428414572434643 436618039029642621858651965)
    ·
      refine ⟨163731764636115983196994487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436618039029642621858651965 163731764636115983196994487)
      ·
        refine ⟨245597646954173974795491731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163731764636115983196994487 245597646954173974795491731)
        ·
          refine ⟨368396470431260962193237597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245597646954173974795491731 368396470431260962193237597)
          ·
            refine ⟨138148676411722860822464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368396470431260962193237597 138148676411722860822464099)
            ·
              refine ⟨207223014617584291233696149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138148676411722860822464099 207223014617584291233696149)
              ·
                refine ⟨9713578810199263651579507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207223014617584291233696149 9713578810199263651579507)
                ·
                  refine ⟨14570368215298895477369261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713578810199263651579507 14570368215298895477369261)
                  ·
                    refine ⟨5463888080737085804013473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14570368215298895477369261 5463888080737085804013473)
                    ·
                      refine ⟨4097916060552814353010105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5463888080737085804013473 4097916060552814353010105)
                      ·
                        rfl

theorem cell23_7980663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_7980663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980663 prefixEnd_7980663 := by exact prefixLift 7980663
  have htrace : WordTrace (prefixWord ++ tailWord_7980663) baseStart_7980663 baseEnd_7980663 := by
    simpa [prefixWord, tailWord_7980663, baseEnd_7980663] using wordTrace_append hprefix tailTrace_7980663
  have hstable : (prefixWord ++ tailWord_7980663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980663).length < 2 ^ (prefixWord ++ tailWord_7980663).sum := by decide
  have hdescent : baseEnd_7980663 < baseStart_7980663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980686 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_7980686 : Nat := 118140960795 + 7980686 * 2 ^ 59
def prefixEnd_7980686 : Nat := 4983230072969 + 3 ^ 40 * 7980686 * 2
def baseEnd_7980686 : Nat := 1365975956869289254340833

theorem tailTrace_7980686 : CollatzResearch.WordTrace tailWord_7980686 prefixEnd_7980686 1365975956869289254340833 := by
  unfold tailWord_7980686
  simp only [CollatzResearch.WordTrace]
  refine ⟨36384941445668136187565239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194053021043563393000347941 36384941445668136187565239)
  ·
    refine ⟨54577412168502204281347859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36384941445668136187565239 54577412168502204281347859)
    ·
      refine ⟨81866118252753306422021789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54577412168502204281347859 81866118252753306422021789)
      ·
        refine ⟨30699794344782489908258171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81866118252753306422021789 30699794344782489908258171)
        ·
          refine ⟨46049691517173734862387257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699794344782489908258171 46049691517173734862387257)
          ·
            refine ⟨34537268637880301146790443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46049691517173734862387257 34537268637880301146790443)
            ·
              refine ⟨51805902956820451720185665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34537268637880301146790443 51805902956820451720185665)
              ·
                refine ⟨38854427217615338790139249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51805902956820451720185665 38854427217615338790139249)
                ·
                  refine ⟨29140820413211504092604437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38854427217615338790139249 29140820413211504092604437)
                  ·
                    refine ⟨1365975956869289254340833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29140820413211504092604437 1365975956869289254340833)
                    ·
                      rfl

theorem cell23_7980686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_7980686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980686 prefixEnd_7980686 := by exact prefixLift 7980686
  have htrace : WordTrace (prefixWord ++ tailWord_7980686) baseStart_7980686 baseEnd_7980686 := by
    simpa [prefixWord, tailWord_7980686, baseEnd_7980686] using wordTrace_append hprefix tailTrace_7980686
  have hstable : (prefixWord ++ tailWord_7980686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980686).length < 2 ^ (prefixWord ++ tailWord_7980686).sum := by decide
  have hdescent : baseEnd_7980686 < baseStart_7980686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980739 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_7980739 : Nat := 118140960795 + 7980739 * 2 ^ 59
def prefixEnd_7980739 : Nat := 4983230072969 + 3 ^ 40 * 7980739 * 2
def baseEnd_7980739 : Nat := 4097955085082556055659755

theorem tailTrace_7980739 : CollatzResearch.WordTrace tailWord_7980739 prefixEnd_7980739 4097955085082556055659755 := by
  unfold tailWord_7980739
  simp only [CollatzResearch.WordTrace]
  refine ⟨291081464634153079552201271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194054309756102053034800847 291081464634153079552201271)
  ·
    refine ⟨436622196951229619328301907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291081464634153079552201271 436622196951229619328301907)
    ·
      refine ⟨654933295426844428992452861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436622196951229619328301907 654933295426844428992452861)
      ·
        refine ⟨245599985785066660872169823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654933295426844428992452861 245599985785066660872169823)
        ·
          refine ⟨368399978677599991308254735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245599985785066660872169823 368399978677599991308254735)
          ·
            refine ⟨552599968016399986962382103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368399978677599991308254735 552599968016399986962382103)
            ·
              refine ⟨828899952024599980443573155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552599968016399986962382103 828899952024599980443573155)
              ·
                refine ⟨1243349928036899970665359733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828899952024599980443573155 1243349928036899970665359733)
                ·
                  refine ⟨116564055753459372249877475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1243349928036899970665359733 116564055753459372249877475)
                  ·
                    refine ⟨174846083630189058374816213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116564055753459372249877475 174846083630189058374816213)
                    ·
                      refine ⟨4097955085082556055659755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174846083630189058374816213 4097955085082556055659755)
                      ·
                        rfl

theorem cell23_7980739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_7980739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980739 prefixEnd_7980739 := by exact prefixLift 7980739
  have htrace : WordTrace (prefixWord ++ tailWord_7980739) baseStart_7980739 baseEnd_7980739 := by
    simpa [prefixWord, tailWord_7980739, baseEnd_7980739] using wordTrace_append hprefix tailTrace_7980739
  have hstable : (prefixWord ++ tailWord_7980739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980739).length < 2 ^ (prefixWord ++ tailWord_7980739).sum := by decide
  have hdescent : baseEnd_7980739 < baseStart_7980739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980750 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_7980750 : Nat := 118140960795 + 7980750 * 2 ^ 59
def prefixEnd_7980750 : Nat := 4983230072969 + 3 ^ 40 * 7980750 * 2
def baseEnd_7980750 : Nat := 455328970374417279180245

theorem tailTrace_7980750 : CollatzResearch.WordTrace tailWord_7980750 prefixEnd_7980750 455328970374417279180245 := by
  unfold tailWord_7980750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36385233229639153553856463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194054577224742152287234469 36385233229639153553856463)
  ·
    refine ⟨54577849844458730330784695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36385233229639153553856463 54577849844458730330784695)
    ·
      refine ⟨81866774766688095496177043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54577849844458730330784695 81866774766688095496177043)
      ·
        refine ⟨122800162150032143244265565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81866774766688095496177043 122800162150032143244265565)
        ·
          refine ⟨46050060806262053716599587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122800162150032143244265565 46050060806262053716599587)
          ·
            refine ⟨69075091209393080574899381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46050060806262053716599587 69075091209393080574899381)
            ·
              refine ⟨6475789800880601303896817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69075091209393080574899381 6475789800880601303896817)
              ·
                refine ⟨4856842350660450977922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475789800880601303896817 4856842350660450977922613)
                ·
                  refine ⟨455328970374417279180245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4856842350660450977922613 455328970374417279180245)
                  ·
                    rfl

theorem cell23_7980750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_7980750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980750 prefixEnd_7980750 := by exact prefixLift 7980750
  have htrace : WordTrace (prefixWord ++ tailWord_7980750) baseStart_7980750 baseEnd_7980750 := by
    simpa [prefixWord, tailWord_7980750, baseEnd_7980750] using wordTrace_append hprefix tailTrace_7980750
  have hstable : (prefixWord ++ tailWord_7980750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980750).length < 2 ^ (prefixWord ++ tailWord_7980750).sum := by decide
  have hdescent : baseEnd_7980750 < baseStart_7980750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980783 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_7980783 : Nat := 118140960795 + 7980783 * 2 ^ 59
def prefixEnd_7980783 : Nat := 4983230072969 + 3 ^ 40 * 7980783 * 2
def baseEnd_7980783 : Nat := 4097977678231353883509553

theorem tailTrace_7980783 : CollatzResearch.WordTrace tailWord_7980783 prefixEnd_7980783 4097977678231353883509553 := by
  unfold tailWord_7980783
  simp only [CollatzResearch.WordTrace]
  refine ⟨291083069445993675066803003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194055379630662450044535335 291083069445993675066803003)
  ·
    refine ⟨436624604168990512600204505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291083069445993675066803003 436624604168990512600204505)
    ·
      refine ⟨327468453126742884450153379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436624604168990512600204505 327468453126742884450153379)
      ·
        refine ⟨491202679690114326675230069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327468453126742884450153379 491202679690114326675230069)
        ·
          refine ⟨46050251220948218125802819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491202679690114326675230069 46050251220948218125802819)
          ·
            refine ⟨69075376831422327188704229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46050251220948218125802819 69075376831422327188704229)
            ·
              refine ⟨12951633155891686347882043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69075376831422327188704229 12951633155891686347882043)
              ·
                refine ⟨19427449733837529521823065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951633155891686347882043 19427449733837529521823065)
                ·
                  refine ⟨14570587300378147141367299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19427449733837529521823065 14570587300378147141367299)
                  ·
                    refine ⟨21855880950567220712050949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14570587300378147141367299 21855880950567220712050949)
                    ·
                      refine ⟨4097977678231353883509553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21855880950567220712050949 4097977678231353883509553)
                      ·
                        rfl

theorem cell23_7980783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_7980783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980783 prefixEnd_7980783 := by exact prefixLift 7980783
  have htrace : WordTrace (prefixWord ++ tailWord_7980783) baseStart_7980783 baseEnd_7980783 := by
    simpa [prefixWord, tailWord_7980783, baseEnd_7980783] using wordTrace_append hprefix tailTrace_7980783
  have hstable : (prefixWord ++ tailWord_7980783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980783).length < 2 ^ (prefixWord ++ tailWord_7980783).sum := by decide
  have hdescent : baseEnd_7980783 < baseStart_7980783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980796 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_7980796 : Nat := 118140960795 + 7980796 * 2 ^ 59
def prefixEnd_7980796 : Nat := 4983230072969 + 3 ^ 40 * 7980796 * 2
def baseEnd_7980796 : Nat := 4097984353479862332646993

theorem tailTrace_7980796 : CollatzResearch.WordTrace tailWord_7980796 prefixEnd_7980796 4097984353479862332646993 := by
  unfold tailWord_7980796
  simp only [CollatzResearch.WordTrace]
  refine ⟨145541771797473289143513121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194055695729964385524684161 145541771797473289143513121)
  ·
    refine ⟨109156328848104966857634841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145541771797473289143513121 109156328848104966857634841)
    ·
      refine ⟨81867246636078725143226131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109156328848104966857634841 81867246636078725143226131)
      ·
        refine ⟨122800869954118087714839197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81867246636078725143226131 122800869954118087714839197)
        ·
          refine ⟨46050326232794282893064699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122800869954118087714839197 46050326232794282893064699)
          ·
            refine ⟨69075489349191424339597049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46050326232794282893064699 69075489349191424339597049)
            ·
              refine ⟨51806617011893568254697787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69075489349191424339597049 51806617011893568254697787)
              ·
                refine ⟨77709925517840352382046681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51806617011893568254697787 77709925517840352382046681)
                ·
                  refine ⟨58282444138380264286535011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77709925517840352382046681 58282444138380264286535011)
                  ·
                    refine ⟨87423666207570396429802517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58282444138380264286535011 87423666207570396429802517)
                    ·
                      refine ⟨4097984353479862332646993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87423666207570396429802517 4097984353479862332646993)
                      ·
                        rfl

theorem cell23_7980796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_7980796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980796 prefixEnd_7980796 := by exact prefixLift 7980796
  have htrace : WordTrace (prefixWord ++ tailWord_7980796) baseStart_7980796 baseEnd_7980796 := by
    simpa [prefixWord, tailWord_7980796, baseEnd_7980796] using wordTrace_append hprefix tailTrace_7980796
  have hstable : (prefixWord ++ tailWord_7980796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980796).length < 2 ^ (prefixWord ++ tailWord_7980796).sum := by decide
  have hdescent : baseEnd_7980796 < baseStart_7980796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980803 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3]
def baseStart_7980803 : Nat := 118140960795 + 7980803 * 2 ^ 59
def prefixEnd_7980803 : Nat := 4983230072969 + 3 ^ 40 * 7980803 * 2
def baseEnd_7980803 : Nat := 4097987947844443805259461

theorem tailTrace_7980803 : CollatzResearch.WordTrace tailWord_7980803 prefixEnd_7980803 4097987947844443805259461 := by
  unfold tailWord_7980803
  simp only [CollatzResearch.WordTrace]
  refine ⟨291083798905921218482531063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194055865937280812321687375 291083798905921218482531063)
  ·
    refine ⟨436625698358881827723796595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291083798905921218482531063 436625698358881827723796595)
    ·
      refine ⟨654938547538322741585694893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436625698358881827723796595 654938547538322741585694893)
      ·
        refine ⟨245601955326871028094635585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654938547538322741585694893 245601955326871028094635585)
        ·
          refine ⟨184201466495153271070976689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245601955326871028094635585 184201466495153271070976689)
          ·
            refine ⟨138151099871364953303232517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184201466495153271070976689 138151099871364953303232517)
            ·
              refine ⟨25903331225880928744356097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138151099871364953303232517 25903331225880928744356097)
              ·
                refine ⟨19427498419410696558267073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25903331225880928744356097 19427498419410696558267073)
                ·
                  refine ⟨14570623814558022418700305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19427498419410696558267073 14570623814558022418700305)
                  ·
                    refine ⟨10927967860918516814025229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14570623814558022418700305 10927967860918516814025229)
                    ·
                      refine ⟨4097987947844443805259461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10927967860918516814025229 4097987947844443805259461)
                      ·
                        rfl

theorem cell23_7980803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_7980803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980803 prefixEnd_7980803 := by exact prefixLift 7980803
  have htrace : WordTrace (prefixWord ++ tailWord_7980803) baseStart_7980803 baseEnd_7980803 := by
    simpa [prefixWord, tailWord_7980803, baseEnd_7980803] using wordTrace_append hprefix tailTrace_7980803
  have hstable : (prefixWord ++ tailWord_7980803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980803).length < 2 ^ (prefixWord ++ tailWord_7980803).sum := by decide
  have hdescent : baseEnd_7980803 < baseStart_7980803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980823 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 6]
def baseStart_7980823 : Nat := 118140960795 + 7980823 * 2 ^ 59
def prefixEnd_7980823 : Nat := 4983230072969 + 3 ^ 40 * 7980823 * 2
def baseEnd_7980823 : Nat := 455333135273059303001041

theorem tailTrace_7980823 : CollatzResearch.WordTrace tailWord_7980823 prefixEnd_7980823 455333135273059303001041 := by
  unfold tailWord_7980823
  simp only [CollatzResearch.WordTrace]
  refine ⟨291084528365848761898259123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194056352243899174598839415 291084528365848761898259123)
  ·
    refine ⟨436626792548773142847388685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291084528365848761898259123 436626792548773142847388685)
    ·
      refine ⟨163735047205789928567770757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436626792548773142847388685 163735047205789928567770757)
      ·
        refine ⟨30700321351085611606457017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163735047205789928567770757 30700321351085611606457017)
        ·
          refine ⟨23025241013314208704842763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30700321351085611606457017 23025241013314208704842763)
          ·
            refine ⟨34537861519971313057264145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23025241013314208704842763 34537861519971313057264145)
            ·
              refine ⟨25903396139978484792948109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34537861519971313057264145 25903396139978484792948109)
              ·
                refine ⟨9713773552491931797355541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25903396139978484792948109 9713773552491931797355541)
                ·
                  refine ⟨455333135273059303001041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9713773552491931797355541 455333135273059303001041)
                  ·
                    rfl

theorem cell23_7980823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 6].length) (baseStart_7980823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980823 prefixEnd_7980823 := by exact prefixLift 7980823
  have htrace : WordTrace (prefixWord ++ tailWord_7980823) baseStart_7980823 baseEnd_7980823 := by
    simpa [prefixWord, tailWord_7980823, baseEnd_7980823] using wordTrace_append hprefix tailTrace_7980823
  have hstable : (prefixWord ++ tailWord_7980823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980823).length < 2 ^ (prefixWord ++ tailWord_7980823).sum := by decide
  have hdescent : baseEnd_7980823 < baseStart_7980823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980857 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 6]
def baseStart_7980857 : Nat := 118140960795 + 7980857 * 2 ^ 59
def prefixEnd_7980857 : Nat := 4983230072969 + 3 ^ 40 * 7980857 * 2
def baseEnd_7980857 : Nat := 455335075088865177109357

theorem tailTrace_7980857 : CollatzResearch.WordTrace tailWord_7980857 prefixEnd_7980857 455335075088865177109357 := by
  unfold tailWord_7980857
  simp only [CollatzResearch.WordTrace]
  refine ⟨291085768447725585704996825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194057178965150390469997883 291085768447725585704996825)
  ·
    refine ⟨218314326335794189278747619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291085768447725585704996825 218314326335794189278747619)
    ·
      refine ⟨327471489503691283918121429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218314326335794189278747619 327471489503691283918121429)
      ·
        refine ⟨7675113035242764466830971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 327471489503691283918121429 7675113035242764466830971)
        ·
          refine ⟨11512669552864146700246457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675113035242764466830971 11512669552864146700246457)
          ·
            refine ⟨8634502164648110025184843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11512669552864146700246457 8634502164648110025184843)
            ·
              refine ⟨12951753246972165037777265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634502164648110025184843 12951753246972165037777265)
              ·
                refine ⟨9713814935229123778332949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12951753246972165037777265 9713814935229123778332949)
                ·
                  refine ⟨455335075088865177109357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9713814935229123778332949 455335075088865177109357)
                  ·
                    rfl

theorem cell23_7980857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_7980857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980857 prefixEnd_7980857 := by exact prefixLift 7980857
  have htrace : WordTrace (prefixWord ++ tailWord_7980857) baseStart_7980857 baseEnd_7980857 := by
    simpa [prefixWord, tailWord_7980857, baseEnd_7980857] using wordTrace_append hprefix tailTrace_7980857
  have hstable : (prefixWord ++ tailWord_7980857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980857).length < 2 ^ (prefixWord ++ tailWord_7980857).sum := by decide
  have hdescent : baseEnd_7980857 < baseStart_7980857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980860 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_7980860 : Nat := 118140960795 + 7980860 * 2 ^ 59
def prefixEnd_7980860 : Nat := 4983230072969 + 3 ^ 40 * 7980860 * 2
def baseEnd_7980860 : Nat := 4098017216241750082246699

theorem tailTrace_7980860 : CollatzResearch.WordTrace tailWord_7980860 prefixEnd_7980860 4098017216241750082246699 := by
  unfold tailWord_7980860
  simp only [CollatzResearch.WordTrace]
  refine ⟨145542938933357358608678017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194057251911143144811570689 145542938933357358608678017)
  ·
    refine ⟨109157204200018018956508513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145542938933357358608678017 109157204200018018956508513)
    ·
      refine ⟨81867903150013514217381385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109157204200018018956508513 81867903150013514217381385)
      ·
        refine ⟨61400927362510135663036039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81867903150013514217381385 61400927362510135663036039)
        ·
          refine ⟨92101391043765203494554059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61400927362510135663036039 92101391043765203494554059)
          ·
            refine ⟨138152086565647805241831089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92101391043765203494554059 138152086565647805241831089)
            ·
              refine ⟨103614064924235853931373317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138152086565647805241831089 103614064924235853931373317)
              ·
                refine ⟨19427637173294222612132497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103614064924235853931373317 19427637173294222612132497)
                ·
                  refine ⟨14570727879970666959099373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19427637173294222612132497 14570727879970666959099373)
                  ·
                    refine ⟨5464022954989000109662265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14570727879970666959099373 5464022954989000109662265)
                    ·
                      refine ⟨4098017216241750082246699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464022954989000109662265 4098017216241750082246699)
                      ·
                        rfl

theorem cell23_7980860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_7980860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980860 prefixEnd_7980860 := by exact prefixLift 7980860
  have htrace : WordTrace (prefixWord ++ tailWord_7980860) baseStart_7980860 baseEnd_7980860 := by
    simpa [prefixWord, tailWord_7980860, baseEnd_7980860] using wordTrace_append hprefix tailTrace_7980860
  have hstable : (prefixWord ++ tailWord_7980860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980860).length < 2 ^ (prefixWord ++ tailWord_7980860).sum := by decide
  have hdescent : baseEnd_7980860 < baseStart_7980860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980867 : List Nat := [1, 1, 1, 3, 1, 5, 2, 4, 1, 1, 3]
def baseStart_7980867 : Nat := 118140960795 + 7980867 * 2 ^ 59
def prefixEnd_7980867 : Nat := 4983230072969 + 3 ^ 40 * 7980867 * 2
def baseEnd_7980867 : Nat := 4098020810606331554859167

theorem tailTrace_7980867 : CollatzResearch.WordTrace tailWord_7980867 prefixEnd_7980867 4098020810606331554859167 := by
  unfold tailWord_7980867
  simp only [CollatzResearch.WordTrace]
  refine ⟨291086133177689357412860855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194057422118459571608573903 291086133177689357412860855)
  ·
    refine ⟨436629199766534036119291283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291086133177689357412860855 436629199766534036119291283)
    ·
      refine ⟨654943799649801054178936925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436629199766534036119291283 654943799649801054178936925)
      ·
        refine ⟨245603924868675395317101347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654943799649801054178936925 245603924868675395317101347)
        ·
          refine ⟨368405887303013092975652021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245603924868675395317101347 368405887303013092975652021)
          ·
            refine ⟨34538051934657477466467377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368405887303013092975652021 34538051934657477466467377)
            ·
              refine ⟨25903538950993108099850533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34538051934657477466467377 25903538950993108099850533)
              ·
                refine ⟨4856913553311207768721975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25903538950993108099850533 4856913553311207768721975)
                ·
                  refine ⟨7285370329966811653082963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856913553311207768721975 7285370329966811653082963)
                  ·
                    refine ⟨10928055494950217479624445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7285370329966811653082963 10928055494950217479624445)
                    ·
                      refine ⟨4098020810606331554859167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10928055494950217479624445 4098020810606331554859167)
                      ·
                        rfl

theorem cell23_7980867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_7980867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980867 prefixEnd_7980867 := by exact prefixLift 7980867
  have htrace : WordTrace (prefixWord ++ tailWord_7980867) baseStart_7980867 baseEnd_7980867 := by
    simpa [prefixWord, tailWord_7980867, baseEnd_7980867] using wordTrace_append hprefix tailTrace_7980867
  have hstable : (prefixWord ++ tailWord_7980867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980867).length < 2 ^ (prefixWord ++ tailWord_7980867).sum := by decide
  have hdescent : baseEnd_7980867 < baseStart_7980867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980877 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7980877 : Nat := 118140960795 + 7980877 * 2 ^ 59
def prefixEnd_7980877 : Nat := 4983230072969 + 3 ^ 40 * 7980877 * 2
def baseEnd_7980877 : Nat := 4098025945412876515734121

theorem tailTrace_7980877 : CollatzResearch.WordTrace tailWord_7980877 prefixEnd_7980877 4098025945412876515734121 := by
  unfold tailWord_7980877
  simp only [CollatzResearch.WordTrace]
  refine ⟨291086497907653129120724885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194057665271768752747149923 291086497907653129120724885)
  ·
    refine ⟨13644679589421240427533979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291086497907653129120724885 13644679589421240427533979)
    ·
      refine ⟨20467019384131860641300969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644679589421240427533979 20467019384131860641300969)
      ·
        refine ⟨15350264538098895480975727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20467019384131860641300969 15350264538098895480975727)
        ·
          refine ⟨23025396807148343221463591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15350264538098895480975727 23025396807148343221463591)
          ·
            refine ⟨34538095210722514832195387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23025396807148343221463591 34538095210722514832195387)
            ·
              refine ⟨51807142816083772248293081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34538095210722514832195387 51807142816083772248293081)
              ·
                refine ⟨38855357112062829186219811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51807142816083772248293081 38855357112062829186219811)
                ·
                  refine ⟨58283035668094243779329717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38855357112062829186219811 58283035668094243779329717)
                  ·
                    refine ⟨5464034593883835354312161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58283035668094243779329717 5464034593883835354312161)
                    ·
                      refine ⟨4098025945412876515734121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464034593883835354312161 4098025945412876515734121)
                      ·
                        rfl

theorem cell23_7980877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7980877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980877 prefixEnd_7980877 := by exact prefixLift 7980877
  have htrace : WordTrace (prefixWord ++ tailWord_7980877) baseStart_7980877 baseEnd_7980877 := by
    simpa [prefixWord, tailWord_7980877, baseEnd_7980877] using wordTrace_append hprefix tailTrace_7980877
  have hstable : (prefixWord ++ tailWord_7980877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980877).length < 2 ^ (prefixWord ++ tailWord_7980877).sum := by decide
  have hdescent : baseEnd_7980877 < baseStart_7980877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980890 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_7980890 : Nat := 118140960795 + 7980890 * 2 ^ 59
def prefixEnd_7980890 : Nat := 4983230072969 + 3 ^ 40 * 7980890 * 2
def baseEnd_7980890 : Nat := 4098032620661384964871561

theorem tailTrace_7980890 : CollatzResearch.WordTrace tailWord_7980890 prefixEnd_7980890 4098032620661384964871561 := by
  unfold tailWord_7980890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72771743014151508085237031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194057981371070688227298749 72771743014151508085237031)
  ·
    refine ⟨109157614521227262127855547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72771743014151508085237031 109157614521227262127855547)
    ·
      refine ⟨163736421781840893191783321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109157614521227262127855547 163736421781840893191783321)
      ·
        refine ⟨122802316336380669893837491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163736421781840893191783321 122802316336380669893837491)
        ·
          refine ⟨184203474504571004840756237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122802316336380669893837491 184203474504571004840756237)
          ·
            refine ⟨69076302939214126815283589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184203474504571004840756237 69076302939214126815283589)
            ·
              refine ⟨12951806801102648777865673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69076302939214126815283589 12951806801102648777865673)
              ·
                refine ⟨9713855100826986583399255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12951806801102648777865673 9713855100826986583399255)
                ·
                  refine ⟨14570782651240479875098883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713855100826986583399255 14570782651240479875098883)
                  ·
                    refine ⟨21856173976860719812648325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14570782651240479875098883 21856173976860719812648325)
                    ·
                      refine ⟨4098032620661384964871561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21856173976860719812648325 4098032620661384964871561)
                      ·
                        rfl

theorem cell23_7980890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_7980890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980890 prefixEnd_7980890 := by exact prefixLift 7980890
  have htrace : WordTrace (prefixWord ++ tailWord_7980890) baseStart_7980890 baseEnd_7980890 := by
    simpa [prefixWord, tailWord_7980890, baseEnd_7980890] using wordTrace_append hprefix tailTrace_7980890
  have hstable : (prefixWord ++ tailWord_7980890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980890).length < 2 ^ (prefixWord ++ tailWord_7980890).sum := by decide
  have hdescent : baseEnd_7980890 < baseStart_7980890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980903 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_7980903 : Nat := 118140960795 + 7980903 * 2 ^ 59
def prefixEnd_7980903 : Nat := 4983230072969 + 3 ^ 40 * 7980903 * 2
def baseEnd_7980903 : Nat := 4098039295909893414009001

theorem tailTrace_7980903 : CollatzResearch.WordTrace tailWord_7980903 prefixEnd_7980903 4098039295909893414009001 := by
  unfold tailWord_7980903
  simp only [CollatzResearch.WordTrace]
  refine ⟨291087446205558935561171363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194058297470372623707447575 291087446205558935561171363)
  ·
    refine ⟨436631169308338403341757045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291087446205558935561171363 436631169308338403341757045)
    ·
      refine ⟨40934172122656725313289723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436631169308338403341757045 40934172122656725313289723)
      ·
        refine ⟨61401258183985087969934585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40934172122656725313289723 61401258183985087969934585)
        ·
          refine ⟨46050943637988815977450939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61401258183985087969934585 46050943637988815977450939)
          ·
            refine ⟨69076415456983223966176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46050943637988815977450939 69076415456983223966176409)
            ·
              refine ⟨51807311592737417974632307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69076415456983223966176409 51807311592737417974632307)
              ·
                refine ⟨77710967389106126961948461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51807311592737417974632307 77710967389106126961948461)
                ·
                  refine ⟨29141612770914797610730673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77710967389106126961948461 29141612770914797610730673)
                  ·
                    refine ⟨21856209578186098208048005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29141612770914797610730673 21856209578186098208048005)
                    ·
                      refine ⟨4098039295909893414009001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21856209578186098208048005 4098039295909893414009001)
                      ·
                        rfl

theorem cell23_7980903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_7980903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980903 prefixEnd_7980903 := by exact prefixLift 7980903
  have htrace : WordTrace (prefixWord ++ tailWord_7980903) baseStart_7980903 baseEnd_7980903 := by
    simpa [prefixWord, tailWord_7980903, baseEnd_7980903] using wordTrace_append hprefix tailTrace_7980903
  have hstable : (prefixWord ++ tailWord_7980903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980903).length < 2 ^ (prefixWord ++ tailWord_7980903).sum := by decide
  have hdescent : baseEnd_7980903 < baseStart_7980903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980910 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7980910 : Nat := 118140960795 + 7980910 * 2 ^ 59
def prefixEnd_7980910 : Nat := 4983230072969 + 3 ^ 40 * 7980910 * 2
def baseEnd_7980910 : Nat := 4098042890274474886621469

theorem tailTrace_7980910 : CollatzResearch.WordTrace tailWord_7980910 prefixEnd_7980910 4098042890274474886621469 := by
  unfold tailWord_7980910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36385962689566696969584523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194058467677689050504450789 36385962689566696969584523)
  ·
    refine ⟨54578944034350045454376785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36385962689566696969584523 54578944034350045454376785)
    ·
      refine ⟨40934208025762534090782589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54578944034350045454376785 40934208025762534090782589)
      ·
        refine ⟨15350328009660950284043471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40934208025762534090782589 15350328009660950284043471)
        ·
          refine ⟨23025492014491425426065207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15350328009660950284043471 23025492014491425426065207)
          ·
            refine ⟨34538238021737138139097811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23025492014491425426065207 34538238021737138139097811)
            ·
              refine ⟨51807357032605707208646717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34538238021737138139097811 51807357032605707208646717)
              ·
                refine ⟨19427758887227140203242519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51807357032605707208646717 19427758887227140203242519)
                ·
                  refine ⟨29141638330840710304863779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19427758887227140203242519 29141638330840710304863779)
                  ·
                    refine ⟨43712457496261065457295669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29141638330840710304863779 43712457496261065457295669)
                    ·
                      refine ⟨4098042890274474886621469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43712457496261065457295669 4098042890274474886621469)
                      ·
                        rfl

theorem cell23_7980910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7980910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980910 prefixEnd_7980910 := by exact prefixLift 7980910
  have htrace : WordTrace (prefixWord ++ tailWord_7980910) baseStart_7980910 baseEnd_7980910 := by
    simpa [prefixWord, tailWord_7980910, baseEnd_7980910] using wordTrace_append hprefix tailTrace_7980910
  have hstable : (prefixWord ++ tailWord_7980910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980910).length < 2 ^ (prefixWord ++ tailWord_7980910).sum := by decide
  have hdescent : baseEnd_7980910 < baseStart_7980910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980918 : List Nat := [5, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7980918 : Nat := 118140960795 + 7980918 * 2 ^ 59
def prefixEnd_7980918 : Nat := 4983230072969 + 3 ^ 40 * 7980918 * 2
def baseEnd_7980918 : Nat := 4098046998119710855321433

theorem tailTrace_7980918 : CollatzResearch.WordTrace tailWord_7980918 prefixEnd_7980918 4098046998119710855321433 := by
  unfold tailWord_7980918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18192999581281537070185463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194058662200336395415311605 18192999581281537070185463)
  ·
    refine ⟨27289499371922305605278195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18192999581281537070185463 27289499371922305605278195)
    ·
      refine ⟨40934249057883458407917293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27289499371922305605278195 40934249057883458407917293)
      ·
        refine ⟨15350343396706296902968985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40934249057883458407917293 15350343396706296902968985)
        ·
          refine ⟨11512757547529722677226739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15350343396706296902968985 11512757547529722677226739)
          ·
            refine ⟨17269136321294584015840109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512757547529722677226739 17269136321294584015840109)
            ·
              refine ⟨6475926120485469005940041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17269136321294584015840109 6475926120485469005940041)
              ·
                refine ⟨4856944590364101754455031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475926120485469005940041 4856944590364101754455031)
                ·
                  refine ⟨7285416885546152631682547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856944590364101754455031 7285416885546152631682547)
                  ·
                    refine ⟨10928125328319228947523821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7285416885546152631682547 10928125328319228947523821)
                    ·
                      refine ⟨4098046998119710855321433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10928125328319228947523821 4098046998119710855321433)
                      ·
                        rfl

theorem cell23_7980918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7980918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980918 prefixEnd_7980918 := by exact prefixLift 7980918
  have htrace : WordTrace (prefixWord ++ tailWord_7980918) baseStart_7980918 baseEnd_7980918 := by
    simpa [prefixWord, tailWord_7980918, baseEnd_7980918] using wordTrace_append hprefix tailTrace_7980918
  have hstable : (prefixWord ++ tailWord_7980918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980918).length < 2 ^ (prefixWord ++ tailWord_7980918).sum := by decide
  have hdescent : baseEnd_7980918 < baseStart_7980918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7980990 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7980990 : Nat := 118140960795 + 7980990 * 2 ^ 59
def prefixEnd_7980990 : Nat := 4983230072969 + 3 ^ 40 * 7980990 * 2
def baseEnd_7980990 : Nat := 1366027989575611524540367

theorem tailTrace_7980990 : CollatzResearch.WordTrace tailWord_7980990 prefixEnd_7980990 1366027989575611524540367 := by
  unfold tailWord_7980990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386327419530468677448553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194060412904162499613058949 36386327419530468677448553)
  ·
    refine ⟨27289745564647851508086415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36386327419530468677448553 27289745564647851508086415)
    ·
      refine ⟨40934618346971777262129623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27289745564647851508086415 40934618346971777262129623)
      ·
        refine ⟨61401927520457665893194435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40934618346971777262129623 61401927520457665893194435)
        ·
          refine ⟨92102891280686498839791653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61401927520457665893194435 92102891280686498839791653)
          ·
            refine ⟨17269292115128718532460935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92102891280686498839791653 17269292115128718532460935)
            ·
              refine ⟨25903938172693077798691403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17269292115128718532460935 25903938172693077798691403)
              ·
                refine ⟨38855907259039616698037105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25903938172693077798691403 38855907259039616698037105)
                ·
                  refine ⟨29141930444279712523527829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38855907259039616698037105 29141930444279712523527829)
                  ·
                    refine ⟨1366027989575611524540367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29141930444279712523527829 1366027989575611524540367)
                    ·
                      rfl

theorem cell23_7980990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7980990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7980990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7980990 prefixEnd_7980990 := by exact prefixLift 7980990
  have htrace : WordTrace (prefixWord ++ tailWord_7980990) baseStart_7980990 baseEnd_7980990 := by
    simpa [prefixWord, tailWord_7980990, baseEnd_7980990] using wordTrace_append hprefix tailTrace_7980990
  have hstable : (prefixWord ++ tailWord_7980990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7980990).length < 2 ^ (prefixWord ++ tailWord_7980990).sum := by decide
  have hdescent : baseEnd_7980990 < baseStart_7980990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7980990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981003 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 7]
def baseStart_7981003 : Nat := 118140960795 + 7981003 * 2 ^ 59
def prefixEnd_7981003 : Nat := 4983230072969 + 3 ^ 40 * 7981003 * 2
def baseEnd_7981003 : Nat := 455343404886149224750949

theorem tailTrace_7981003 : CollatzResearch.WordTrace tailWord_7981003 prefixEnd_7981003 455343404886149224750949 := by
  unfold tailWord_7981003
  simp only [CollatzResearch.WordTrace]
  refine ⟨291091093505196652639811663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194060729003464435093207775 291091093505196652639811663)
  ·
    refine ⟨436636640257794978959717495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291091093505196652639811663 436636640257794978959717495)
    ·
      refine ⟨654954960386692468439576243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436636640257794978959717495 654954960386692468439576243)
      ·
        refine ⟨982432440580038702659364365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654954960386692468439576243 982432440580038702659364365)
        ·
          refine ⟨368412165217514513497261637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 982432440580038702659364365 368412165217514513497261637)
          ·
            refine ⟨69077280978283971280736557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368412165217514513497261637 69077280978283971280736557)
            ·
              refine ⟨25903980366856489230276209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69077280978283971280736557 25903980366856489230276209)
              ·
                refine ⟨19427985275142366922707157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25903980366856489230276209 19427985275142366922707157)
                ·
                  refine ⟨455343404886149224750949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19427985275142366922707157 455343404886149224750949)
                  ·
                    rfl

theorem cell23_7981003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 7].length) (baseStart_7981003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981003 prefixEnd_7981003 := by exact prefixLift 7981003
  have htrace : WordTrace (prefixWord ++ tailWord_7981003) baseStart_7981003 baseEnd_7981003 := by
    simpa [prefixWord, tailWord_7981003, baseEnd_7981003] using wordTrace_append hprefix tailTrace_7981003
  have hstable : (prefixWord ++ tailWord_7981003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981003).length < 2 ^ (prefixWord ++ tailWord_7981003).sum := by decide
  have hdescent : baseEnd_7981003 < baseStart_7981003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981018 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_7981018 : Nat := 118140960795 + 7981018 * 2 ^ 59
def prefixEnd_7981018 : Nat := 4983230072969 + 3 ^ 40 * 7981018 * 2
def baseEnd_7981018 : Nat := 4098098346185160464070973

theorem tailTrace_7981018 : CollatzResearch.WordTrace tailWord_7981018 prefixEnd_7981018 4098098346185160464070973 := by
  unfold tailWord_7981018
  simp only [CollatzResearch.WordTrace]
  refine ⟨72772910150035577550401927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194061093733428206801071805 72772910150035577550401927)
  ·
    refine ⟨109159365225053366325602891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72772910150035577550401927 109159365225053366325602891)
    ·
      refine ⟨163739047837580049488404337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109159365225053366325602891 163739047837580049488404337)
      ·
        refine ⟨122804285878185037116303253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163739047837580049488404337 122804285878185037116303253)
        ·
          refine ⟨5756450900539923614826715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122804285878185037116303253 5756450900539923614826715)
          ·
            refine ⟨8634676350809885422240073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756450900539923614826715 8634676350809885422240073)
            ·
              refine ⟨6476007263107414066680055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8634676350809885422240073 6476007263107414066680055)
              ·
                refine ⟨9714010894661121100020083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476007263107414066680055 9714010894661121100020083)
                ·
                  refine ⟨14571016341991681650030125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714010894661121100020083 14571016341991681650030125)
                  ·
                    refine ⟨5464131128246880618761297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14571016341991681650030125 5464131128246880618761297)
                    ·
                      refine ⟨4098098346185160464070973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464131128246880618761297 4098098346185160464070973)
                      ·
                        rfl

theorem cell23_7981018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_7981018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981018 prefixEnd_7981018 := by exact prefixLift 7981018
  have htrace : WordTrace (prefixWord ++ tailWord_7981018) baseStart_7981018 baseEnd_7981018 := by
    simpa [prefixWord, tailWord_7981018, baseEnd_7981018] using wordTrace_append hprefix tailTrace_7981018
  have hstable : (prefixWord ++ tailWord_7981018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981018).length < 2 ^ (prefixWord ++ tailWord_7981018).sum := by decide
  have hdescent : baseEnd_7981018 < baseStart_7981018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981040 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2]
def baseStart_7981040 : Nat := 118140960795 + 7981040 * 2 ^ 59
def prefixEnd_7981040 : Nat := 4983230072969 + 3 ^ 40 * 7981040 * 2
def baseEnd_7981040 : Nat := 4098109642759559377995871

theorem tailTrace_7981040 : CollatzResearch.WordTrace tailWord_7981040 prefixEnd_7981040 4098109642759559377995871 := by
  unfold tailWord_7981040
  simp only [CollatzResearch.WordTrace]
  refine ⟨145546221503031303979454287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194061628670708405305939049 145546221503031303979454287)
  ·
    refine ⟨218319332254546955969181431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145546221503031303979454287 218319332254546955969181431)
    ·
      refine ⟨327478998381820433953772147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218319332254546955969181431 327478998381820433953772147)
      ·
        refine ⟨491218497572730650930658221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327478998381820433953772147 491218497572730650930658221)
        ·
          refine ⟨184206936589773994098996833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491218497572730650930658221 184206936589773994098996833)
          ·
            refine ⟨138155202442330495574247625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184206936589773994098996833 138155202442330495574247625)
            ·
              refine ⟨103616401831747871680685719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138155202442330495574247625 103616401831747871680685719)
              ·
                refine ⟨155424602747621807521028579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103616401831747871680685719 155424602747621807521028579)
                ·
                  refine ⟨233136904121432711281542869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155424602747621807521028579 233136904121432711281542869)
                  ·
                    refine ⟨5464146190346079170661161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233136904121432711281542869 5464146190346079170661161)
                    ·
                      refine ⟨4098109642759559377995871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464146190346079170661161 4098109642759559377995871)
                      ·
                        rfl

theorem cell23_7981040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 7, 2].length) (baseStart_7981040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981040 prefixEnd_7981040 := by exact prefixLift 7981040
  have htrace : WordTrace (prefixWord ++ tailWord_7981040) baseStart_7981040 baseEnd_7981040 := by
    simpa [prefixWord, tailWord_7981040, baseEnd_7981040] using wordTrace_append hprefix tailTrace_7981040
  have hstable : (prefixWord ++ tailWord_7981040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981040).length < 2 ^ (prefixWord ++ tailWord_7981040).sum := by decide
  have hdescent : baseEnd_7981040 < baseStart_7981040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981043 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_7981043 : Nat := 118140960795 + 7981043 * 2 ^ 59
def prefixEnd_7981043 : Nat := 4983230072969 + 3 ^ 40 * 7981043 * 2
def baseEnd_7981043 : Nat := 4098111183201522866258357

theorem tailTrace_7981043 : CollatzResearch.WordTrace tailWord_7981043 prefixEnd_7981043 4098111183201522866258357 := by
  unfold tailWord_7981043
  simp only [CollatzResearch.WordTrace]
  refine ⟨291092552425051739471267783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194061701616701159647511855 291092552425051739471267783)
  ·
    refine ⟨436638828637577609206901675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291092552425051739471267783 436638828637577609206901675)
    ·
      refine ⟨654958242956366413810352513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436638828637577609206901675 654958242956366413810352513)
      ·
        refine ⟨491218682217274810357764385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654958242956366413810352513 491218682217274810357764385)
        ·
          refine ⟨368414011662956107768323289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491218682217274810357764385 368414011662956107768323289)
          ·
            refine ⟨276310508747217080826242467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368414011662956107768323289 276310508747217080826242467)
            ·
              refine ⟨414465763120825621239363701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276310508747217080826242467 414465763120825621239363701)
              ·
                refine ⟨38856165292577401991190347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 414465763120825621239363701 38856165292577401991190347)
                ·
                  refine ⟨58284247938866102986785521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38856165292577401991190347 58284247938866102986785521)
                  ·
                    refine ⟨43713185954149577240089141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58284247938866102986785521 43713185954149577240089141)
                    ·
                      refine ⟨4098111183201522866258357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43713185954149577240089141 4098111183201522866258357)
                      ·
                        rfl

theorem cell23_7981043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_7981043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981043 prefixEnd_7981043 := by exact prefixLift 7981043
  have htrace : WordTrace (prefixWord ++ tailWord_7981043) baseStart_7981043 baseEnd_7981043 := by
    simpa [prefixWord, tailWord_7981043, baseEnd_7981043] using wordTrace_append hprefix tailTrace_7981043
  have hstable : (prefixWord ++ tailWord_7981043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981043).length < 2 ^ (prefixWord ++ tailWord_7981043).sum := by decide
  have hdescent : baseEnd_7981043 < baseStart_7981043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981070 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7981070 : Nat := 118140960795 + 7981070 * 2 ^ 59
def prefixEnd_7981070 : Nat := 4983230072969 + 3 ^ 40 * 7981070 * 2
def baseEnd_7981070 : Nat := 4098125047179194260620733

theorem tailTrace_7981070 : CollatzResearch.WordTrace tailWord_7981070 prefixEnd_7981070 4098125047179194260620733 := by
  unfold tailWord_7981070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386692149494240385312583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194062358130635948721667109 36386692149494240385312583)
  ·
    refine ⟨54580038224241360577968875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386692149494240385312583 54580038224241360577968875)
    ·
      refine ⟨81870057336362040866953313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54580038224241360577968875 81870057336362040866953313)
      ·
        refine ⟨61402543002271530650214985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81870057336362040866953313 61402543002271530650214985)
        ·
          refine ⟨46051907251703647987661239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61402543002271530650214985 46051907251703647987661239)
          ·
            refine ⟨69077860877555471981491859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46051907251703647987661239 69077860877555471981491859)
            ·
              refine ⟨103616791316333207972237789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69077860877555471981491859 103616791316333207972237789)
              ·
                refine ⟨38856296743624952989589171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103616791316333207972237789 38856296743624952989589171)
                ·
                  refine ⟨58284445115437429484383757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38856296743624952989589171 58284445115437429484383757)
                  ·
                    refine ⟨21856666918289036056643909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58284445115437429484383757 21856666918289036056643909)
                    ·
                      refine ⟨4098125047179194260620733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21856666918289036056643909 4098125047179194260620733)
                      ·
                        rfl

theorem cell23_7981070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7981070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981070 prefixEnd_7981070 := by exact prefixLift 7981070
  have htrace : WordTrace (prefixWord ++ tailWord_7981070) baseStart_7981070 baseEnd_7981070 := by
    simpa [prefixWord, tailWord_7981070, baseEnd_7981070] using wordTrace_append hprefix tailTrace_7981070
  have hstable : (prefixWord ++ tailWord_7981070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981070).length < 2 ^ (prefixWord ++ tailWord_7981070).sum := by decide
  have hdescent : baseEnd_7981070 < baseStart_7981070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981073 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_7981073 : Nat := 118140960795 + 7981073 * 2 ^ 59
def prefixEnd_7981073 : Nat := 4983230072969 + 3 ^ 40 * 7981073 * 2
def baseEnd_7981073 : Nat := 4098126587621157748883219

theorem tailTrace_7981073 : CollatzResearch.WordTrace tailWord_7981073 prefixEnd_7981073 4098126587621157748883219 := by
  unfold tailWord_7981073
  simp only [CollatzResearch.WordTrace]
  refine ⟨291093646614943054594859873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194062431076628703063239915 291093646614943054594859873)
  ·
    refine ⟨218320234961207290946144905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291093646614943054594859873 218320234961207290946144905)
    ·
      refine ⟨163740176220905468209608679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218320234961207290946144905 163740176220905468209608679)
      ·
        refine ⟨245610264331358202314413019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163740176220905468209608679 245610264331358202314413019)
        ·
          refine ⟨368415396497037303471619529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245610264331358202314413019 368415396497037303471619529)
          ·
            refine ⟨276311547372777977603714647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368415396497037303471619529 276311547372777977603714647)
            ·
              refine ⟨414467321059166966405571971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276311547372777977603714647 414467321059166966405571971)
              ·
                refine ⟨621700981588750449608357957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414467321059166966405571971 621700981588750449608357957)
                ·
                  refine ⟨116568934047890709301567117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621700981588750449608357957 116568934047890709301567117)
                  ·
                    refine ⟨43713350267959015988087669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116568934047890709301567117 43713350267959015988087669)
                    ·
                      refine ⟨4098126587621157748883219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43713350267959015988087669 4098126587621157748883219)
                      ·
                        rfl

theorem cell23_7981073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_7981073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981073 prefixEnd_7981073 := by exact prefixLift 7981073
  have htrace : WordTrace (prefixWord ++ tailWord_7981073) baseStart_7981073 baseEnd_7981073 := by
    simpa [prefixWord, tailWord_7981073, baseEnd_7981073] using wordTrace_append hprefix tailTrace_7981073
  have hstable : (prefixWord ++ tailWord_7981073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981073).length < 2 ^ (prefixWord ++ tailWord_7981073).sum := by decide
  have hdescent : baseEnd_7981073 < baseStart_7981073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981083 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_7981083 : Nat := 118140960795 + 7981083 * 2 ^ 59
def prefixEnd_7981083 : Nat := 4983230072969 + 3 ^ 40 * 7981083 * 2
def baseEnd_7981083 : Nat := 4098131722427702709758173

theorem tailTrace_7981083 : CollatzResearch.WordTrace tailWord_7981083 prefixEnd_7981083 4098131722427702709758173 := by
  unfold tailWord_7981083
  simp only [CollatzResearch.WordTrace]
  refine ⟨291094011344906826302723903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194062674229937884201815935 291094011344906826302723903)
  ·
    refine ⟨436641017017360239454085855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291094011344906826302723903 436641017017360239454085855)
    ·
      refine ⟨654961525526040359181128783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436641017017360239454085855 654961525526040359181128783)
      ·
        refine ⟨982442288289060538771693175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654961525526040359181128783 982442288289060538771693175)
        ·
          refine ⟨1473663432433590808157539763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982442288289060538771693175 1473663432433590808157539763)
          ·
            refine ⟨2210495148650386212236309645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473663432433590808157539763 2210495148650386212236309645)
            ·
              refine ⟨828935680743894829588616117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2210495148650386212236309645 828935680743894829588616117)
              ·
                refine ⟨77712720069740140273932761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 828935680743894829588616117 77712720069740140273932761)
                ·
                  refine ⟨58284540052305105205449571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77712720069740140273932761 58284540052305105205449571)
                  ·
                    refine ⟨87426810078457657808174357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58284540052305105205449571 87426810078457657808174357)
                    ·
                      refine ⟨4098131722427702709758173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87426810078457657808174357 4098131722427702709758173)
                      ·
                        rfl

theorem cell23_7981083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_7981083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981083 prefixEnd_7981083 := by exact prefixLift 7981083
  have htrace : WordTrace (prefixWord ++ tailWord_7981083) baseStart_7981083 baseEnd_7981083 := by
    simpa [prefixWord, tailWord_7981083, baseEnd_7981083] using wordTrace_append hprefix tailTrace_7981083
  have hstable : (prefixWord ++ tailWord_7981083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981083).length < 2 ^ (prefixWord ++ tailWord_7981083).sum := by decide
  have hdescent : baseEnd_7981083 < baseStart_7981083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981148 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7981148 : Nat := 118140960795 + 7981148 * 2 ^ 59
def prefixEnd_7981148 : Nat := 4983230072969 + 3 ^ 40 * 7981148 * 2
def baseEnd_7981148 : Nat := 1366055032890081651815125

theorem tailTrace_7981148 : CollatzResearch.WordTrace tailWord_7981148 prefixEnd_7981148 1366055032890081651815125 := by
  unfold tailWord_7981148
  simp only [CollatzResearch.WordTrace]
  refine ⟨145548191044835671201920049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194064254726447561602560065 145548191044835671201920049)
  ·
    refine ⟨109161143283626753401440037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145548191044835671201920049 109161143283626753401440037)
    ·
      refine ⟨20467714365680016262770007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109161143283626753401440037 20467714365680016262770007)
      ·
        refine ⟨30701571548520024394155011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20467714365680016262770007 30701571548520024394155011)
        ·
          refine ⟨46052357322780036591232517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30701571548520024394155011 46052357322780036591232517)
          ·
            refine ⟨8634816998021256860856097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46052357322780036591232517 8634816998021256860856097)
            ·
              refine ⟨6476112748515942645642073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8634816998021256860856097 6476112748515942645642073)
              ·
                refine ⟨4857084561386956984231555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476112748515942645642073 4857084561386956984231555)
                ·
                  refine ⟨7285626842080435476347333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857084561386956984231555 7285626842080435476347333)
                  ·
                    refine ⟨1366055032890081651815125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7285626842080435476347333 1366055032890081651815125)
                    ·
                      rfl

theorem cell23_7981148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7981148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981148 prefixEnd_7981148 := by exact prefixLift 7981148
  have htrace : WordTrace (prefixWord ++ tailWord_7981148) baseStart_7981148 baseEnd_7981148 := by
    simpa [prefixWord, tailWord_7981148, baseEnd_7981148] using wordTrace_append hprefix tailTrace_7981148
  have hstable : (prefixWord ++ tailWord_7981148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981148).length < 2 ^ (prefixWord ++ tailWord_7981148).sum := by decide
  have hdescent : baseEnd_7981148 < baseStart_7981148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981177 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_7981177 : Nat := 118140960795 + 7981177 * 2 ^ 59
def prefixEnd_7981177 : Nat := 4983230072969 + 3 ^ 40 * 7981177 * 2
def baseEnd_7981177 : Nat := 4098179989609225341982741

theorem tailTrace_7981177 : CollatzResearch.WordTrace tailWord_7981177 prefixEnd_7981177 4098179989609225341982741 := by
  unfold tailWord_7981177
  simp only [CollatzResearch.WordTrace]
  refine ⟨291097439806566280356645785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194064959871044186904430523 291097439806566280356645785)
  ·
    refine ⟨218323079854924710267484339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291097439806566280356645785 218323079854924710267484339)
    ·
      refine ⟨327484619782387065401226509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218323079854924710267484339 327484619782387065401226509)
      ·
        refine ⟨122806732418395149525459941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327484619782387065401226509 122806732418395149525459941)
        ·
          refine ⟨23026262328449090536023739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122806732418395149525459941 23026262328449090536023739)
          ·
            refine ⟨34539393492673635804035609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23026262328449090536023739 34539393492673635804035609)
            ·
              refine ⟨25904545119505226853026707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34539393492673635804035609 25904545119505226853026707)
              ·
                refine ⟨38856817679257840279540061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25904545119505226853026707 38856817679257840279540061)
                ·
                  refine ⟨14571306629721690104827523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38856817679257840279540061 14571306629721690104827523)
                  ·
                    refine ⟨21856959944582535157241285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14571306629721690104827523 21856959944582535157241285)
                    ·
                      refine ⟨4098179989609225341982741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21856959944582535157241285 4098179989609225341982741)
                      ·
                        rfl

theorem cell23_7981177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_7981177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981177 prefixEnd_7981177 := by exact prefixLift 7981177
  have htrace : WordTrace (prefixWord ++ tailWord_7981177) baseStart_7981177 baseEnd_7981177 := by
    simpa [prefixWord, tailWord_7981177, baseEnd_7981177] using wordTrace_append hprefix tailTrace_7981177
  have hstable : (prefixWord ++ tailWord_7981177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981177).length < 2 ^ (prefixWord ++ tailWord_7981177).sum := by decide
  have hdescent : baseEnd_7981177 < baseStart_7981177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981181 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_7981181 : Nat := 118140960795 + 7981181 * 2 ^ 59
def prefixEnd_7981181 : Nat := 4983230072969 + 3 ^ 40 * 7981181 * 2
def baseEnd_7981181 : Nat := 4098182043531843326332723

theorem tailTrace_7981181 : CollatzResearch.WordTrace tailWord_7981181 prefixEnd_7981181 4098182043531843326332723 := by
  unfold tailWord_7981181
  simp only [CollatzResearch.WordTrace]
  refine ⟨291097585698551789039791397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194065057132367859359860931 291097585698551789039791397)
  ·
    refine ⟨54580797318478460444960887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291097585698551789039791397 54580797318478460444960887)
    ·
      refine ⟨81871195977717690667441331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54580797318478460444960887 81871195977717690667441331)
      ·
        refine ⟨122806793966576536001161997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81871195977717690667441331 122806793966576536001161997)
        ·
          refine ⟨46052547737466201000435749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122806793966576536001161997 46052547737466201000435749)
          ·
            refine ⟨8634852700774912687581703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46052547737466201000435749 8634852700774912687581703)
            ·
              refine ⟨12952279051162369031372555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634852700774912687581703 12952279051162369031372555)
              ·
                refine ⟨19428418576743553547058833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952279051162369031372555 19428418576743553547058833)
                ·
                  refine ⟨14571313932557665160294125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19428418576743553547058833 14571313932557665160294125)
                  ·
                    refine ⟨5464242724709124435110297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14571313932557665160294125 5464242724709124435110297)
                    ·
                      refine ⟨4098182043531843326332723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464242724709124435110297 4098182043531843326332723)
                      ·
                        rfl

theorem cell23_7981181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_7981181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981181 prefixEnd_7981181 := by exact prefixLift 7981181
  have htrace : WordTrace (prefixWord ++ tailWord_7981181) baseStart_7981181 baseEnd_7981181 := by
    simpa [prefixWord, tailWord_7981181, baseEnd_7981181] using wordTrace_append hprefix tailTrace_7981181
  have hstable : (prefixWord ++ tailWord_7981181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981181).length < 2 ^ (prefixWord ++ tailWord_7981181).sum := by decide
  have hdescent : baseEnd_7981181 < baseStart_7981181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981194 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_7981194 : Nat := 118140960795 + 7981194 * 2 ^ 59
def prefixEnd_7981194 : Nat := 4983230072969 + 3 ^ 40 * 7981194 * 2
def baseEnd_7981194 : Nat := 4098188718780351775470163

theorem tailTrace_7981194 : CollatzResearch.WordTrace tailWord_7981194 prefixEnd_7981194 4098188718780351775470163 := by
  unfold tailWord_7981194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72774514961876173065003659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194065373231669794840009757 72774514961876173065003659)
  ·
    refine ⟨109161772442814259597505489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72774514961876173065003659 109161772442814259597505489)
    ·
      refine ⟨81871329332110694698129117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109161772442814259597505489 81871329332110694698129117)
      ·
        refine ⟨30701748499541510511798419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81871329332110694698129117 30701748499541510511798419)
        ·
          refine ⟨46052622749312265767697629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30701748499541510511798419 46052622749312265767697629)
          ·
            refine ⟨17269733530992099662886611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46052622749312265767697629 17269733530992099662886611)
            ·
              refine ⟨25904600296488149494329917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17269733530992099662886611 25904600296488149494329917)
              ·
                refine ⟨9714225111183056060373719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25904600296488149494329917 9714225111183056060373719)
                ·
                  refine ⟨14571337666774584090560579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714225111183056060373719 14571337666774584090560579)
                  ·
                    refine ⟨21857006500161876135840869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14571337666774584090560579 21857006500161876135840869)
                    ·
                      refine ⟨4098188718780351775470163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21857006500161876135840869 4098188718780351775470163)
                      ·
                        rfl

theorem cell23_7981194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_7981194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981194 prefixEnd_7981194 := by exact prefixLift 7981194
  have htrace : WordTrace (prefixWord ++ tailWord_7981194) baseStart_7981194 baseEnd_7981194 := by
    simpa [prefixWord, tailWord_7981194, baseEnd_7981194] using wordTrace_append hprefix tailTrace_7981194
  have hstable : (prefixWord ++ tailWord_7981194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981194).length < 2 ^ (prefixWord ++ tailWord_7981194).sum := by decide
  have hdescent : baseEnd_7981194 < baseStart_7981194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981211 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 1, 2, 2]
def baseStart_7981211 : Nat := 118140960795 + 7981211 * 2 ^ 59
def prefixEnd_7981211 : Nat := 4983230072969 + 3 ^ 40 * 7981211 * 2
def baseEnd_7981211 : Nat := 4098197447951478208957585

theorem tailTrace_7981211 : CollatzResearch.WordTrace tailWord_7981211 prefixEnd_7981211 4098197447951478208957585 := by
  unfold tailWord_7981211
  simp only [CollatzResearch.WordTrace]
  refine ⟨291098679888443104163383487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194065786592295402775588991 291098679888443104163383487)
  ·
    refine ⟨436648019832664656245075231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291098679888443104163383487 436648019832664656245075231)
    ·
      refine ⟨654972029748996984367612847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436648019832664656245075231 654972029748996984367612847)
      ·
        refine ⟨982458044623495476551419271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654972029748996984367612847 982458044623495476551419271)
        ·
          refine ⟨1473687066935243214827128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982458044623495476551419271 1473687066935243214827128907)
          ·
            refine ⟨2210530600402864822240693361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473687066935243214827128907 2210530600402864822240693361)
            ·
              refine ⟨1657897950302148616680520021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210530600402864822240693361 1657897950302148616680520021)
              ·
                refine ⟨4857122901275826025431211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1657897950302148616680520021 4857122901275826025431211)
                ·
                  refine ⟨7285684351913739038146817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857122901275826025431211 7285684351913739038146817)
                  ·
                    refine ⟨5464263263935304278610113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7285684351913739038146817 5464263263935304278610113)
                    ·
                      refine ⟨4098197447951478208957585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464263263935304278610113 4098197447951478208957585)
                      ·
                        rfl

theorem cell23_7981211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 2, 2].length) (baseStart_7981211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981211 prefixEnd_7981211 := by exact prefixLift 7981211
  have htrace : WordTrace (prefixWord ++ tailWord_7981211) baseStart_7981211 baseEnd_7981211 := by
    simpa [prefixWord, tailWord_7981211, baseEnd_7981211] using wordTrace_append hprefix tailTrace_7981211
  have hstable : (prefixWord ++ tailWord_7981211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981211).length < 2 ^ (prefixWord ++ tailWord_7981211).sum := by decide
  have hdescent : baseEnd_7981211 < baseStart_7981211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981240 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_7981240 : Nat := 118140960795 + 7981240 * 2 ^ 59
def prefixEnd_7981240 : Nat := 4983230072969 + 3 ^ 40 * 7981240 * 2
def baseEnd_7981240 : Nat := 4098212338890458595494951

theorem tailTrace_7981240 : CollatzResearch.WordTrace tailWord_7981240 prefixEnd_7981240 4098212338890458595494951 := by
  unfold tailWord_7981240
  simp only [CollatzResearch.WordTrace]
  refine ⟨145549868802669021058094587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194066491736892028077459449 145549868802669021058094587)
  ·
    refine ⟨218324803204003531587141881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145549868802669021058094587 218324803204003531587141881)
    ·
      refine ⟨163743602403002648690356411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218324803204003531587141881 163743602403002648690356411)
      ·
        refine ⟨245615403604503973035534617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163743602403002648690356411 245615403604503973035534617)
        ·
          refine ⟨184211552703377979776650963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245615403604503973035534617 184211552703377979776650963)
          ·
            refine ⟨276317329055066969664976445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184211552703377979776650963 276317329055066969664976445)
            ·
              refine ⟨103618998395650113624366167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276317329055066969664976445 103618998395650113624366167)
              ·
                refine ⟨155428497593475170436549251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103618998395650113624366167 155428497593475170436549251)
                ·
                  refine ⟨233142746390212755654823877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155428497593475170436549251 233142746390212755654823877)
                  ·
                    refine ⟨43714264948164891685279477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233142746390212755654823877 43714264948164891685279477)
                    ·
                      refine ⟨4098212338890458595494951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43714264948164891685279477 4098212338890458595494951)
                      ·
                        rfl

theorem cell23_7981240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_7981240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981240 prefixEnd_7981240 := by exact prefixLift 7981240
  have htrace : WordTrace (prefixWord ++ tailWord_7981240) baseStart_7981240 baseEnd_7981240 := by
    simpa [prefixWord, tailWord_7981240, baseEnd_7981240] using wordTrace_append hprefix tailTrace_7981240
  have hstable : (prefixWord ++ tailWord_7981240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981240).length < 2 ^ (prefixWord ++ tailWord_7981240).sum := by decide
  have hdescent : baseEnd_7981240 < baseStart_7981240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981267 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 8, 2]
def baseStart_7981267 : Nat := 118140960795 + 7981267 * 2 ^ 59
def prefixEnd_7981267 : Nat := 4983230072969 + 3 ^ 40 * 7981267 * 2
def baseEnd_7981267 : Nat := 4098226202868129989857327

theorem tailTrace_7981267 : CollatzResearch.WordTrace tailWord_7981267 prefixEnd_7981267 4098226202868129989857327 := by
  unfold tailWord_7981267
  simp only [CollatzResearch.WordTrace]
  refine ⟨291100722376240225727422055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194067148250826817151614703 291100722376240225727422055)
  ·
    refine ⟨436651083564360338591133083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291100722376240225727422055 436651083564360338591133083)
    ·
      refine ⟨654976625346540507886699625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436651083564360338591133083 654976625346540507886699625)
      ·
        refine ⟨491232469009905380915024719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654976625346540507886699625 491232469009905380915024719)
        ·
          refine ⟨736848703514858071372537079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491232469009905380915024719 736848703514858071372537079)
          ·
            refine ⟨1105273055272287107058805619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736848703514858071372537079 1105273055272287107058805619)
            ·
              refine ⟨1657909582908430660588208429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105273055272287107058805619 1657909582908430660588208429)
              ·
                refine ⟨621716093590661497720578161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1657909582908430660588208429 621716093590661497720578161)
                ·
                  refine ⟨466287070192996123290433621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621716093590661497720578161 466287070192996123290433621)
                  ·
                    refine ⟨5464301603824173319809769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 466287070192996123290433621 5464301603824173319809769)
                    ·
                      refine ⟨4098226202868129989857327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464301603824173319809769 4098226202868129989857327)
                      ·
                        rfl

theorem cell23_7981267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 8, 2].length) (baseStart_7981267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981267 prefixEnd_7981267 := by exact prefixLift 7981267
  have htrace : WordTrace (prefixWord ++ tailWord_7981267) baseStart_7981267 baseEnd_7981267 := by
    simpa [prefixWord, tailWord_7981267, baseEnd_7981267] using wordTrace_append hprefix tailTrace_7981267
  have hstable : (prefixWord ++ tailWord_7981267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981267).length < 2 ^ (prefixWord ++ tailWord_7981267).sum := by decide
  have hdescent : baseEnd_7981267 < baseStart_7981267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981282 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7981282 : Nat := 118140960795 + 7981282 * 2 ^ 59
def prefixEnd_7981282 : Nat := 4983230072969 + 3 ^ 40 * 7981282 * 2
def baseEnd_7981282 : Nat := 4098233905077947431169759

theorem tailTrace_7981282 : CollatzResearch.WordTrace tailWord_7981282 prefixEnd_7981282 4098233905077947431169759 := by
  unfold tailWord_7981282
  simp only [CollatzResearch.WordTrace]
  refine ⟨72775317367796470822304525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194067512980790588859478733 72775317367796470822304525)
  ·
    refine ⟨27290744012923676558364197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72775317367796470822304525 27290744012923676558364197)
    ·
      refine ⟨5117014502423189354693287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27290744012923676558364197 5117014502423189354693287)
      ·
        refine ⟨7675521753634784032039931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5117014502423189354693287 7675521753634784032039931)
        ·
          refine ⟨11513282630452176048059897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675521753634784032039931 11513282630452176048059897)
          ·
            refine ⟨8634961972839132036044923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11513282630452176048059897 8634961972839132036044923)
            ·
              refine ⟨12952442959258698054067385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634961972839132036044923 12952442959258698054067385)
              ·
                refine ⟨9714332219444023540550539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12952442959258698054067385 9714332219444023540550539)
                ·
                  refine ⟨14571498329166035310825809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714332219444023540550539 14571498329166035310825809)
                  ·
                    refine ⟨10928623746874526483119357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14571498329166035310825809 10928623746874526483119357)
                    ·
                      refine ⟨4098233905077947431169759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10928623746874526483119357 4098233905077947431169759)
                      ·
                        rfl

theorem cell23_7981282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7981282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981282 prefixEnd_7981282 := by exact prefixLift 7981282
  have htrace : WordTrace (prefixWord ++ tailWord_7981282) baseStart_7981282 baseEnd_7981282 := by
    simpa [prefixWord, tailWord_7981282, baseEnd_7981282] using wordTrace_append hprefix tailTrace_7981282
  have hstable : (prefixWord ++ tailWord_7981282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981282).length < 2 ^ (prefixWord ++ tailWord_7981282).sum := by decide
  have hdescent : baseEnd_7981282 < baseStart_7981282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981284 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_7981284 : Nat := 118140960795 + 7981284 * 2 ^ 59
def prefixEnd_7981284 : Nat := 4983230072969 + 3 ^ 40 * 7981284 * 2
def baseEnd_7981284 : Nat := 4098234932039256423344749

theorem tailTrace_7981284 : CollatzResearch.WordTrace tailWord_7981284 prefixEnd_7981284 4098234932039256423344749 := by
  unfold tailWord_7981284
  simp only [CollatzResearch.WordTrace]
  refine ⟨145550671208589318815395453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194067561611452425087193937 145550671208589318815395453)
  ·
    refine ⟨54581501703220994555773295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145550671208589318815395453 54581501703220994555773295)
    ·
      refine ⟨81872252554831491833659943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54581501703220994555773295 81872252554831491833659943)
      ·
        refine ⟨122808378832247237750489915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81872252554831491833659943 122808378832247237750489915)
        ·
          refine ⟨184212568248370856625734873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122808378832247237750489915 184212568248370856625734873)
          ·
            refine ⟨138159426186278142469301155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184212568248370856625734873 138159426186278142469301155)
            ·
              refine ⟨207239139279417213703951733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138159426186278142469301155 207239139279417213703951733)
              ·
                refine ⟨19428669307445363784745475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207239139279417213703951733 19428669307445363784745475)
                ·
                  refine ⟨29143003961168045677118213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19428669307445363784745475 29143003961168045677118213)
                  ·
                    refine ⟨5464313242719008564459665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29143003961168045677118213 5464313242719008564459665)
                    ·
                      refine ⟨4098234932039256423344749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464313242719008564459665 4098234932039256423344749)
                      ·
                        rfl

theorem cell23_7981284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_7981284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981284 prefixEnd_7981284 := by exact prefixLift 7981284
  have htrace : WordTrace (prefixWord ++ tailWord_7981284) baseStart_7981284 baseEnd_7981284 := by
    simpa [prefixWord, tailWord_7981284, baseEnd_7981284] using wordTrace_append hprefix tailTrace_7981284
  have hstable : (prefixWord ++ tailWord_7981284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981284).length < 2 ^ (prefixWord ++ tailWord_7981284).sum := by decide
  have hdescent : baseEnd_7981284 < baseStart_7981284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981288 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7981288 : Nat := 118140960795 + 7981288 * 2 ^ 59
def prefixEnd_7981288 : Nat := 4983230072969 + 3 ^ 40 * 7981288 * 2
def baseEnd_7981288 : Nat := 4098236985961874407694731

theorem tailTrace_7981288 : CollatzResearch.WordTrace tailWord_7981288 prefixEnd_7981288 4098236985961874407694731 := by
  unfold tailWord_7981288
  simp only [CollatzResearch.WordTrace]
  refine ⟨145550744154582073156968259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194067658872776097542624345 145550744154582073156968259)
  ·
    refine ⟨218326116231873109735452389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145550744154582073156968259 218326116231873109735452389)
    ·
      refine ⟨40936146793476208075397323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218326116231873109735452389 40936146793476208075397323)
      ·
        refine ⟨61404220190214312113095985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40936146793476208075397323 61404220190214312113095985)
        ·
          refine ⟨46053165142660734084821989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61404220190214312113095985 46053165142660734084821989)
          ·
            refine ⟨8634968464248887640904123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46053165142660734084821989 8634968464248887640904123)
            ·
              refine ⟨12952452696373331461356185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634968464248887640904123 12952452696373331461356185)
              ·
                refine ⟨9714339522279998596017139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12952452696373331461356185 9714339522279998596017139)
                ·
                  refine ⟨14571509283419997894025709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714339522279998596017139 14571509283419997894025709)
                  ·
                    refine ⟨5464315981282499210259641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14571509283419997894025709 5464315981282499210259641)
                    ·
                      refine ⟨4098236985961874407694731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464315981282499210259641 4098236985961874407694731)
                      ·
                        rfl

theorem cell23_7981288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7981288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981288 prefixEnd_7981288 := by exact prefixLift 7981288
  have htrace : WordTrace (prefixWord ++ tailWord_7981288) baseStart_7981288 baseEnd_7981288 := by
    simpa [prefixWord, tailWord_7981288, baseEnd_7981288] using wordTrace_append hprefix tailTrace_7981288
  have hstable : (prefixWord ++ tailWord_7981288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981288).length < 2 ^ (prefixWord ++ tailWord_7981288).sum := by decide
  have hdescent : baseEnd_7981288 < baseStart_7981288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981324 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 5]
def baseStart_7981324 : Nat := 118140960795 + 7981324 * 2 ^ 59
def prefixEnd_7981324 : Nat := 4983230072969 + 3 ^ 40 * 7981324 * 2
def baseEnd_7981324 : Nat := 455361719029492918538285

theorem tailTrace_7981324 : CollatzResearch.WordTrace tailWord_7981324 prefixEnd_7981324 455361719029492918538285 := by
  unfold tailWord_7981324
  simp only [CollatzResearch.WordTrace]
  refine ⟨145551400668516862231123513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194068534224689149641498017 145551400668516862231123513)
  ·
    refine ⟨109163550501387646673342635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145551400668516862231123513 109163550501387646673342635)
    ·
      refine ⟨163745325752081470010013953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109163550501387646673342635 163745325752081470010013953)
      ·
        refine ⟨122808994314061102507510465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163745325752081470010013953 122808994314061102507510465)
        ·
          refine ⟨92106745735545826880632849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122808994314061102507510465 92106745735545826880632849)
          ·
            refine ⟨69080059301659370160474637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92106745735545826880632849 69080059301659370160474637)
            ·
              refine ⟨25905022238122263810177989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69080059301659370160474637 25905022238122263810177989)
              ·
                refine ⟨4857191669647924464408373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25905022238122263810177989 4857191669647924464408373)
                ·
                  refine ⟨455361719029492918538285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4857191669647924464408373 455361719029492918538285)
                  ·
                    rfl

theorem cell23_7981324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_7981324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981324 prefixEnd_7981324 := by exact prefixLift 7981324
  have htrace : WordTrace (prefixWord ++ tailWord_7981324) baseStart_7981324 baseEnd_7981324 := by
    simpa [prefixWord, tailWord_7981324, baseEnd_7981324] using wordTrace_append hprefix tailTrace_7981324
  have hstable : (prefixWord ++ tailWord_7981324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981324).length < 2 ^ (prefixWord ++ tailWord_7981324).sum := by decide
  have hdescent : baseEnd_7981324 < baseStart_7981324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981384 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 3, 4]
def baseStart_7981384 : Nat := 118140960795 + 7981384 * 2 ^ 59
def prefixEnd_7981384 : Nat := 4983230072969 + 3 ^ 40 * 7981384 * 2
def baseEnd_7981384 : Nat := 1366095426701568677364763

theorem tailTrace_7981384 : CollatzResearch.WordTrace tailWord_7981384 prefixEnd_7981384 1366095426701568677364763 := by
  unfold tailWord_7981384
  simp only [CollatzResearch.WordTrace]
  refine ⟨145552494858408177354715603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194069993144544236472954137 145552494858408177354715603)
  ·
    refine ⟨218328742287612266032073405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145552494858408177354715603 218328742287612266032073405)
    ·
      refine ⟨81873278357854599762027527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218328742287612266032073405 81873278357854599762027527)
      ·
        refine ⟨122809917536781899643041291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81873278357854599762027527 122809917536781899643041291)
        ·
          refine ⟨184214876305172849464561937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122809917536781899643041291 184214876305172849464561937)
          ·
            refine ⟨138161157228879637098421453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184214876305172849464561937 138161157228879637098421453)
            ·
              refine ⟨51810433960829863911908045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138161157228879637098421453 51810433960829863911908045)
              ·
                refine ⟨19428912735311198966965517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51810433960829863911908045 19428912735311198966965517)
                ·
                  refine ⟨7285842275741699612612069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19428912735311198966965517 7285842275741699612612069)
                  ·
                    refine ⟨1366095426701568677364763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7285842275741699612612069 1366095426701568677364763)
                    ·
                      rfl

theorem cell23_7981384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_7981384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981384 prefixEnd_7981384 := by exact prefixLift 7981384
  have htrace : WordTrace (prefixWord ++ tailWord_7981384) baseStart_7981384 baseEnd_7981384 := by
    simpa [prefixWord, tailWord_7981384, baseEnd_7981384] using wordTrace_append hprefix tailTrace_7981384
  have hstable : (prefixWord ++ tailWord_7981384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981384).length < 2 ^ (prefixWord ++ tailWord_7981384).sum := by decide
  have hdescent : baseEnd_7981384 < baseStart_7981384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981394 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_7981394 : Nat := 118140960795 + 7981394 * 2 ^ 59
def prefixEnd_7981394 : Nat := 4983230072969 + 3 ^ 40 * 7981394 * 2
def baseEnd_7981394 : Nat := 4098291414911250992969243

theorem tailTrace_7981394 : CollatzResearch.WordTrace tailWord_7981394 prefixEnd_7981394 4098291414911250992969243 := by
  unfold tailWord_7981394
  simp only [CollatzResearch.WordTrace]
  refine ⟨72776338611695031604323809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194070236297853417611530157 72776338611695031604323809)
  ·
    refine ⟨54582253958771273703242857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72776338611695031604323809 54582253958771273703242857)
    ·
      refine ⟨40936690469078455277432143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54582253958771273703242857 40936690469078455277432143)
      ·
        refine ⟨61405035703617682916148215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40936690469078455277432143 61405035703617682916148215)
        ·
          refine ⟨92107553555426524374222323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61405035703617682916148215 92107553555426524374222323)
          ·
            refine ⟨138161330333139786561333485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92107553555426524374222323 138161330333139786561333485)
            ·
              refine ⟨51810498874927419960500057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138161330333139786561333485 51810498874927419960500057)
              ·
                refine ⟨38857874156195564970375043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51810498874927419960500057 38857874156195564970375043)
                ·
                  refine ⟨58286811234293347455562565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38857874156195564970375043 58286811234293347455562565)
                  ·
                    refine ⟨10928777106430002647917981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58286811234293347455562565 10928777106430002647917981)
                    ·
                      refine ⟨4098291414911250992969243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10928777106430002647917981 4098291414911250992969243)
                      ·
                        rfl

theorem cell23_7981394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_7981394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981394 prefixEnd_7981394 := by exact prefixLift 7981394
  have htrace : WordTrace (prefixWord ++ tailWord_7981394) baseStart_7981394 baseEnd_7981394 := by
    simpa [prefixWord, tailWord_7981394, baseEnd_7981394] using wordTrace_append hprefix tailTrace_7981394
  have hstable : (prefixWord ++ tailWord_7981394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981394).length < 2 ^ (prefixWord ++ tailWord_7981394).sum := by decide
  have hdescent : baseEnd_7981394 < baseStart_7981394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981444 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_7981444 : Nat := 118140960795 + 7981444 * 2 ^ 59
def prefixEnd_7981444 : Nat := 4983230072969 + 3 ^ 40 * 7981444 * 2
def baseEnd_7981444 : Nat := 1366105696314658599114671

theorem tailTrace_7981444 : CollatzResearch.WordTrace tailWord_7981444 prefixEnd_7981444 1366105696314658599114671 := by
  unfold tailWord_7981444
  simp only [CollatzResearch.WordTrace]
  refine ⟨145553589048299492478307693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194071452064399323304410257 145553589048299492478307693)
  ·
    refine ⟨54582595893112309679365385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145553589048299492478307693 54582595893112309679365385)
    ·
      refine ⟨40936946919834232259524039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54582595893112309679365385 40936946919834232259524039)
      ·
        refine ⟨61405420379751348389286059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40936946919834232259524039 61405420379751348389286059)
        ·
          refine ⟨92108130569627022583929089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61405420379751348389286059 92108130569627022583929089)
          ·
            refine ⟨69081097927220266937946817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92108130569627022583929089 69081097927220266937946817)
            ·
              refine ⟨51810823445415200203460113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69081097927220266937946817 51810823445415200203460113)
              ·
                refine ⟨38858117584061400152595085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51810823445415200203460113 38858117584061400152595085)
                ·
                  refine ⟨14571794094023025057223157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38858117584061400152595085 14571794094023025057223157)
                  ·
                    refine ⟨1366105696314658599114671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14571794094023025057223157 1366105696314658599114671)
                    ·
                      rfl

theorem cell23_7981444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_7981444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981444 prefixEnd_7981444 := by exact prefixLift 7981444
  have htrace : WordTrace (prefixWord ++ tailWord_7981444) baseStart_7981444 baseEnd_7981444 := by
    simpa [prefixWord, tailWord_7981444, baseEnd_7981444] using wordTrace_append hprefix tailTrace_7981444
  have hstable : (prefixWord ++ tailWord_7981444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981444).length < 2 ^ (prefixWord ++ tailWord_7981444).sum := by decide
  have hdescent : baseEnd_7981444 < baseStart_7981444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981501 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_7981501 : Nat := 118140960795 + 7981501 * 2 ^ 59
def prefixEnd_7981501 : Nat := 4983230072969 + 3 ^ 40 * 7981501 * 2
def baseEnd_7981501 : Nat := 4098346357341282074331251

theorem tailTrace_7981501 : CollatzResearch.WordTrace tailWord_7981501 prefixEnd_7981501 4098346357341282074331251 := by
  unfold tailWord_7981501
  simp only [CollatzResearch.WordTrace]
  refine ⟨291109257057392483691440357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194072838038261655794293571 291109257057392483691440357)
  ·
    refine ⟨54582985698261090692145067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291109257057392483691440357 54582985698261090692145067)
    ·
      refine ⟨81874478547391636038217601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54582985698261090692145067 81874478547391636038217601)
      ·
        refine ⟨61405858910543727028663201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81874478547391636038217601 61405858910543727028663201)
        ·
          refine ⟨46054394182907795271497401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61405858910543727028663201 46054394182907795271497401)
          ·
            refine ⟨34540795637180846453623051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46054394182907795271497401 34540795637180846453623051)
            ·
              refine ⟨51811193455771269680434577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34540795637180846453623051 51811193455771269680434577)
              ·
                refine ⟨38858395091828452260325933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51811193455771269680434577 38858395091828452260325933)
                ·
                  refine ⟨14571898159435669597622225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38858395091828452260325933 14571898159435669597622225)
                  ·
                    refine ⟨10928923619576752198216669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14571898159435669597622225 10928923619576752198216669)
                    ·
                      refine ⟨4098346357341282074331251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10928923619576752198216669 4098346357341282074331251)
                      ·
                        rfl

theorem cell23_7981501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_7981501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981501 prefixEnd_7981501 := by exact prefixLift 7981501
  have htrace : WordTrace (prefixWord ++ tailWord_7981501) baseStart_7981501 baseEnd_7981501 := by
    simpa [prefixWord, tailWord_7981501, baseEnd_7981501] using wordTrace_append hprefix tailTrace_7981501
  have hstable : (prefixWord ++ tailWord_7981501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981501).length < 2 ^ (prefixWord ++ tailWord_7981501).sum := by decide
  have hdescent : baseEnd_7981501 < baseStart_7981501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981508 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7981508 : Nat := 118140960795 + 7981508 * 2 ^ 59
def prefixEnd_7981508 : Nat := 4983230072969 + 3 ^ 40 * 7981508 * 2
def baseEnd_7981508 : Nat := 1366116650568621182314573

theorem tailTrace_7981508 : CollatzResearch.WordTrace tailWord_7981508 prefixEnd_7981508 1366116650568621182314573 := by
  unfold tailWord_7981508
  simp only [CollatzResearch.WordTrace]
  refine ⟨145554756184183561943472589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194073008245578082591296785 145554756184183561943472589)
  ·
    refine ⟨54583033569068835728802221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145554756184183561943472589 54583033569068835728802221)
    ·
      refine ⟨20468637588400813398300833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54583033569068835728802221 20468637588400813398300833)
      ·
        refine ⟨15351478191300610048725625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20468637588400813398300833 15351478191300610048725625)
        ·
          refine ⟨11513608643475457536544219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15351478191300610048725625 11513608643475457536544219)
          ·
            refine ⟨17270412965213186304816329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513608643475457536544219 17270412965213186304816329)
            ·
              refine ⟨12952809723909889728612247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17270412965213186304816329 12952809723909889728612247)
              ·
                refine ⟨19429214585864834592918371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952809723909889728612247 19429214585864834592918371)
                ·
                  refine ⟨29143821878797251889377557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19429214585864834592918371 29143821878797251889377557)
                  ·
                    refine ⟨1366116650568621182314573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29143821878797251889377557 1366116650568621182314573)
                    ·
                      rfl

theorem cell23_7981508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7981508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981508 prefixEnd_7981508 := by exact prefixLift 7981508
  have htrace : WordTrace (prefixWord ++ tailWord_7981508) baseStart_7981508 baseEnd_7981508 := by
    simpa [prefixWord, tailWord_7981508, baseEnd_7981508] using wordTrace_append hprefix tailTrace_7981508
  have hstable : (prefixWord ++ tailWord_7981508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981508).length < 2 ^ (prefixWord ++ tailWord_7981508).sum := by decide
  have hdescent : baseEnd_7981508 < baseStart_7981508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981511 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_7981511 : Nat := 118140960795 + 7981511 * 2 ^ 59
def prefixEnd_7981511 : Nat := 4983230072969 + 3 ^ 40 * 7981511 * 2
def baseEnd_7981511 : Nat := 4098351492147827035206205

theorem tailTrace_7981511 : CollatzResearch.WordTrace tailWord_7981511 prefixEnd_7981511 4098351492147827035206205 := by
  unfold tailWord_7981511
  simp only [CollatzResearch.WordTrace]
  refine ⟨291109621787356255399304387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194073081191570836932869591 291109621787356255399304387)
  ·
    refine ⟨436664432681034383098956581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291109621787356255399304387 436664432681034383098956581)
    ·
      refine ⟨81874581127693946831054359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436664432681034383098956581 81874581127693946831054359)
      ·
        refine ⟨122811871691540920246581539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81874581127693946831054359 122811871691540920246581539)
        ·
          refine ⟨184217807537311380369872309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122811871691540920246581539 184217807537311380369872309)
          ·
            refine ⟨17270419456622941909675529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184217807537311380369872309 17270419456622941909675529)
            ·
              refine ⟨12952814592467206432256647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17270419456622941909675529 12952814592467206432256647)
              ·
                refine ⟨19429221888700809648384971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952814592467206432256647 19429221888700809648384971)
                ·
                  refine ⟨29143832833051214472577457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19429221888700809648384971 29143832833051214472577457)
                  ·
                    refine ⟨21857874624788410854433093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29143832833051214472577457 21857874624788410854433093)
                    ·
                      refine ⟨4098351492147827035206205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21857874624788410854433093 4098351492147827035206205)
                      ·
                        rfl

theorem cell23_7981511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_7981511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981511 prefixEnd_7981511 := by exact prefixLift 7981511
  have htrace : WordTrace (prefixWord ++ tailWord_7981511) baseStart_7981511 baseEnd_7981511 := by
    simpa [prefixWord, tailWord_7981511, baseEnd_7981511] using wordTrace_append hprefix tailTrace_7981511
  have hstable : (prefixWord ++ tailWord_7981511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981511).length < 2 ^ (prefixWord ++ tailWord_7981511).sum := by decide
  have hdescent : baseEnd_7981511 < baseStart_7981511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981535 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 1, 2, 3]
def baseStart_7981535 : Nat := 118140960795 + 7981535 * 2 ^ 59
def prefixEnd_7981535 : Nat := 4983230072969 + 3 ^ 40 * 7981535 * 2
def baseEnd_7981535 : Nat := 4098363815683534941306095

theorem tailTrace_7981535 : CollatzResearch.WordTrace tailWord_7981535 prefixEnd_7981535 4098363815683534941306095 := by
  unfold tailWord_7981535
  simp only [CollatzResearch.WordTrace]
  refine ⟨291110497139269307498178059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194073664759512871665452039 291110497139269307498178059)
  ·
    refine ⟨436665745708903961247267089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291110497139269307498178059 436665745708903961247267089)
    ·
      refine ⟨327499309281677970935450317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436665745708903961247267089 327499309281677970935450317)
      ·
        refine ⟨122812240980629239100793869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327499309281677970935450317 122812240980629239100793869)
        ·
          refine ⟨46054590367735964662797701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122812240980629239100793869 46054590367735964662797701)
          ·
            refine ⟨8635235693950493374274569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46054590367735964662797701 8635235693950493374274569)
            ·
              refine ⟨6476426770462870030705927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8635235693950493374274569 6476426770462870030705927)
              ·
                refine ⟨9714640155694305046058891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476426770462870030705927 9714640155694305046058891)
                ·
                  refine ⟨14571960233541457569088337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714640155694305046058891 14571960233541457569088337)
                  ·
                    refine ⟨10928970175156093176816253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14571960233541457569088337 10928970175156093176816253)
                    ·
                      refine ⟨4098363815683534941306095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10928970175156093176816253 4098363815683534941306095)
                      ·
                        rfl

theorem cell23_7981535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_7981535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981535 prefixEnd_7981535 := by exact prefixLift 7981535
  have htrace : WordTrace (prefixWord ++ tailWord_7981535) baseStart_7981535 baseEnd_7981535 := by
    simpa [prefixWord, tailWord_7981535, baseEnd_7981535] using wordTrace_append hprefix tailTrace_7981535
  have hstable : (prefixWord ++ tailWord_7981535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981535).length < 2 ^ (prefixWord ++ tailWord_7981535).sum := by decide
  have hdescent : baseEnd_7981535 < baseStart_7981535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981538 : List Nat := [3, 3, 3, 2, 1, 1, 10]
def baseStart_7981538 : Nat := 118140960795 + 7981538 * 2 ^ 59
def prefixEnd_7981538 : Nat := 4983230072969 + 3 ^ 40 * 7981538 * 2
def baseEnd_7981538 : Nat := 50597103162043190488501

theorem tailTrace_7981538 : CollatzResearch.WordTrace tailWord_7981538 prefixEnd_7981538 50597103162043190488501 := by
  unfold tailWord_7981538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72777651639564609752634317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194073737705505626007024845 72777651639564609752634317)
  ·
    refine ⟨27291619364836728657237869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72777651639564609752634317 27291619364836728657237869)
    ·
      refine ⟨10234357261813773246464201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27291619364836728657237869 10234357261813773246464201)
      ·
        refine ⟨7675767946360329934848151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10234357261813773246464201 7675767946360329934848151)
        ·
          refine ⟨11513651919540494902272227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675767946360329934848151 11513651919540494902272227)
          ·
            refine ⟨17270477879310742353408341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513651919540494902272227 17270477879310742353408341)
            ·
              refine ⟨50597103162043190488501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17270477879310742353408341 50597103162043190488501)
              ·
                rfl

theorem cell23_7981538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 10].length) (baseStart_7981538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981538 prefixEnd_7981538 := by exact prefixLift 7981538
  have htrace : WordTrace (prefixWord ++ tailWord_7981538) baseStart_7981538 baseEnd_7981538 := by
    simpa [prefixWord, tailWord_7981538, baseEnd_7981538] using wordTrace_append hprefix tailTrace_7981538
  have hstable : (prefixWord ++ tailWord_7981538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981538).length < 2 ^ (prefixWord ++ tailWord_7981538).sum := by decide
  have hdescent : baseEnd_7981538 < baseStart_7981538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981565 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_7981565 : Nat := 118140960795 + 7981565 * 2 ^ 59
def prefixEnd_7981565 : Nat := 4983230072969 + 3 ^ 40 * 7981565 * 2
def baseEnd_7981565 : Nat := 4098379220103169823930957

theorem tailTrace_7981565 : CollatzResearch.WordTrace tailWord_7981565 prefixEnd_7981565 4098379220103169823930957 := by
  unfold tailWord_7981565
  simp only [CollatzResearch.WordTrace]
  refine ⟨291111591329160622621770149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194074394219440415081180099 291111591329160622621770149)
  ·
    refine ⟨54583423374217616741581903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291111591329160622621770149 54583423374217616741581903)
    ·
      refine ⟨81875135061326425112372855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54583423374217616741581903 81875135061326425112372855)
      ·
        refine ⟨122812702591989637668559283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81875135061326425112372855 122812702591989637668559283)
        ·
          refine ⟨184219053887984456502838925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122812702591989637668559283 184219053887984456502838925)
          ·
            refine ⟨69082145207994171188564597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184219053887984456502838925 69082145207994171188564597)
            ·
              refine ⟨6476451113249453548927931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69082145207994171188564597 6476451113249453548927931)
              ·
                refine ⟨9714676669874180323391897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476451113249453548927931 9714676669874180323391897)
                ·
                  refine ⟨7286007502405635242543923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714676669874180323391897 7286007502405635242543923)
                  ·
                    refine ⟨10929011253608452863815885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7286007502405635242543923 10929011253608452863815885)
                    ·
                      refine ⟨4098379220103169823930957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10929011253608452863815885 4098379220103169823930957)
                      ·
                        rfl

theorem cell23_7981565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_7981565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981565 prefixEnd_7981565 := by exact prefixLift 7981565
  have htrace : WordTrace (prefixWord ++ tailWord_7981565) baseStart_7981565 baseEnd_7981565 := by
    simpa [prefixWord, tailWord_7981565, baseEnd_7981565] using wordTrace_append hprefix tailTrace_7981565
  have hstable : (prefixWord ++ tailWord_7981565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981565).length < 2 ^ (prefixWord ++ tailWord_7981565).sum := by decide
  have hdescent : baseEnd_7981565 < baseStart_7981565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981594 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_7981594 : Nat := 118140960795 + 7981594 * 2 ^ 59
def prefixEnd_7981594 : Nat := 4983230072969 + 3 ^ 40 * 7981594 * 2
def baseEnd_7981594 : Nat := 455377123449127801163147

theorem tailTrace_7981594 : CollatzResearch.WordTrace tailWord_7981594 prefixEnd_7981594 455377123449127801163147 := by
  unfold tailWord_7981594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72778162261513890143643959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194075099364037040383050557 72778162261513890143643959)
  ·
    refine ⟨109167243392270835215465939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72778162261513890143643959 109167243392270835215465939)
    ·
      refine ⟨163750865088406252823198909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109167243392270835215465939 163750865088406252823198909)
      ·
        refine ⟨61406574408152344808699591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163750865088406252823198909 61406574408152344808699591)
        ·
          refine ⟨92109861612228517213049387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61406574408152344808699591 92109861612228517213049387)
          ·
            refine ⟨138164792418342775819574081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92109861612228517213049387 138164792418342775819574081)
            ·
              refine ⟨103623594313757081864680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138164792418342775819574081 103623594313757081864680561)
              ·
                refine ⟨77717695735317811398510421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103623594313757081864680561 77717695735317811398510421)
                ·
                  refine ⟨455377123449127801163147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77717695735317811398510421 455377123449127801163147)
                  ·
                    rfl

theorem cell23_7981594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_7981594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981594 prefixEnd_7981594 := by exact prefixLift 7981594
  have htrace : WordTrace (prefixWord ++ tailWord_7981594) baseStart_7981594 baseEnd_7981594 := by
    simpa [prefixWord, tailWord_7981594, baseEnd_7981594] using wordTrace_append hprefix tailTrace_7981594
  have hstable : (prefixWord ++ tailWord_7981594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981594).length < 2 ^ (prefixWord ++ tailWord_7981594).sum := by decide
  have hdescent : baseEnd_7981594 < baseStart_7981594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981611 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 5]
def baseStart_7981611 : Nat := 118140960795 + 7981611 * 2 ^ 59
def prefixEnd_7981611 : Nat := 4983230072969 + 3 ^ 40 * 7981611 * 2
def baseEnd_7981611 : Nat := 455378093357030738217305

theorem tailTrace_7981611 : CollatzResearch.WordTrace tailWord_7981611 prefixEnd_7981611 455378093357030738217305 := by
  unfold tailWord_7981611
  simp only [CollatzResearch.WordTrace]
  refine ⟨291113269086993972477944687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194075512724662648318629791 291113269086993972477944687)
  ·
    refine ⟨436669903630490958716917031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291113269086993972477944687 436669903630490958716917031)
    ·
      refine ⟨655004855445736438075375547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436669903630490958716917031 655004855445736438075375547)
      ·
        refine ⟨982507283168604657113063321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655004855445736438075375547 982507283168604657113063321)
        ·
          refine ⟨736880462376453492834797491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982507283168604657113063321 736880462376453492834797491)
          ·
            refine ⟨1105320693564680239252196237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736880462376453492834797491 1105320693564680239252196237)
            ·
              refine ⟨414495260086755089719573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105320693564680239252196237 414495260086755089719573589)
              ·
                refine ⟨4857366329141661207651253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 414495260086755089719573589 4857366329141661207651253)
                ·
                  refine ⟨455378093357030738217305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4857366329141661207651253 455378093357030738217305)
                  ·
                    rfl

theorem cell23_7981611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 5].length) (baseStart_7981611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981611 prefixEnd_7981611 := by exact prefixLift 7981611
  have htrace : WordTrace (prefixWord ++ tailWord_7981611) baseStart_7981611 baseEnd_7981611 := by
    simpa [prefixWord, tailWord_7981611, baseEnd_7981611] using wordTrace_append hprefix tailTrace_7981611
  have hstable : (prefixWord ++ tailWord_7981611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981611).length < 2 ^ (prefixWord ++ tailWord_7981611).sum := by decide
  have hdescent : baseEnd_7981611 < baseStart_7981611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981621 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_7981621 : Nat := 118140960795 + 7981621 * 2 ^ 59
def prefixEnd_7981621 : Nat := 4983230072969 + 3 ^ 40 * 7981621 * 2
def baseEnd_7981621 : Nat := 4098407975019821604830699

theorem tailTrace_7981621 : CollatzResearch.WordTrace tailWord_7981621 prefixEnd_7981621 4098407975019821604830699 := by
  unfold tailWord_7981621
  simp only [CollatzResearch.WordTrace]
  refine ⟨291113633816957744185808717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194075755877971829457205811 291113633816957744185808717)
  ·
    refine ⟨109167612681359154069678269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291113633816957744185808717 109167612681359154069678269)
    ·
      refine ⟨40937854755509682776129351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109167612681359154069678269 40937854755509682776129351)
      ·
        refine ⟨61406782133264524164194027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40937854755509682776129351 61406782133264524164194027)
        ·
          refine ⟨92110173199896786246291041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61406782133264524164194027 92110173199896786246291041)
          ·
            refine ⟨69082629899922589684718281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92110173199896786246291041 69082629899922589684718281)
            ·
              refine ⟨51811972424941942263538711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69082629899922589684718281 51811972424941942263538711)
              ·
                refine ⟨77717958637412913395308067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51811972424941942263538711 77717958637412913395308067)
                ·
                  refine ⟨116576937956119370092962101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77717958637412913395308067 116576937956119370092962101)
                  ·
                    refine ⟨10929087933386190946215197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116576937956119370092962101 10929087933386190946215197)
                    ·
                      refine ⟨4098407975019821604830699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10929087933386190946215197 4098407975019821604830699)
                      ·
                        rfl

theorem cell23_7981621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_7981621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981621 prefixEnd_7981621 := by exact prefixLift 7981621
  have htrace : WordTrace (prefixWord ++ tailWord_7981621) baseStart_7981621 baseEnd_7981621 := by
    simpa [prefixWord, tailWord_7981621, baseEnd_7981621] using wordTrace_append hprefix tailTrace_7981621
  have hstable : (prefixWord ++ tailWord_7981621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981621).length < 2 ^ (prefixWord ++ tailWord_7981621).sum := by decide
  have hdescent : baseEnd_7981621 < baseStart_7981621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981722 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_7981722 : Nat := 118140960795 + 7981722 * 2 ^ 59
def prefixEnd_7981722 : Nat := 4983230072969 + 3 ^ 40 * 7981722 * 2
def baseEnd_7981722 : Nat := 1366153278855308569889245

theorem tailTrace_7981722 : CollatzResearch.WordTrace tailWord_7981722 prefixEnd_7981722 1366153278855308569889245 := by
  unfold tailWord_7981722
  simp only [CollatzResearch.WordTrace]
  refine ⟨72779329397397959608808855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194078211726394558956823613 72779329397397959608808855)
  ·
    refine ⟨109168994096096939413213283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72779329397397959608808855 109168994096096939413213283)
    ·
      refine ⟨163753491144145409119819925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109168994096096939413213283 163753491144145409119819925)
      ·
        refine ⟨7675944897381816052491559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163753491144145409119819925 7675944897381816052491559)
        ·
          refine ⟨11513917346072724078737339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675944897381816052491559 11513917346072724078737339)
          ·
            refine ⟨17270876019109086118106009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513917346072724078737339 17270876019109086118106009)
            ·
              refine ⟨12953157014331814588579507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17270876019109086118106009 12953157014331814588579507)
              ·
                refine ⟨19429735521497721882869261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12953157014331814588579507 19429735521497721882869261)
                ·
                  refine ⟨7286150820561645706075973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19429735521497721882869261 7286150820561645706075973)
                  ·
                    refine ⟨1366153278855308569889245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286150820561645706075973 1366153278855308569889245)
                    ·
                      rfl

theorem cell23_7981722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_7981722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981722 prefixEnd_7981722 := by exact prefixLift 7981722
  have htrace : WordTrace (prefixWord ++ tailWord_7981722) baseStart_7981722 baseEnd_7981722 := by
    simpa [prefixWord, tailWord_7981722, baseEnd_7981722] using wordTrace_append hprefix tailTrace_7981722
  have hstable : (prefixWord ++ tailWord_7981722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981722).length < 2 ^ (prefixWord ++ tailWord_7981722).sum := by decide
  have hdescent : baseEnd_7981722 < baseStart_7981722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981731 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 3, 5]
def baseStart_7981731 : Nat := 118140960795 + 7981731 * 2 ^ 59
def prefixEnd_7981731 : Nat := 4983230072969 + 3 ^ 40 * 7981731 * 2
def baseEnd_7981731 : Nat := 1366154819297272058151731

theorem tailTrace_7981731 : CollatzResearch.WordTrace tailWord_7981731 prefixEnd_7981731 1366154819297272058151731 := by
  unfold tailWord_7981731
  simp only [CollatzResearch.WordTrace]
  refine ⟨291117645846559232972313047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194078430564372821981542031 291117645846559232972313047)
  ·
    refine ⟨436676468769838849458469571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291117645846559232972313047 436676468769838849458469571)
    ·
      refine ⟨655014703154758274187704357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436676468769838849458469571 655014703154758274187704357)
      ·
        refine ⟨122815256841517176410194567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 655014703154758274187704357 122815256841517176410194567)
        ·
          refine ⟨184222885262275764615291851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122815256841517176410194567 184222885262275764615291851)
          ·
            refine ⟨276334327893413646922937777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184222885262275764615291851 276334327893413646922937777)
            ·
              refine ⟨207250745920060235192203333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276334327893413646922937777 207250745920060235192203333)
              ·
                refine ⟨38859514860011294098538125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207250745920060235192203333 38859514860011294098538125)
                ·
                  refine ⟨14572318072504235286951797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38859514860011294098538125 14572318072504235286951797)
                  ·
                    refine ⟨1366154819297272058151731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14572318072504235286951797 1366154819297272058151731)
                    ·
                      rfl

theorem cell23_7981731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 5].length) (baseStart_7981731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981731 prefixEnd_7981731 := by exact prefixLift 7981731
  have htrace : WordTrace (prefixWord ++ tailWord_7981731) baseStart_7981731 baseEnd_7981731 := by
    simpa [prefixWord, tailWord_7981731, baseEnd_7981731] using wordTrace_append hprefix tailTrace_7981731
  have hstable : (prefixWord ++ tailWord_7981731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981731).length < 2 ^ (prefixWord ++ tailWord_7981731).sum := by decide
  have hdescent : baseEnd_7981731 < baseStart_7981731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981772 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7981772 : Nat := 118140960795 + 7981772 * 2 ^ 59
def prefixEnd_7981772 : Nat := 4983230072969 + 3 ^ 40 * 7981772 * 2
def baseEnd_7981772 : Nat := 4098485510598650514042505

theorem tailTrace_7981772 : CollatzResearch.WordTrace tailWord_7981772 prefixEnd_7981772 4098485510598650514042505 := by
  unfold tailWord_7981772
  simp only [CollatzResearch.WordTrace]
  refine ⟨145559570619705348487277785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194079427492940464649703713 145559570619705348487277785)
  ·
    refine ⟨109169677964779011365458339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145559570619705348487277785 109169677964779011365458339)
    ·
      refine ⟨163754516947168517048187509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109169677964779011365458339 163754516947168517048187509)
      ·
        refine ⟨15351985963797048473267579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163754516947168517048187509 15351985963797048473267579)
        ·
          refine ⟨23027978945695572709901369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15351985963797048473267579 23027978945695572709901369)
          ·
            refine ⟨17270984209271679532426027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23027978945695572709901369 17270984209271679532426027)
            ·
              refine ⟨25906476313907519298639041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17270984209271679532426027 25906476313907519298639041)
              ·
                refine ⟨19429857235430639473979281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25906476313907519298639041 19429857235430639473979281)
                ·
                  refine ⟨14572392926572979605484461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19429857235430639473979281 14572392926572979605484461)
                  ·
                    refine ⟨5464647347464867352056673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14572392926572979605484461 5464647347464867352056673)
                    ·
                      refine ⟨4098485510598650514042505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464647347464867352056673 4098485510598650514042505)
                      ·
                        rfl

theorem cell23_7981772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7981772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981772 prefixEnd_7981772 := by exact prefixLift 7981772
  have htrace : WordTrace (prefixWord ++ tailWord_7981772) baseStart_7981772 baseEnd_7981772 := by
    simpa [prefixWord, tailWord_7981772, baseEnd_7981772] using wordTrace_append hprefix tailTrace_7981772
  have hstable : (prefixWord ++ tailWord_7981772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981772).length < 2 ^ (prefixWord ++ tailWord_7981772).sum := by decide
  have hdescent : baseEnd_7981772 < baseStart_7981772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981791 : List Nat := [1, 1, 2, 3, 2, 3, 1, 10]
def baseStart_7981791 : Nat := 118140960795 + 7981791 * 2 ^ 59
def prefixEnd_7981791 : Nat := 4983230072969 + 3 ^ 40 * 7981791 * 2
def baseEnd_7981791 : Nat := 151796120990040219989071

theorem tailTrace_7981791 : CollatzResearch.WordTrace tailWord_7981791 prefixEnd_7981791 151796120990040219989071 := by
  unfold tailWord_7981791
  simp only [CollatzResearch.WordTrace]
  refine ⟨291119834226341863219497227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194079889484227908812998151 291119834226341863219497227)
  ·
    refine ⟨436679751339512794829245841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291119834226341863219497227 436679751339512794829245841)
    ·
      refine ⟨327509813504634596121934381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436679751339512794829245841 327509813504634596121934381)
      ·
        refine ⟨122816180064237973545725393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327509813504634596121934381 122816180064237973545725393)
        ·
          refine ⟨92112135048178480159294045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122816180064237973545725393 92112135048178480159294045)
          ·
            refine ⟨34542050643066930059735267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92112135048178480159294045 34542050643066930059735267)
            ·
              refine ⟨51813075964600395089602901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34542050643066930059735267 51813075964600395089602901)
              ·
                refine ⟨151796120990040219989071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51813075964600395089602901 151796120990040219989071)
                ·
                  rfl

theorem cell23_7981791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 10].length) (baseStart_7981791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981791 prefixEnd_7981791 := by exact prefixLift 7981791
  have htrace : WordTrace (prefixWord ++ tailWord_7981791) baseStart_7981791 baseEnd_7981791 := by
    simpa [prefixWord, tailWord_7981791, baseEnd_7981791] using wordTrace_append hprefix tailTrace_7981791
  have hstable : (prefixWord ++ tailWord_7981791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981791).length < 2 ^ (prefixWord ++ tailWord_7981791).sum := by decide
  have hdescent : baseEnd_7981791 < baseStart_7981791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981805 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7981805 : Nat := 118140960795 + 7981805 * 2 ^ 59
def prefixEnd_7981805 : Nat := 4983230072969 + 3 ^ 40 * 7981805 * 2
def baseEnd_7981805 : Nat := 4098502455460248884929853

theorem tailTrace_7981805 : CollatzResearch.WordTrace tailWord_7981805 prefixEnd_7981805 4098502455460248884929853 := by
  unfold tailWord_7981805
  simp only [CollatzResearch.WordTrace]
  refine ⟨291120344848291143610506869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194080229898860762407004579 291120344848291143610506869)
  ·
    refine ⟨27292532329527294713485019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291120344848291143610506869 27292532329527294713485019)
    ·
      refine ⟨40938798494290942070227529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27292532329527294713485019 40938798494290942070227529)
      ·
        refine ⟨30704098870718206552670647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40938798494290942070227529 30704098870718206552670647)
        ·
          refine ⟨46056148306077309829005971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30704098870718206552670647 46056148306077309829005971)
          ·
            refine ⟨69084222459115964743508957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46056148306077309829005971 69084222459115964743508957)
            ·
              refine ⟨25906583422168486778815859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69084222459115964743508957 25906583422168486778815859)
              ·
                refine ⟨38859875133252730168223789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25906583422168486778815859 38859875133252730168223789)
                ·
                  refine ⟨14572453174969773813083921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38859875133252730168223789 14572453174969773813083921)
                  ·
                    refine ⟨10929339881227330359812941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14572453174969773813083921 10929339881227330359812941)
                    ·
                      refine ⟨4098502455460248884929853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10929339881227330359812941 4098502455460248884929853)
                      ·
                        rfl

theorem cell23_7981805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7981805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981805 prefixEnd_7981805 := by exact prefixLift 7981805
  have htrace : WordTrace (prefixWord ++ tailWord_7981805) baseStart_7981805 baseEnd_7981805 := by
    simpa [prefixWord, tailWord_7981805, baseEnd_7981805] using wordTrace_append hprefix tailTrace_7981805
  have hstable : (prefixWord ++ tailWord_7981805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981805).length < 2 ^ (prefixWord ++ tailWord_7981805).sum := by decide
  have hdescent : baseEnd_7981805 < baseStart_7981805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981818 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_7981818 : Nat := 118140960795 + 7981818 * 2 ^ 59
def prefixEnd_7981818 : Nat := 4983230072969 + 3 ^ 40 * 7981818 * 2
def baseEnd_7981818 : Nat := 4098509130708757334067293

theorem tailTrace_7981818 : CollatzResearch.WordTrace tailWord_7981818 prefixEnd_7981818 4098509130708757334067293 := by
  unfold tailWord_7981818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72780204749311011707682527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194080545998162697887153405 72780204749311011707682527)
  ·
    refine ⟨109170307123966517561523791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72780204749311011707682527 109170307123966517561523791)
    ·
      refine ⟨163755460685949776342285687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109170307123966517561523791 163755460685949776342285687)
      ·
        refine ⟨245633191028924664513428531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163755460685949776342285687 245633191028924664513428531)
        ·
          refine ⟨368449786543386996770142797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245633191028924664513428531 368449786543386996770142797)
          ·
            refine ⟨138168669953770123788803549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368449786543386996770142797 138168669953770123788803549)
            ·
              refine ⟨51813251232663796420801331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138168669953770123788803549 51813251232663796420801331)
              ·
                refine ⟨77719876848995694631201997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51813251232663796420801331 77719876848995694631201997)
                ·
                  refine ⟨29144953818373385486700749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77719876848995694631201997 29144953818373385486700749)
                  ·
                    refine ⟨10929357681890019557512781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29144953818373385486700749 10929357681890019557512781)
                    ·
                      refine ⟨4098509130708757334067293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10929357681890019557512781 4098509130708757334067293)
                      ·
                        rfl

theorem cell23_7981818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_7981818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981818 prefixEnd_7981818 := by exact prefixLift 7981818
  have htrace : WordTrace (prefixWord ++ tailWord_7981818) baseStart_7981818 baseEnd_7981818 := by
    simpa [prefixWord, tailWord_7981818, baseEnd_7981818] using wordTrace_append hprefix tailTrace_7981818
  have hstable : (prefixWord ++ tailWord_7981818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981818).length < 2 ^ (prefixWord ++ tailWord_7981818).sum := by decide
  have hdescent : baseEnd_7981818 < baseStart_7981818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981822 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7981822 : Nat := 118140960795 + 7981822 * 2 ^ 59
def prefixEnd_7981822 : Nat := 4983230072969 + 3 ^ 40 * 7981822 * 2
def baseEnd_7981822 : Nat := 4098511184631375318417275

theorem tailTrace_7981822 : CollatzResearch.WordTrace tailWord_7981822 prefixEnd_7981822 4098511184631375318417275 := by
  unfold tailWord_7981822
  simp only [CollatzResearch.WordTrace]
  refine ⟨36390120611153694439234465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194080643259486370342583813 36390120611153694439234465)
  ·
    refine ⟨27292590458365270829425849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36390120611153694439234465 27292590458365270829425849)
    ·
      refine ⟨20469442843773953122069387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27292590458365270829425849 20469442843773953122069387)
      ·
        refine ⟨30704164265660929683104081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20469442843773953122069387 30704164265660929683104081)
        ·
          refine ⟨23028123199245697262328061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30704164265660929683104081 23028123199245697262328061)
          ·
            refine ⟨8635546199717136473373023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23028123199245697262328061 8635546199717136473373023)
            ·
              refine ⟨12953319299575704710059535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635546199717136473373023 12953319299575704710059535)
              ·
                refine ⟨19429978949363557065089303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12953319299575704710059535 19429978949363557065089303)
                ·
                  refine ⟨29144968424045335597633955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19429978949363557065089303 29144968424045335597633955)
                  ·
                    refine ⟨43717452636068003396450933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29144968424045335597633955 43717452636068003396450933)
                    ·
                      refine ⟨4098511184631375318417275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43717452636068003396450933 4098511184631375318417275)
                      ·
                        rfl

theorem cell23_7981822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7981822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981822 prefixEnd_7981822 := by exact prefixLift 7981822
  have htrace : WordTrace (prefixWord ++ tailWord_7981822) baseStart_7981822 baseEnd_7981822 := by
    simpa [prefixWord, tailWord_7981822, baseEnd_7981822] using wordTrace_append hprefix tailTrace_7981822
  have hstable : (prefixWord ++ tailWord_7981822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981822).length < 2 ^ (prefixWord ++ tailWord_7981822).sum := by decide
  have hdescent : baseEnd_7981822 < baseStart_7981822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981842 : List Nat := [3, 2, 4, 1, 2, 2, 1, 8]
def baseStart_7981842 : Nat := 118140960795 + 7981842 * 2 ^ 59
def prefixEnd_7981842 : Nat := 4983230072969 + 3 ^ 40 * 7981842 * 2
def baseEnd_7981842 : Nat := 151797090897943157043229

theorem tailTrace_7981842 : CollatzResearch.WordTrace tailWord_7981842 prefixEnd_7981842 151797090897943157043229 := by
  unfold tailWord_7981842
  simp only [CollatzResearch.WordTrace]
  refine ⟨72780423587289274732400945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194081129566104732619735853 72780423587289274732400945)
  ·
    refine ⟨54585317690466956049300709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72780423587289274732400945 54585317690466956049300709)
    ·
      refine ⟨10234747066962554259243883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54585317690466956049300709 10234747066962554259243883)
      ·
        refine ⟨15352120600443831388865825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10234747066962554259243883 15352120600443831388865825)
        ·
          refine ⟨11514090450332873541649369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15352120600443831388865825 11514090450332873541649369)
          ·
            refine ⟨8635567837749655156237027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11514090450332873541649369 8635567837749655156237027)
            ·
              refine ⟨12953351756624482734355541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635567837749655156237027 12953351756624482734355541)
              ·
                refine ⟨151797090897943157043229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12953351756624482734355541 151797090897943157043229)
                ·
                  rfl

theorem cell23_7981842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_7981842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981842 prefixEnd_7981842 := by exact prefixLift 7981842
  have htrace : WordTrace (prefixWord ++ tailWord_7981842) baseStart_7981842 baseEnd_7981842 := by
    simpa [prefixWord, tailWord_7981842, baseEnd_7981842] using wordTrace_append hprefix tailTrace_7981842
  have hstable : (prefixWord ++ tailWord_7981842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981842).length < 2 ^ (prefixWord ++ tailWord_7981842).sum := by decide
  have hdescent : baseEnd_7981842 < baseStart_7981842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981845 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_7981845 : Nat := 118140960795 + 7981845 * 2 ^ 59
def prefixEnd_7981845 : Nat := 4983230072969 + 3 ^ 40 * 7981845 * 2
def baseEnd_7981845 : Nat := 4098522994686428728429669

theorem tailTrace_7981845 : CollatzResearch.WordTrace tailWord_7981845 prefixEnd_7981845 4098522994686428728429669 := by
  unfold tailWord_7981845
  simp only [CollatzResearch.WordTrace]
  refine ⟨291121803768146230441962989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194081202512097486961308659 291121803768146230441962989)
  ·
    refine ⟨109170676413054836415736121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291121803768146230441962989 109170676413054836415736121)
    ·
      refine ⟨81878007309791127311802091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109170676413054836415736121 81878007309791127311802091)
      ·
        refine ⟨122817010964686690967703137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81878007309791127311802091 122817010964686690967703137)
        ·
          refine ⟨92112758223515018225777353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122817010964686690967703137 92112758223515018225777353)
          ·
            refine ⟨69084568667636263669333015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92112758223515018225777353 69084568667636263669333015)
            ·
              refine ⟨103626853001454395503999523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69084568667636263669333015 103626853001454395503999523)
              ·
                refine ⟨155440279502181593255999285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103626853001454395503999523 155440279502181593255999285)
                ·
                  refine ⟨14572526203329524367749933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155440279502181593255999285 14572526203329524367749933)
                  ·
                    refine ⟨5464697326248571637906225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14572526203329524367749933 5464697326248571637906225)
                    ·
                      refine ⟨4098522994686428728429669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464697326248571637906225 4098522994686428728429669)
                      ·
                        rfl

theorem cell23_7981845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_7981845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981845 prefixEnd_7981845 := by exact prefixLift 7981845
  have htrace : WordTrace (prefixWord ++ tailWord_7981845) baseStart_7981845 baseEnd_7981845 := by
    simpa [prefixWord, tailWord_7981845, baseEnd_7981845] using wordTrace_append hprefix tailTrace_7981845
  have hstable : (prefixWord ++ tailWord_7981845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981845).length < 2 ^ (prefixWord ++ tailWord_7981845).sum := by decide
  have hdescent : baseEnd_7981845 < baseStart_7981845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981852 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7981852 : Nat := 118140960795 + 7981852 * 2 ^ 59
def prefixEnd_7981852 : Nat := 4983230072969 + 3 ^ 40 * 7981852 * 2
def baseEnd_7981852 : Nat := 4098526589051010201042137

theorem tailTrace_7981852 : CollatzResearch.WordTrace tailWord_7981852 prefixEnd_7981852 4098526589051010201042137 := by
  unfold tailWord_7981852
  simp only [CollatzResearch.WordTrace]
  refine ⟨145561029539560435318733905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194081372719413913758311873 145561029539560435318733905)
  ·
    refine ⟨109170772154670326489050429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145561029539560435318733905 109170772154670326489050429)
    ·
      refine ⟨40939039558001372433393911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109170772154670326489050429 40939039558001372433393911)
      ·
        refine ⟨61408559337002058650090867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40939039558001372433393911 61408559337002058650090867)
        ·
          refine ⟨92112839005503087975136301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61408559337002058650090867 92112839005503087975136301)
          ·
            refine ⟨34542314627063657990676113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92112839005503087975136301 34542314627063657990676113)
            ·
              refine ⟨25906735970297743493007085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34542314627063657990676113 25906735970297743493007085)
              ·
                refine ⟨9715025988861653809877657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25906735970297743493007085 9715025988861653809877657)
                ·
                  refine ⟨7286269491646240357408243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9715025988861653809877657 7286269491646240357408243)
                  ·
                    refine ⟨10929404237469360536112365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7286269491646240357408243 10929404237469360536112365)
                    ·
                      refine ⟨4098526589051010201042137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10929404237469360536112365 4098526589051010201042137)
                      ·
                        rfl

theorem cell23_7981852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7981852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981852 prefixEnd_7981852 := by exact prefixLift 7981852
  have htrace : WordTrace (prefixWord ++ tailWord_7981852) baseStart_7981852 baseEnd_7981852 := by
    simpa [prefixWord, tailWord_7981852, baseEnd_7981852] using wordTrace_append hprefix tailTrace_7981852
  have hstable : (prefixWord ++ tailWord_7981852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981852).length < 2 ^ (prefixWord ++ tailWord_7981852).sum := by decide
  have hdescent : baseEnd_7981852 < baseStart_7981852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981886 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_7981886 : Nat := 118140960795 + 7981886 * 2 ^ 59
def prefixEnd_7981886 : Nat := 4983230072969 + 3 ^ 40 * 7981886 * 2
def baseEnd_7981886 : Nat := 4098544047393263068016981

theorem tailTrace_7981886 : CollatzResearch.WordTrace tailWord_7981886 prefixEnd_7981886 4098544047393263068016981 := by
  unfold tailWord_7981886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36390412395124711805525689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194082199440665129629470341 36390412395124711805525689)
  ·
    refine ⟨27292809296343533854144267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36390412395124711805525689 27292809296343533854144267)
    ·
      refine ⟨40939213944515300781216401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27292809296343533854144267 40939213944515300781216401)
      ·
        refine ⟨30704410458386475585912301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40939213944515300781216401 30704410458386475585912301)
        ·
          refine ⟨11514153921894928344717113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30704410458386475585912301 11514153921894928344717113)
          ·
            refine ⟨8635615441421196258537835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11514153921894928344717113 8635615441421196258537835)
            ·
              refine ⟨12953423162131794387806753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635615441421196258537835 12953423162131794387806753)
              ·
                refine ⟨9715067371598845790855065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12953423162131794387806753 9715067371598845790855065)
                ·
                  refine ⟨7286300528699134343141299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9715067371598845790855065 7286300528699134343141299)
                  ·
                    refine ⟨10929450793048701514711949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7286300528699134343141299 10929450793048701514711949)
                    ·
                      refine ⟨4098544047393263068016981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10929450793048701514711949 4098544047393263068016981)
                      ·
                        rfl

theorem cell23_7981886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_7981886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981886 prefixEnd_7981886 := by exact prefixLift 7981886
  have htrace : WordTrace (prefixWord ++ tailWord_7981886) baseStart_7981886 baseEnd_7981886 := by
    simpa [prefixWord, tailWord_7981886, baseEnd_7981886] using wordTrace_append hprefix tailTrace_7981886
  have hstable : (prefixWord ++ tailWord_7981886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981886).length < 2 ^ (prefixWord ++ tailWord_7981886).sum := by decide
  have hdescent : baseEnd_7981886 < baseStart_7981886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981945 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_7981945 : Nat := 118140960795 + 7981945 * 2 ^ 59
def prefixEnd_7981945 : Nat := 4983230072969 + 3 ^ 40 * 7981945 * 2
def baseEnd_7981945 : Nat := 1366191447583959445726403

theorem tailTrace_7981945 : CollatzResearch.WordTrace tailWord_7981945 prefixEnd_7981945 1366191447583959445726403 := by
  unfold tailWord_7981945
  simp only [CollatzResearch.WordTrace]
  refine ⟨291125451067783947520603289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194083634045189298347068859 291125451067783947520603289)
  ·
    refine ⟨218344088300837960640452467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291125451067783947520603289 218344088300837960640452467)
    ·
      refine ⟨327516132451256940960678701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218344088300837960640452467 327516132451256940960678701)
      ·
        refine ⟨122818549669221352860254513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327516132451256940960678701 122818549669221352860254513)
        ·
          refine ⟨92113912251916014645190885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122818549669221352860254513 92113912251916014645190885)
          ·
            refine ⟨17271358547234252745973291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92113912251916014645190885 17271358547234252745973291)
            ·
              refine ⟨25907037820851379118959937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17271358547234252745973291 25907037820851379118959937)
              ·
                refine ⟨19430278365638534339219953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25907037820851379118959937 19430278365638534339219953)
                ·
                  refine ⟨14572708774228900754414965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19430278365638534339219953 14572708774228900754414965)
                  ·
                    refine ⟨1366191447583959445726403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14572708774228900754414965 1366191447583959445726403)
                    ·
                      rfl

theorem cell23_7981945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_7981945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981945 prefixEnd_7981945 := by exact prefixLift 7981945
  have htrace : WordTrace (prefixWord ++ tailWord_7981945) baseStart_7981945 baseEnd_7981945 := by
    simpa [prefixWord, tailWord_7981945, baseEnd_7981945] using wordTrace_append hprefix tailTrace_7981945
  have hstable : (prefixWord ++ tailWord_7981945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981945).length < 2 ^ (prefixWord ++ tailWord_7981945).sum := by decide
  have hdescent : baseEnd_7981945 < baseStart_7981945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7981975 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 5, 4]
def baseStart_7981975 : Nat := 118140960795 + 7981975 * 2 ^ 59
def prefixEnd_7981975 : Nat := 4983230072969 + 3 ^ 40 * 7981975 * 2
def baseEnd_7981975 : Nat := 1366196582390504406601357

theorem tailTrace_7981975 : CollatzResearch.WordTrace tailWord_7981975 prefixEnd_7981975 1366196582390504406601357 := by
  unfold tailWord_7981975
  simp only [CollatzResearch.WordTrace]
  refine ⟨291126545257675262644195379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194084363505116841762796919 291126545257675262644195379)
  ·
    refine ⟨436689817886512893966293069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291126545257675262644195379 436689817886512893966293069)
    ·
      refine ⟨163758681707442335237359901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436689817886512893966293069 163758681707442335237359901)
      ·
        refine ⟨61409505640290875714009963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163758681707442335237359901 61409505640290875714009963)
        ·
          refine ⟨92114258460436313571014945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61409505640290875714009963 92114258460436313571014945)
          ·
            refine ⟨69085693845327235178261209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92114258460436313571014945 69085693845327235178261209)
            ·
              refine ⟨51814270383995426383695907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69085693845327235178261209 51814270383995426383695907)
              ·
                refine ⟨77721405575993139575543861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51814270383995426383695907 77721405575993139575543861)
                ·
                  refine ⟨7286381772749356835207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77721405575993139575543861 7286381772749356835207237)
                  ·
                    refine ⟨1366196582390504406601357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286381772749356835207237 1366196582390504406601357)
                    ·
                      rfl

theorem cell23_7981975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_7981975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7981975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7981975 prefixEnd_7981975 := by exact prefixLift 7981975
  have htrace : WordTrace (prefixWord ++ tailWord_7981975) baseStart_7981975 baseEnd_7981975 := by
    simpa [prefixWord, tailWord_7981975, baseEnd_7981975] using wordTrace_append hprefix tailTrace_7981975
  have hstable : (prefixWord ++ tailWord_7981975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7981975).length < 2 ^ (prefixWord ++ tailWord_7981975).sum := by decide
  have hdescent : baseEnd_7981975 < baseStart_7981975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7981975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982009 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 1, 4]
def baseStart_7982009 : Nat := 118140960795 + 7982009 * 2 ^ 59
def prefixEnd_7982009 : Nat := 4983230072969 + 3 ^ 40 * 7982009 * 2
def baseEnd_7982009 : Nat := 1366202401837922028926305

theorem tailTrace_7982009 : CollatzResearch.WordTrace tailWord_7982009 prefixEnd_7982009 1366202401837922028926305 := by
  unfold tailWord_7982009
  simp only [CollatzResearch.WordTrace]
  refine ⟨291127785339552086450933081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194085190226368057633955387 291127785339552086450933081)
  ·
    refine ⟨218345839004664064838199811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291127785339552086450933081 218345839004664064838199811)
    ·
      refine ⟨327518758506996097257299717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218345839004664064838199811 327518758506996097257299717)
      ·
        refine ⟨61409767220061768235743697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327518758506996097257299717 61409767220061768235743697)
        ·
          refine ⟨46057325415046326176807773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61409767220061768235743697 46057325415046326176807773)
          ·
            refine ⟨17271497030642372316302915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46057325415046326176807773 17271497030642372316302915)
            ·
              refine ⟨25907245545963558474454373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17271497030642372316302915 25907245545963558474454373)
              ·
                refine ⟨4857608539868167213960195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25907245545963558474454373 4857608539868167213960195)
                ·
                  refine ⟨7286412809802250820940293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857608539868167213960195 7286412809802250820940293)
                  ·
                    refine ⟨1366202401837922028926305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286412809802250820940293 1366202401837922028926305)
                    ·
                      rfl

theorem cell23_7982009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 4].length) (baseStart_7982009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982009 prefixEnd_7982009 := by exact prefixLift 7982009
  have htrace : WordTrace (prefixWord ++ tailWord_7982009) baseStart_7982009 baseEnd_7982009 := by
    simpa [prefixWord, tailWord_7982009, baseEnd_7982009] using wordTrace_append hprefix tailTrace_7982009
  have hstable : (prefixWord ++ tailWord_7982009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982009).length < 2 ^ (prefixWord ++ tailWord_7982009).sum := by decide
  have hdescent : baseEnd_7982009 < baseStart_7982009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982085 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_7982085 : Nat := 118140960795 + 7982085 * 2 ^ 59
def prefixEnd_7982085 : Nat := 4983230072969 + 3 ^ 40 * 7982085 * 2
def baseEnd_7982085 : Nat := 4098646230043507789428565

theorem tailTrace_7982085 : CollatzResearch.WordTrace tailWord_7982085 prefixEnd_7982085 4098646230043507789428565 := by
  unfold tailWord_7982085
  simp only [CollatzResearch.WordTrace]
  refine ⟨291130557287276751430699709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194087038191517834287133139 291130557287276751430699709)
  ·
    refine ⟨109173958982728781786512391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291130557287276751430699709 109173958982728781786512391)
    ·
      refine ⟨163760938474093172679768587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109173958982728781786512391 163760938474093172679768587)
      ·
        refine ⟨245641407711139759019652881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163760938474093172679768587 245641407711139759019652881)
        ·
          refine ⟨184231055783354819264739661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245641407711139759019652881 184231055783354819264739661)
          ·
            refine ⟨69086645918758057224277373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184231055783354819264739661 69086645918758057224277373)
            ·
              refine ⟨25907492219534271459104015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69086645918758057224277373 25907492219534271459104015)
              ·
                refine ⟨38861238329301407188656023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25907492219534271459104015 38861238329301407188656023)
                ·
                  refine ⟨58291857493952110782984035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38861238329301407188656023 58291857493952110782984035)
                  ·
                    refine ⟨87437786240928166174476053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58291857493952110782984035 87437786240928166174476053)
                    ·
                      refine ⟨4098646230043507789428565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87437786240928166174476053 4098646230043507789428565)
                      ·
                        rfl

theorem cell23_7982085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_7982085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982085 prefixEnd_7982085 := by exact prefixLift 7982085
  have htrace : WordTrace (prefixWord ++ tailWord_7982085) baseStart_7982085 baseEnd_7982085 := by
    simpa [prefixWord, tailWord_7982085, baseEnd_7982085] using wordTrace_append hprefix tailTrace_7982085
  have hstable : (prefixWord ++ tailWord_7982085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982085).length < 2 ^ (prefixWord ++ tailWord_7982085).sum := by decide
  have hdescent : baseEnd_7982085 < baseStart_7982085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982109 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_7982109 : Nat := 118140960795 + 7982109 * 2 ^ 59
def prefixEnd_7982109 : Nat := 4983230072969 + 3 ^ 40 * 7982109 * 2
def baseEnd_7982109 : Nat := 4098658553579215695528455

theorem tailTrace_7982109 : CollatzResearch.WordTrace tailWord_7982109 prefixEnd_7982109 4098658553579215695528455 := by
  unfold tailWord_7982109
  simp only [CollatzResearch.WordTrace]
  refine ⟨291131432639189803529573381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194087621759459869019715587 291131432639189803529573381)
  ·
    refine ⟨54587143619848088161795009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291131432639189803529573381 54587143619848088161795009)
    ·
      refine ⟨40940357714886066121346257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54587143619848088161795009 40940357714886066121346257)
      ·
        refine ⟨30705268286164549591009693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40940357714886066121346257 30705268286164549591009693)
        ·
          refine ⟨11514475607311706096628635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30705268286164549591009693 11514475607311706096628635)
          ·
            refine ⟨17271713410967559144942953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11514475607311706096628635 17271713410967559144942953)
            ·
              refine ⟨12953785058225669358707215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17271713410967559144942953 12953785058225669358707215)
              ·
                refine ⟨19430677587338504038060823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12953785058225669358707215 19430677587338504038060823)
                ·
                  refine ⟨29146016381007756057091235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19430677587338504038060823 29146016381007756057091235)
                  ·
                    refine ⟨43719024571511634085636853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29146016381007756057091235 43719024571511634085636853)
                    ·
                      refine ⟨4098658553579215695528455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43719024571511634085636853 4098658553579215695528455)
                      ·
                        rfl

theorem cell23_7982109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_7982109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982109 prefixEnd_7982109 := by exact prefixLift 7982109
  have htrace : WordTrace (prefixWord ++ tailWord_7982109) baseStart_7982109 baseEnd_7982109 := by
    simpa [prefixWord, tailWord_7982109, baseEnd_7982109] using wordTrace_append hprefix tailTrace_7982109
  have hstable : (prefixWord ++ tailWord_7982109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982109).length < 2 ^ (prefixWord ++ tailWord_7982109).sum := by decide
  have hdescent : baseEnd_7982109 < baseStart_7982109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982123 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 1, 2, 2]
def baseStart_7982123 : Nat := 118140960795 + 7982123 * 2 ^ 59
def prefixEnd_7982123 : Nat := 4983230072969 + 3 ^ 40 * 7982123 * 2
def baseEnd_7982123 : Nat := 4098665742308378640753391

theorem tailTrace_7982123 : CollatzResearch.WordTrace tailWord_7982123 prefixEnd_7982123 4098665742308378640753391 := by
  unfold tailWord_7982123
  simp only [CollatzResearch.WordTrace]
  refine ⟨291131943261139083920583023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194087962174092722613722015 291131943261139083920583023)
  ·
    refine ⟨436697914891708625880874535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291131943261139083920583023 436697914891708625880874535)
    ·
      refine ⟨655046872337562938821311803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436697914891708625880874535 655046872337562938821311803)
      ·
        refine ⟨982570308506344408231967705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655046872337562938821311803 982570308506344408231967705)
        ·
          refine ⟨736927731379758306173975779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982570308506344408231967705 736927731379758306173975779)
          ·
            refine ⟨1105391597069637459260963669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736927731379758306173975779 1105391597069637459260963669)
            ·
              refine ⟨6476903889079906987857209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1105391597069637459260963669 6476903889079906987857209)
              ·
                refine ⟨4857677916809930240892907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476903889079906987857209 4857677916809930240892907)
                ·
                  refine ⟨7286516875214895361339361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857677916809930240892907 7286516875214895361339361)
                  ·
                    refine ⟨5464887656411171521004521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7286516875214895361339361 5464887656411171521004521)
                    ·
                      refine ⟨4098665742308378640753391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464887656411171521004521 4098665742308378640753391)
                      ·
                        rfl

theorem cell23_7982123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 2, 2].length) (baseStart_7982123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982123 prefixEnd_7982123 := by exact prefixLift 7982123
  have htrace : WordTrace (prefixWord ++ tailWord_7982123) baseStart_7982123 baseEnd_7982123 := by
    simpa [prefixWord, tailWord_7982123, baseEnd_7982123] using wordTrace_append hprefix tailTrace_7982123
  have hstable : (prefixWord ++ tailWord_7982123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982123).length < 2 ^ (prefixWord ++ tailWord_7982123).sum := by decide
  have hdescent : baseEnd_7982123 < baseStart_7982123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982172 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7982172 : Nat := 118140960795 + 7982172 * 2 ^ 59
def prefixEnd_7982172 : Nat := 4983230072969 + 3 ^ 40 * 7982172 * 2
def baseEnd_7982172 : Nat := 1366230300953482983013555

theorem tailTrace_7982172 : CollatzResearch.WordTrace tailWord_7982172 prefixEnd_7982172 1366230300953482983013555 := by
  unfold tailWord_7982172
  simp only [CollatzResearch.WordTrace]
  refine ⟨145566865218980782644558385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194089153625307710192744513 145566865218980782644558385)
  ·
    refine ⟨109175148914235586983418789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145566865218980782644558385 109175148914235586983418789)
    ·
      refine ⟨20470340421419172559391023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109175148914235586983418789 20470340421419172559391023)
      ·
        refine ⟨30705510632128758839086535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20470340421419172559391023 30705510632128758839086535)
        ·
          refine ⟨46058265948193138258629803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30705510632128758839086535 46058265948193138258629803)
          ·
            refine ⟨69087398922289707387944705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46058265948193138258629803 69087398922289707387944705)
            ·
              refine ⟨51815549191717280540958529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69087398922289707387944705 51815549191717280540958529)
              ·
                refine ⟨38861661893787960405718897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51815549191717280540958529 38861661893787960405718897)
                ·
                  refine ⟨29146246420340970304289173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38861661893787960405718897 29146246420340970304289173)
                  ·
                    refine ⟨1366230300953482983013555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29146246420340970304289173 1366230300953482983013555)
                    ·
                      rfl

theorem cell23_7982172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7982172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982172 prefixEnd_7982172 := by exact prefixLift 7982172
  have htrace : WordTrace (prefixWord ++ tailWord_7982172) baseStart_7982172 baseEnd_7982172 := by
    simpa [prefixWord, tailWord_7982172, baseEnd_7982172] using wordTrace_append hprefix tailTrace_7982172
  have hstable : (prefixWord ++ tailWord_7982172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982172).length < 2 ^ (prefixWord ++ tailWord_7982172).sum := by decide
  have hdescent : baseEnd_7982172 < baseStart_7982172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982174 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7982174 : Nat := 118140960795 + 7982174 * 2 ^ 59
def prefixEnd_7982174 : Nat := 4983230072969 + 3 ^ 40 * 7982174 * 2
def baseEnd_7982174 : Nat := 4098691929821757941215657

theorem tailTrace_7982174 : CollatzResearch.WordTrace tailWord_7982174 prefixEnd_7982174 4098691929821757941215657 := by
  unfold tailWord_7982174
  simp only [CollatzResearch.WordTrace]
  refine ⟨36391725422994289953836197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194089202255969546420459717 36391725422994289953836197)
  ·
    refine ⟨6823448516811429366344287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36391725422994289953836197 6823448516811429366344287)
    ·
      refine ⟨10235172775217144049516431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823448516811429366344287 10235172775217144049516431)
      ·
        refine ⟨15352759162825716074274647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235172775217144049516431 15352759162825716074274647)
        ·
          refine ⟨23029138744238574111411971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15352759162825716074274647 23029138744238574111411971)
          ·
            refine ⟨34543708116357861167117957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23029138744238574111411971 34543708116357861167117957)
            ·
              refine ⟨6476945271817098968834617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34543708116357861167117957 6476945271817098968834617)
              ·
                refine ⟨4857708953862824226625963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476945271817098968834617 4857708953862824226625963)
                ·
                  refine ⟨7286563430794236339938945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857708953862824226625963 7286563430794236339938945)
                  ·
                    refine ⟨5464922573095677254954209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7286563430794236339938945 5464922573095677254954209)
                    ·
                      refine ⟨4098691929821757941215657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464922573095677254954209 4098691929821757941215657)
                      ·
                        rfl

theorem cell23_7982174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7982174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982174 prefixEnd_7982174 := by exact prefixLift 7982174
  have htrace : WordTrace (prefixWord ++ tailWord_7982174) baseStart_7982174 baseEnd_7982174 := by
    simpa [prefixWord, tailWord_7982174, baseEnd_7982174] using wordTrace_append hprefix tailTrace_7982174
  have hstable : (prefixWord ++ tailWord_7982174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982174).length < 2 ^ (prefixWord ++ tailWord_7982174).sum := by decide
  have hdescent : baseEnd_7982174 < baseStart_7982174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982192 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_7982192 : Nat := 118140960795 + 7982192 * 2 ^ 59
def prefixEnd_7982192 : Nat := 4983230072969 + 3 ^ 40 * 7982192 * 2
def baseEnd_7982192 : Nat := 4098701172473538870790573

theorem tailTrace_7982192 : CollatzResearch.WordTrace tailWord_7982192 prefixEnd_7982192 4098701172473538870790573 := by
  unfold tailWord_7982192
  simp only [CollatzResearch.WordTrace]
  refine ⟨145567229948944554352422415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194089639931926072469896553 145567229948944554352422415)
  ·
    refine ⟨218350844923416831528633623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145567229948944554352422415 218350844923416831528633623)
    ·
      refine ⟨327526267385125247292950435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218350844923416831528633623 327526267385125247292950435)
      ·
        refine ⟨491289401077687870939425653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327526267385125247292950435 491289401077687870939425653)
        ·
          refine ⟨46058381351033237900571155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491289401077687870939425653 46058381351033237900571155)
          ·
            refine ⟨69087572026549856850856733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46058381351033237900571155 69087572026549856850856733)
            ·
              refine ⟨25907839509956196319071275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69087572026549856850856733 25907839509956196319071275)
              ·
                refine ⟨38861759264934294478606913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25907839509956196319071275 38861759264934294478606913)
                ·
                  refine ⟨29146319448700720858955185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38861759264934294478606913 29146319448700720858955185)
                  ·
                    refine ⟨21859739586525540644216389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29146319448700720858955185 21859739586525540644216389)
                    ·
                      refine ⟨4098701172473538870790573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21859739586525540644216389 4098701172473538870790573)
                      ·
                        rfl

theorem cell23_7982192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_7982192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982192 prefixEnd_7982192 := by exact prefixLift 7982192
  have htrace : WordTrace (prefixWord ++ tailWord_7982192) baseStart_7982192 baseEnd_7982192 := by
    simpa [prefixWord, tailWord_7982192, baseEnd_7982192] using wordTrace_append hprefix tailTrace_7982192
  have hstable : (prefixWord ++ tailWord_7982192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982192).length < 2 ^ (prefixWord ++ tailWord_7982192).sum := by decide
  have hdescent : baseEnd_7982192 < baseStart_7982192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982235 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_7982235 : Nat := 118140960795 + 7982235 * 2 ^ 59
def prefixEnd_7982235 : Nat := 4983230072969 + 3 ^ 40 * 7982235 * 2
def baseEnd_7982235 : Nat := 4098723252141682202552875

theorem tailTrace_7982235 : CollatzResearch.WordTrace tailWord_7982235 prefixEnd_7982235 4098723252141682202552875 := by
  unfold tailWord_7982235
  simp only [CollatzResearch.WordTrace]
  refine ⟨291136028236733327048660159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194090685491155551365773439 291136028236733327048660159)
  ·
    refine ⟨436704042355099990572990239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291136028236733327048660159 436704042355099990572990239)
    ·
      refine ⟨655056063532649985859485359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436704042355099990572990239 655056063532649985859485359)
      ·
        refine ⟨982584095298974978789228039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655056063532649985859485359 982584095298974978789228039)
        ·
          refine ⟨1473876142948462468183842059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982584095298974978789228039 1473876142948462468183842059)
          ·
            refine ⟨2210814214422693702275763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473876142948462468183842059 2210814214422693702275763089)
            ·
              refine ⟨1658110660817020276706822317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210814214422693702275763089 1658110660817020276706822317)
              ·
                refine ⟨621791497806382603765058369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1658110660817020276706822317 621791497806382603765058369)
                ·
                  refine ⟨466343623354786952823793777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621791497806382603765058369 466343623354786952823793777)
                  ·
                    refine ⟨349757717516090214617845333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466343623354786952823793777 349757717516090214617845333)
                    ·
                      refine ⟨4098723252141682202552875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 349757717516090214617845333 4098723252141682202552875)
                      ·
                        rfl

theorem cell23_7982235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_7982235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982235 prefixEnd_7982235 := by exact prefixLift 7982235
  have htrace : WordTrace (prefixWord ++ tailWord_7982235) baseStart_7982235 baseEnd_7982235 := by
    simpa [prefixWord, tailWord_7982235, baseEnd_7982235] using wordTrace_append hprefix tailTrace_7982235
  have hstable : (prefixWord ++ tailWord_7982235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982235).length < 2 ^ (prefixWord ++ tailWord_7982235).sum := by decide
  have hdescent : baseEnd_7982235 < baseStart_7982235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982252 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_7982252 : Nat := 118140960795 + 7982252 * 2 ^ 59
def prefixEnd_7982252 : Nat := 4983230072969 + 3 ^ 40 * 7982252 * 2
def baseEnd_7982252 : Nat := 4098731981312808636040297

theorem tailTrace_7982252 : CollatzResearch.WordTrace tailWord_7982252 prefixEnd_7982252 4098731981312808636040297 := by
  unfold tailWord_7982252
  simp only [CollatzResearch.WordTrace]
  refine ⟨145568324138835869476014505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194091098851781159301352673 145568324138835869476014505)
  ·
    refine ⟨109176243104126902107010879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145568324138835869476014505 109176243104126902107010879)
    ·
      refine ⟨163764364656190353160516319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109176243104126902107010879 163764364656190353160516319)
      ·
        refine ⟨245646546984285529740774479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163764364656190353160516319 245646546984285529740774479)
        ·
          refine ⟨368469820476428294611161719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245646546984285529740774479 368469820476428294611161719)
          ·
            refine ⟨552704730714642441916742579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368469820476428294611161719 552704730714642441916742579)
            ·
              refine ⟨829057096071963662875113869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552704730714642441916742579 829057096071963662875113869)
              ·
                refine ⟨310896411026986373578167701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829057096071963662875113869 310896411026986373578167701)
                ·
                  refine ⟨14573269266889986261476611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310896411026986373578167701 14573269266889986261476611)
                  ·
                    refine ⟨21859903900334979392214917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14573269266889986261476611 21859903900334979392214917)
                    ·
                      refine ⟨4098731981312808636040297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21859903900334979392214917 4098731981312808636040297)
                      ·
                        rfl

theorem cell23_7982252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_7982252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982252 prefixEnd_7982252 := by exact prefixLift 7982252
  have htrace : WordTrace (prefixWord ++ tailWord_7982252) baseStart_7982252 baseEnd_7982252 := by
    simpa [prefixWord, tailWord_7982252, baseEnd_7982252] using wordTrace_append hprefix tailTrace_7982252
  have hstable : (prefixWord ++ tailWord_7982252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982252).length < 2 ^ (prefixWord ++ tailWord_7982252).sum := by decide
  have hdescent : baseEnd_7982252 < baseStart_7982252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982269 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_7982269 : Nat := 118140960795 + 7982269 * 2 ^ 59
def prefixEnd_7982269 : Nat := 4983230072969 + 3 ^ 40 * 7982269 * 2
def baseEnd_7982269 : Nat := 4098740710483935069527719

theorem tailTrace_7982269 : CollatzResearch.WordTrace tailWord_7982269 prefixEnd_7982269 4098740710483935069527719 := by
  unfold tailWord_7982269
  simp only [CollatzResearch.WordTrace]
  refine ⟨291137268318610150855397861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194091512212406767236931907 291137268318610150855397861)
  ·
    refine ⟨54588237809739403285387099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291137268318610150855397861 54588237809739403285387099)
    ·
      refine ⟨81882356714609104928080649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54588237809739403285387099 81882356714609104928080649)
      ·
        refine ⟨61411767535956828696060487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81882356714609104928080649 61411767535956828696060487)
        ·
          refine ⟨92117651303935243044090731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61411767535956828696060487 92117651303935243044090731)
          ·
            refine ⟨138176476955902864566136097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92117651303935243044090731 138176476955902864566136097)
            ·
              refine ⟨103632357716927148424602073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138176476955902864566136097 103632357716927148424602073)
              ·
                refine ⟨77724268287695361318451555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103632357716927148424602073 77724268287695361318451555)
                ·
                  refine ⟨116586402431543041977677333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77724268287695361318451555 116586402431543041977677333)
                  ·
                    refine ⟨5464987613978580092703625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116586402431543041977677333 5464987613978580092703625)
                    ·
                      refine ⟨4098740710483935069527719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5464987613978580092703625 4098740710483935069527719)
                      ·
                        rfl

theorem cell23_7982269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_7982269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982269 prefixEnd_7982269 := by exact prefixLift 7982269
  have htrace : WordTrace (prefixWord ++ tailWord_7982269) baseStart_7982269 baseEnd_7982269 := by
    simpa [prefixWord, tailWord_7982269, baseEnd_7982269] using wordTrace_append hprefix tailTrace_7982269
  have hstable : (prefixWord ++ tailWord_7982269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982269).length < 2 ^ (prefixWord ++ tailWord_7982269).sum := by decide
  have hdescent : baseEnd_7982269 < baseStart_7982269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982286 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_7982286 : Nat := 118140960795 + 7982286 * 2 ^ 59
def prefixEnd_7982286 : Nat := 4983230072969 + 3 ^ 40 * 7982286 * 2
def baseEnd_7982286 : Nat := 4098749439655061503015141

theorem tailTrace_7982286 : CollatzResearch.WordTrace tailWord_7982286 prefixEnd_7982286 4098749439655061503015141 := by
  unfold tailWord_7982286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36392236044943570344845839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194091925573032375172511141 36392236044943570344845839)
  ·
    refine ⟨54588354067415355517268759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36392236044943570344845839 54588354067415355517268759)
    ·
      refine ⟨81882531101123033275903139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54588354067415355517268759 81882531101123033275903139)
      ·
        refine ⟨122823796651684549913854709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81882531101123033275903139 122823796651684549913854709)
        ·
          refine ⟨11514730936095426554423879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122823796651684549913854709 11514730936095426554423879)
          ·
            refine ⟨17272096404143139831635819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11514730936095426554423879 17272096404143139831635819)
            ·
              refine ⟨25908144606214709747453729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17272096404143139831635819 25908144606214709747453729)
              ·
                refine ⟨19431108454661032310590297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25908144606214709747453729 19431108454661032310590297)
                ·
                  refine ⟨14573331340995774232942723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19431108454661032310590297 14573331340995774232942723)
                  ·
                    refine ⟨21859997011493661349414085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14573331340995774232942723 21859997011493661349414085)
                    ·
                      refine ⟨4098749439655061503015141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21859997011493661349414085 4098749439655061503015141)
                      ·
                        rfl

theorem cell23_7982286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_7982286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982286 prefixEnd_7982286 := by exact prefixLift 7982286
  have htrace : WordTrace (prefixWord ++ tailWord_7982286) baseStart_7982286 baseEnd_7982286 := by
    simpa [prefixWord, tailWord_7982286, baseEnd_7982286] using wordTrace_append hprefix tailTrace_7982286
  have hstable : (prefixWord ++ tailWord_7982286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982286).length < 2 ^ (prefixWord ++ tailWord_7982286).sum := by decide
  have hdescent : baseEnd_7982286 < baseStart_7982286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982353 : List Nat := [1, 2, 2, 1, 1, 4, 3, 4, 1, 1, 3]
def baseStart_7982353 : Nat := 118140960795 + 7982353 * 2 ^ 59
def prefixEnd_7982353 : Nat := 4983230072969 + 3 ^ 40 * 7982353 * 2
def baseEnd_7982353 : Nat := 4098783842858912740877333

theorem tailTrace_7982353 : CollatzResearch.WordTrace tailWord_7982353 prefixEnd_7982353 4098783842858912740877333 := by
  unfold tailWord_7982353
  simp only [CollatzResearch.WordTrace]
  refine ⟨291140332050305833201455713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194093554700203888800970475 291140332050305833201455713)
  ·
    refine ⟨218355249037729374901091785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291140332050305833201455713 218355249037729374901091785)
    ·
      refine ⟨163766436778297031175818839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218355249037729374901091785 163766436778297031175818839)
      ·
        refine ⟨245649655167445546763728259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163766436778297031175818839 245649655167445546763728259)
        ·
          refine ⟨368474482751168320145592389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245649655167445546763728259 368474482751168320145592389)
          ·
            refine ⟨69088965515844060027298573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368474482751168320145592389 69088965515844060027298573)
            ·
              refine ⟨25908362068441522510236965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69088965515844060027298573 25908362068441522510236965)
              ·
                refine ⟨4857817887832785470669431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25908362068441522510236965 4857817887832785470669431)
                ·
                  refine ⟨7286726831749178206004147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857817887832785470669431 7286726831749178206004147)
                  ·
                    refine ⟨10930090247623767309006221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7286726831749178206004147 10930090247623767309006221)
                    ·
                      refine ⟨4098783842858912740877333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930090247623767309006221 4098783842858912740877333)
                      ·
                        rfl

theorem cell23_7982353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_7982353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982353 prefixEnd_7982353 := by exact prefixLift 7982353
  have htrace : WordTrace (prefixWord ++ tailWord_7982353) baseStart_7982353 baseEnd_7982353 := by
    simpa [prefixWord, tailWord_7982353, baseEnd_7982353] using wordTrace_append hprefix tailTrace_7982353
  have hstable : (prefixWord ++ tailWord_7982353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982353).length < 2 ^ (prefixWord ++ tailWord_7982353).sum := by decide
  have hdescent : baseEnd_7982353 < baseStart_7982353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982359 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7982359 : Nat := 118140960795 + 7982359 * 2 ^ 59
def prefixEnd_7982359 : Nat := 4983230072969 + 3 ^ 40 * 7982359 * 2
def baseEnd_7982359 : Nat := 4098786923742839717402305

theorem tailTrace_7982359 : CollatzResearch.WordTrace tailWord_7982359 prefixEnd_7982359 4098786923742839717402305 := by
  unfold tailWord_7982359
  simp only [CollatzResearch.WordTrace]
  refine ⟨291140550888284096226174131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194093700592189397484116087 291140550888284096226174131)
  ·
    refine ⟨436710826332426144339261197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291140550888284096226174131 436710826332426144339261197)
    ·
      refine ⟨163766559874659804127222949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436710826332426144339261197 163766559874659804127222949)
      ·
        refine ⟨30706229976498713273854303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163766559874659804127222949 30706229976498713273854303)
        ·
          refine ⟨46059344964748069910781455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30706229976498713273854303 46059344964748069910781455)
          ·
            refine ⟨69089017447122104866172183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46059344964748069910781455 69089017447122104866172183)
            ·
              refine ⟨103633526170683157299258275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69089017447122104866172183 103633526170683157299258275)
              ·
                refine ⟨155450289256024735948887413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103633526170683157299258275 155450289256024735948887413)
                ·
                  refine ⟨14573464617752318995208195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155450289256024735948887413 14573464617752318995208195)
                  ·
                    refine ⟨21860196926628478492812293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14573464617752318995208195 21860196926628478492812293)
                    ·
                      refine ⟨4098786923742839717402305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21860196926628478492812293 4098786923742839717402305)
                      ·
                        rfl

theorem cell23_7982359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7982359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982359 prefixEnd_7982359 := by exact prefixLift 7982359
  have htrace : WordTrace (prefixWord ++ tailWord_7982359) baseStart_7982359 baseEnd_7982359 := by
    simpa [prefixWord, tailWord_7982359, baseEnd_7982359] using wordTrace_append hprefix tailTrace_7982359
  have hstable : (prefixWord ++ tailWord_7982359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982359).length < 2 ^ (prefixWord ++ tailWord_7982359).sum := by decide
  have hdescent : baseEnd_7982359 < baseStart_7982359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982369 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_7982369 : Nat := 118140960795 + 7982369 * 2 ^ 59
def prefixEnd_7982369 : Nat := 4983230072969 + 3 ^ 40 * 7982369 * 2
def baseEnd_7982369 : Nat := 1366264019516461559425753

theorem tailTrace_7982369 : CollatzResearch.WordTrace tailWord_7982369 prefixEnd_7982369 1366264019516461559425753 := by
  unfold tailWord_7982369
  simp only [CollatzResearch.WordTrace]
  refine ⟨291140915618247867934038161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194093943745498578622692107 291140915618247867934038161)
  ·
    refine ⟨218355686713685900950528621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291140915618247867934038161 218355686713685900950528621)
    ·
      refine ⟨81883382517632212856448233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218355686713685900950528621 81883382517632212856448233)
      ·
        refine ⟨61412536888224159642336175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81883382517632212856448233 61412536888224159642336175)
        ·
          refine ⟨92118805332336239463504263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61412536888224159642336175 92118805332336239463504263)
          ·
            refine ⟨138178207998504359195256395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92118805332336239463504263 138178207998504359195256395)
            ·
              refine ⟨207267311997756538792884593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138178207998504359195256395 207267311997756538792884593)
              ·
                refine ⟨155450483998317404094663445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207267311997756538792884593 155450483998317404094663445)
                ·
                  refine ⟨7286741437421128316937349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155450483998317404094663445 7286741437421128316937349)
                  ·
                    refine ⟨1366264019516461559425753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286741437421128316937349 1366264019516461559425753)
                    ·
                      rfl

theorem cell23_7982369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_7982369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982369 prefixEnd_7982369 := by exact prefixLift 7982369
  have htrace : WordTrace (prefixWord ++ tailWord_7982369) baseStart_7982369 baseEnd_7982369 := by
    simpa [prefixWord, tailWord_7982369, baseEnd_7982369] using wordTrace_append hprefix tailTrace_7982369
  have hstable : (prefixWord ++ tailWord_7982369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982369).length < 2 ^ (prefixWord ++ tailWord_7982369).sum := by decide
  have hdescent : baseEnd_7982369 < baseStart_7982369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982376 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7982376 : Nat := 118140960795 + 7982376 * 2 ^ 59
def prefixEnd_7982376 : Nat := 4983230072969 + 3 ^ 40 * 7982376 * 2
def baseEnd_7982376 : Nat := 4098795652913966150889727

theorem tailTrace_7982376 : CollatzResearch.WordTrace tailWord_7982376 prefixEnd_7982376 4098795652913966150889727 := by
  unfold tailWord_7982376
  simp only [CollatzResearch.WordTrace]
  refine ⟨145570585464611254064771491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194094113952815005419695321 145570585464611254064771491)
  ·
    refine ⟨218355878196916881097157237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145570585464611254064771491 218355878196916881097157237)
    ·
      refine ⟨20470863580960957602858491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218355878196916881097157237 20470863580960957602858491)
      ·
        refine ⟨30706295371441436404287737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20470863580960957602858491 30706295371441436404287737)
        ·
          refine ⟨23029721528581077303215803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30706295371441436404287737 23029721528581077303215803)
          ·
            refine ⟨34544582292871615954823705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23029721528581077303215803 34544582292871615954823705)
            ·
              refine ⟨25908436719653711966117779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34544582292871615954823705 25908436719653711966117779)
              ·
                refine ⟨38862655079480567949176669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25908436719653711966117779 38862655079480567949176669)
                ·
                  refine ⟨14573495654805212980941251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38862655079480567949176669 14573495654805212980941251)
                  ·
                    refine ⟨21860243482207819471411877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14573495654805212980941251 21860243482207819471411877)
                    ·
                      refine ⟨4098795652913966150889727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21860243482207819471411877 4098795652913966150889727)
                      ·
                        rfl

theorem cell23_7982376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7982376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982376 prefixEnd_7982376 := by exact prefixLift 7982376
  have htrace : WordTrace (prefixWord ++ tailWord_7982376) baseStart_7982376 baseEnd_7982376 := by
    simpa [prefixWord, tailWord_7982376, baseEnd_7982376] using wordTrace_append hprefix tailTrace_7982376
  have hstable : (prefixWord ++ tailWord_7982376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982376).length < 2 ^ (prefixWord ++ tailWord_7982376).sum := by decide
  have hdescent : baseEnd_7982376 < baseStart_7982376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982390 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7982390 : Nat := 118140960795 + 7982390 * 2 ^ 59
def prefixEnd_7982390 : Nat := 4983230072969 + 3 ^ 40 * 7982390 * 2
def baseEnd_7982390 : Nat := 1366267613881043032038221

theorem tailTrace_7982390 : CollatzResearch.WordTrace tailWord_7982390 prefixEnd_7982390 1366267613881043032038221 := by
  unfold tailWord_7982390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196355096948236782534539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194094454367447859013701749 18196355096948236782534539)
  ·
    refine ⟨27294532645422355173801809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196355096948236782534539 27294532645422355173801809)
    ·
      refine ⟨20470899484066766380351357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27294532645422355173801809 20470899484066766380351357)
      ·
        refine ⟨7676587306525037392631759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20470899484066766380351357 7676587306525037392631759)
        ·
          refine ⟨11514880959787556088947639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676587306525037392631759 11514880959787556088947639)
          ·
            refine ⟨17272321439681334133421459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11514880959787556088947639 17272321439681334133421459)
            ·
              refine ⟨25908482159522001200132189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17272321439681334133421459 25908482159522001200132189)
              ·
                refine ⟨9715680809820750450049571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25908482159522001200132189 9715680809820750450049571)
                ·
                  refine ⟨14573521214731125675074357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9715680809820750450049571 14573521214731125675074357)
                  ·
                    refine ⟨1366267613881043032038221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14573521214731125675074357 1366267613881043032038221)
                    ·
                      rfl

theorem cell23_7982390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7982390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982390 prefixEnd_7982390 := by exact prefixLift 7982390
  have htrace : WordTrace (prefixWord ++ tailWord_7982390) baseStart_7982390 baseEnd_7982390 := by
    simpa [prefixWord, tailWord_7982390, baseEnd_7982390] using wordTrace_append hprefix tailTrace_7982390
  have hstable : (prefixWord ++ tailWord_7982390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982390).length < 2 ^ (prefixWord ++ tailWord_7982390).sum := by decide
  have hdescent : baseEnd_7982390 < baseStart_7982390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982393 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7982393 : Nat := 118140960795 + 7982393 * 2 ^ 59
def prefixEnd_7982393 : Nat := 4983230072969 + 3 ^ 40 * 7982393 * 2
def baseEnd_7982393 : Nat := 4098804382085092584377149

theorem tailTrace_7982393 : CollatzResearch.WordTrace tailWord_7982393 prefixEnd_7982393 4098804382085092584377149 := by
  unfold tailWord_7982393
  simp only [CollatzResearch.WordTrace]
  refine ⟨291141790970160920032911833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194094527313440613355274555 291141790970160920032911833)
  ·
    refine ⟨218356343227620690024683875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291141790970160920032911833 218356343227620690024683875)
    ·
      refine ⟨327534514841431035037025813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218356343227620690024683875 327534514841431035037025813)
      ·
        refine ⟨15353180383192079767360585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 327534514841431035037025813 15353180383192079767360585)
        ·
          refine ⟨11514885287394059825520439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15353180383192079767360585 11514885287394059825520439)
          ·
            refine ⟨17272327931091089738280659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11514885287394059825520439 17272327931091089738280659)
            ·
              refine ⟨25908491896636634607420989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17272327931091089738280659 25908491896636634607420989)
              ·
                refine ⟨9715684461238737977782871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25908491896636634607420989 9715684461238737977782871)
                ·
                  refine ⟨14573526691858106966674307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9715684461238737977782871 14573526691858106966674307)
                  ·
                    refine ⟨21860290037787160450011461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14573526691858106966674307 21860290037787160450011461)
                    ·
                      refine ⟨4098804382085092584377149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21860290037787160450011461 4098804382085092584377149)
                      ·
                        rfl

theorem cell23_7982393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7982393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982393 prefixEnd_7982393 := by exact prefixLift 7982393
  have htrace : WordTrace (prefixWord ++ tailWord_7982393) baseStart_7982393 baseEnd_7982393 := by
    simpa [prefixWord, tailWord_7982393, baseEnd_7982393] using wordTrace_append hprefix tailTrace_7982393
  have hstable : (prefixWord ++ tailWord_7982393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982393).length < 2 ^ (prefixWord ++ tailWord_7982393).sum := by decide
  have hdescent : baseEnd_7982393 < baseStart_7982393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982409 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_7982409 : Nat := 118140960795 + 7982409 * 2 ^ 59
def prefixEnd_7982409 : Nat := 4983230072969 + 3 ^ 40 * 7982409 * 2
def baseEnd_7982409 : Nat := 4098812597775564521777075

theorem tailTrace_7982409 : CollatzResearch.WordTrace tailWord_7982409 prefixEnd_7982409 4098812597775564521777075 := by
  unfold tailWord_7982409
  simp only [CollatzResearch.WordTrace]
  refine ⟨291142374538102954765494281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194094916358735303176996187 291142374538102954765494281)
  ·
    refine ⟨218356780903577216074120711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291142374538102954765494281 218356780903577216074120711)
    ·
      refine ⟨327535171355365824111181067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218356780903577216074120711 327535171355365824111181067)
      ·
        refine ⟨491302757033048736166771601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327535171355365824111181067 491302757033048736166771601)
        ·
          refine ⟨368477067774786552125078701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491302757033048736166771601 368477067774786552125078701)
          ·
            refine ⟨138178900415544957046904513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368477067774786552125078701 138178900415544957046904513)
            ·
              refine ⟨103634175311658717785178385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138178900415544957046904513 103634175311658717785178385)
              ·
                refine ⟨77725631483744038338883789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103634175311658717785178385 77725631483744038338883789)
                ·
                  refine ⟨29147111806404014377081421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77725631483744038338883789 29147111806404014377081421)
                  ·
                    refine ⟨10930166927401505391405533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29147111806404014377081421 10930166927401505391405533)
                    ·
                      refine ⟨4098812597775564521777075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930166927401505391405533 4098812597775564521777075)
                      ·
                        rfl

theorem cell23_7982409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_7982409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982409 prefixEnd_7982409 := by exact prefixLift 7982409
  have htrace : WordTrace (prefixWord ++ tailWord_7982409) baseStart_7982409 baseEnd_7982409 := by
    simpa [prefixWord, tailWord_7982409, baseEnd_7982409] using wordTrace_append hprefix tailTrace_7982409
  have hstable : (prefixWord ++ tailWord_7982409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982409).length < 2 ^ (prefixWord ++ tailWord_7982409).sum := by decide
  have hdescent : baseEnd_7982409 < baseStart_7982409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982426 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_7982426 : Nat := 118140960795 + 7982426 * 2 ^ 59
def prefixEnd_7982426 : Nat := 4983230072969 + 3 ^ 40 * 7982426 * 2
def baseEnd_7982426 : Nat := 4098821326946690955264497

theorem tailTrace_7982426 : CollatzResearch.WordTrace tailWord_7982426 prefixEnd_7982426 4098821326946690955264497 := by
  unfold tailWord_7982426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72785748644760341667215783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194095329719360911112575421 72785748644760341667215783)
  ·
    refine ⟨109178622967140512500823675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72785748644760341667215783 109178622967140512500823675)
    ·
      refine ⟨163767934450710768751235513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109178622967140512500823675 163767934450710768751235513)
      ·
        refine ⟨122825950838033076563426635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163767934450710768751235513 122825950838033076563426635)
        ·
          refine ⟨184238926257049614845139953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122825950838033076563426635 184238926257049614845139953)
          ·
            refine ⟨138179194692787211133854965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184238926257049614845139953 138179194692787211133854965)
            ·
              refine ⟨12954299502448801043798903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138179194692787211133854965 12954299502448801043798903)
              ·
                refine ⟨19431449253673201565698355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12954299502448801043798903 19431449253673201565698355)
                ·
                  refine ⟨29147173880509802348547533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19431449253673201565698355 29147173880509802348547533)
                  ·
                    refine ⟨10930190205191175880705325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29147173880509802348547533 10930190205191175880705325)
                    ·
                      refine ⟨4098821326946690955264497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930190205191175880705325 4098821326946690955264497)
                      ·
                        rfl

theorem cell23_7982426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_7982426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982426 prefixEnd_7982426 := by exact prefixLift 7982426
  have htrace : WordTrace (prefixWord ++ tailWord_7982426) baseStart_7982426 baseEnd_7982426 := by
    simpa [prefixWord, tailWord_7982426, baseEnd_7982426] using wordTrace_append hprefix tailTrace_7982426
  have hstable : (prefixWord ++ tailWord_7982426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982426).length < 2 ^ (prefixWord ++ tailWord_7982426).sum := by decide
  have hdescent : baseEnd_7982426 < baseStart_7982426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982504 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7982504 : Nat := 118140960795 + 7982504 * 2 ^ 59
def prefixEnd_7982504 : Nat := 4983230072969 + 3 ^ 40 * 7982504 * 2
def baseEnd_7982504 : Nat := 4098861378437741650089139

theorem tailTrace_7982504 : CollatzResearch.WordTrace tailWord_7982504 prefixEnd_7982504 4098861378437741650089139 := by
  unfold tailWord_7982504
  simp only [CollatzResearch.WordTrace]
  refine ⟨145572919736379392995101283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194097226315172523993468377 145572919736379392995101283)
  ·
    refine ⟨218359379604569089492651925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145572919736379392995101283 218359379604569089492651925)
    ·
      refine ⟨10235595918964176069968059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218359379604569089492651925 10235595918964176069968059)
      ·
        refine ⟨15353393878446264104952089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235595918964176069968059 15353393878446264104952089)
        ·
          refine ⟨11515045408834698078714067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15353393878446264104952089 11515045408834698078714067)
          ·
            refine ⟨17272568113252047118071101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11515045408834698078714067 17272568113252047118071101)
            ·
              refine ⟨6477213042469517669276663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17272568113252047118071101 6477213042469517669276663)
              ·
                refine ⟨9715819563704276503914995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6477213042469517669276663 9715819563704276503914995)
                ·
                  refine ⟨14573729345556414755872493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9715819563704276503914995 14573729345556414755872493)
                  ·
                    refine ⟨5465148504583655533452185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14573729345556414755872493 5465148504583655533452185)
                    ·
                      refine ⟨4098861378437741650089139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465148504583655533452185 4098861378437741650089139)
                      ·
                        rfl

theorem cell23_7982504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7982504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982504 prefixEnd_7982504 := by exact prefixLift 7982504
  have htrace : WordTrace (prefixWord ++ tailWord_7982504) baseStart_7982504 baseEnd_7982504 := by
    simpa [prefixWord, tailWord_7982504, baseEnd_7982504] using wordTrace_append hprefix tailTrace_7982504
  have hstable : (prefixWord ++ tailWord_7982504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982504).length < 2 ^ (prefixWord ++ tailWord_7982504).sum := by decide
  have hdescent : baseEnd_7982504 < baseStart_7982504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982517 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7982517 : Nat := 118140960795 + 7982517 * 2 ^ 59
def prefixEnd_7982517 : Nat := 4983230072969 + 3 ^ 40 * 7982517 * 2
def baseEnd_7982517 : Nat := 4098868053686250099226579

theorem tailTrace_7982517 : CollatzResearch.WordTrace tailWord_7982517 prefixEnd_7982517 4098868053686250099226579 := by
  unfold tailWord_7982517
  simp only [CollatzResearch.WordTrace]
  refine ⟨291146313621711689210425805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194097542414474459473617203 291146313621711689210425805)
  ·
    refine ⟨109179867608141883453909677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291146313621711689210425805 109179867608141883453909677)
    ·
      refine ⟨40942450353053206295216129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109179867608141883453909677 40942450353053206295216129)
      ·
        refine ⟨30706837764789904721412097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40942450353053206295216129 30706837764789904721412097)
        ·
          refine ⟨23030128323592428541059073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30706837764789904721412097 23030128323592428541059073)
          ·
            refine ⟨17272596242694321405794305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23030128323592428541059073 17272596242694321405794305)
            ·
              refine ⟨12954447182020741054345729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17272596242694321405794305 12954447182020741054345729)
              ·
                refine ⟨9715835386515555790759297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12954447182020741054345729 9715835386515555790759297)
                ·
                  refine ⟨7286876539886666843069473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9715835386515555790759297 7286876539886666843069473)
                  ·
                    refine ⟨5465157404915000132302105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7286876539886666843069473 5465157404915000132302105)
                    ·
                      refine ⟨4098868053686250099226579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465157404915000132302105 4098868053686250099226579)
                      ·
                        rfl

theorem cell23_7982517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7982517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982517 prefixEnd_7982517 := by exact prefixLift 7982517
  have htrace : WordTrace (prefixWord ++ tailWord_7982517) baseStart_7982517 baseEnd_7982517 := by
    simpa [prefixWord, tailWord_7982517, baseEnd_7982517] using wordTrace_append hprefix tailTrace_7982517
  have hstable : (prefixWord ++ tailWord_7982517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982517).length < 2 ^ (prefixWord ++ tailWord_7982517).sum := by decide
  have hdescent : baseEnd_7982517 < baseStart_7982517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982553 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_7982553 : Nat := 118140960795 + 7982553 * 2 ^ 59
def prefixEnd_7982553 : Nat := 4983230072969 + 3 ^ 40 * 7982553 * 2
def baseEnd_7982553 : Nat := 1366295512996603986125471

theorem tailTrace_7982553 : CollatzResearch.WordTrace tailWord_7982553 prefixEnd_7982553 1366295512996603986125471 := by
  unfold tailWord_7982553
  simp only [CollatzResearch.WordTrace]
  refine ⟨291147626649581267358736313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194098417766387511572490875 291147626649581267358736313)
  ·
    refine ⟨218360719987185950519052235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291147626649581267358736313 218360719987185950519052235)
    ·
      refine ⟨327541079980778925778578353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218360719987185950519052235 327541079980778925778578353)
      ·
        refine ⟨245655809985584194333933765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327541079980778925778578353 245655809985584194333933765)
        ·
          refine ⟨46060464372297036437612581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245655809985584194333933765 46060464372297036437612581)
          ·
            refine ⟨8636337069805694332052359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46060464372297036437612581 8636337069805694332052359)
            ·
              refine ⟨12954505604708541498078539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636337069805694332052359 12954505604708541498078539)
              ·
                refine ⟨19431758407062812247117809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12954505604708541498078539 19431758407062812247117809)
                ·
                  refine ⟨14573818805297109185338357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19431758407062812247117809 14573818805297109185338357)
                  ·
                    refine ⟨1366295512996603986125471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14573818805297109185338357 1366295512996603986125471)
                    ·
                      rfl

theorem cell23_7982553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_7982553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982553 prefixEnd_7982553 := by exact prefixLift 7982553
  have htrace : WordTrace (prefixWord ++ tailWord_7982553) baseStart_7982553 baseEnd_7982553 := by
    simpa [prefixWord, tailWord_7982553, baseEnd_7982553] using wordTrace_append hprefix tailTrace_7982553
  have hstable : (prefixWord ++ tailWord_7982553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982553).length < 2 ^ (prefixWord ++ tailWord_7982553).sum := by decide
  have hdescent : baseEnd_7982553 < baseStart_7982553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982623 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 3]
def baseStart_7982623 : Nat := 118140960795 + 7982623 * 2 ^ 59
def prefixEnd_7982623 : Nat := 4983230072969 + 3 ^ 40 * 7982623 * 2
def baseEnd_7982623 : Nat := 4098922482635626684501091

theorem tailTrace_7982623 : CollatzResearch.WordTrace tailWord_7982623 prefixEnd_7982623 4098922482635626684501091 := by
  unfold tailWord_7982623
  simp only [CollatzResearch.WordTrace]
  refine ⟨291150179759327669313784523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194100119839551779542523015 291150179759327669313784523)
  ·
    refine ⟨436725269638991503970676785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291150179759327669313784523 436725269638991503970676785)
    ·
      refine ⟨327543952229243627978007589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436725269638991503970676785 327543952229243627978007589)
      ·
        refine ⟨61414491042983180245876423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327543952229243627978007589 61414491042983180245876423)
        ·
          refine ⟨92121736564474770368814635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61414491042983180245876423 92121736564474770368814635)
          ·
            refine ⟨138182604846712155553221953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92121736564474770368814635 138182604846712155553221953)
            ·
              refine ⟨103636953635034116664916465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138182604846712155553221953 103636953635034116664916465)
              ·
                refine ⟨77727715226275587498687349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103636953635034116664916465 77727715226275587498687349)
                ·
                  refine ⟨7286973302463336328001939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77727715226275587498687349 7286973302463336328001939)
                  ·
                    refine ⟨10930459953695004492002909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7286973302463336328001939 10930459953695004492002909)
                    ·
                      refine ⟨4098922482635626684501091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930459953695004492002909 4098922482635626684501091)
                      ·
                        rfl

theorem cell23_7982623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_7982623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982623 prefixEnd_7982623 := by exact prefixLift 7982623
  have htrace : WordTrace (prefixWord ++ tailWord_7982623) baseStart_7982623 baseEnd_7982623 := by
    simpa [prefixWord, tailWord_7982623, baseEnd_7982623] using wordTrace_append hprefix tailTrace_7982623
  have hstable : (prefixWord ++ tailWord_7982623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982623).length < 2 ^ (prefixWord ++ tailWord_7982623).sum := by decide
  have hdescent : baseEnd_7982623 < baseStart_7982623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982656 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 1, 6]
def baseStart_7982656 : Nat := 118140960795 + 7982656 * 2 ^ 59
def prefixEnd_7982656 : Nat := 4983230072969 + 3 ^ 40 * 7982656 * 2
def baseEnd_7982656 : Nat := 1366313142499075018462813

theorem tailTrace_7982656 : CollatzResearch.WordTrace tailWord_7982656 prefixEnd_7982656 1366313142499075018462813 := by
  unfold tailWord_7982656
  simp only [CollatzResearch.WordTrace]
  refine ⟨145575691684104057974867911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194100922245472077299823881 145575691684104057974867911)
  ·
    refine ⟨218363537526156086962301867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145575691684104057974867911 218363537526156086962301867)
    ·
      refine ⟨327545306289234130443452801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218363537526156086962301867 327545306289234130443452801)
      ·
        refine ⟨245658979716925597832589601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327545306289234130443452801 245658979716925597832589601)
        ·
          refine ⟨184244234787694198374442201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245658979716925597832589601 184244234787694198374442201)
          ·
            refine ⟨138183176090770648780831651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184244234787694198374442201 138183176090770648780831651)
            ·
              refine ⟨207274764136155973171247477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138183176090770648780831651 207274764136155973171247477)
              ·
                refine ⟨19432009137764622484804451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207274764136155973171247477 19432009137764622484804451)
                ·
                  refine ⟨29148013706646933727206677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19432009137764622484804451 29148013706646933727206677)
                  ·
                    refine ⟨1366313142499075018462813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29148013706646933727206677 1366313142499075018462813)
                    ·
                      rfl

theorem cell23_7982656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_7982656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982656 prefixEnd_7982656 := by exact prefixLift 7982656
  have htrace : WordTrace (prefixWord ++ tailWord_7982656) baseStart_7982656 baseEnd_7982656 := by
    simpa [prefixWord, tailWord_7982656, baseEnd_7982656] using wordTrace_append hprefix tailTrace_7982656
  have hstable : (prefixWord ++ tailWord_7982656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982656).length < 2 ^ (prefixWord ++ tailWord_7982656).sum := by decide
  have hdescent : baseEnd_7982656 < baseStart_7982656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982710 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7982710 : Nat := 118140960795 + 7982710 * 2 ^ 59
def prefixEnd_7982710 : Nat := 4983230072969 + 3 ^ 40 * 7982710 * 2
def baseEnd_7982710 : Nat := 4098967155452567844113191

theorem tailTrace_7982710 : CollatzResearch.WordTrace tailWord_7982710 prefixEnd_7982710 4098967155452567844113191 := by
  unfold tailWord_7982710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197084556875780198262599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194102235273341655448134389 18197084556875780198262599)
  ·
    refine ⟨27295626835313670297393899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18197084556875780198262599 27295626835313670297393899)
    ·
      refine ⟨40943440252970505446090849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27295626835313670297393899 40943440252970505446090849)
      ·
        refine ⟨30707580189727879084568137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40943440252970505446090849 30707580189727879084568137)
        ·
          refine ⟨23030685142295909313426103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30707580189727879084568137 23030685142295909313426103)
          ·
            refine ⟨34546027713443863970139155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23030685142295909313426103 34546027713443863970139155)
            ·
              refine ⟨51819041570165795955208733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34546027713443863970139155 51819041570165795955208733)
              ·
                refine ⟨19432140588812173483203275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51819041570165795955208733 19432140588812173483203275)
                ·
                  refine ⟨29148210883218260224804913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19432140588812173483203275 29148210883218260224804913)
                  ·
                    refine ⟨21861158162413695168603685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29148210883218260224804913 21861158162413695168603685)
                    ·
                      refine ⟨4098967155452567844113191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21861158162413695168603685 4098967155452567844113191)
                      ·
                        rfl

theorem cell23_7982710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7982710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982710 prefixEnd_7982710 := by exact prefixLift 7982710
  have htrace : WordTrace (prefixWord ++ tailWord_7982710) baseStart_7982710 baseEnd_7982710 := by
    simpa [prefixWord, tailWord_7982710, baseEnd_7982710] using wordTrace_append hprefix tailTrace_7982710
  have hstable : (prefixWord ++ tailWord_7982710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982710).length < 2 ^ (prefixWord ++ tailWord_7982710).sum := by decide
  have hdescent : baseEnd_7982710 < baseStart_7982710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982716 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_7982716 : Nat := 118140960795 + 7982716 * 2 ^ 59
def prefixEnd_7982716 : Nat := 4983230072969 + 3 ^ 40 * 7982716 * 2
def baseEnd_7982716 : Nat := 1366323412112164940212721

theorem tailTrace_7982716 : CollatzResearch.WordTrace tailWord_7982716 prefixEnd_7982716 1366323412112164940212721 := by
  unfold tailWord_7982716
  simp only [CollatzResearch.WordTrace]
  refine ⟨145576785873995373098460001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194102381165327164131280001 145576785873995373098460001)
  ·
    refine ⟨109182589405496529823845001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145576785873995373098460001 109182589405496529823845001)
    ·
      refine ⟨81886942054122397367883751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109182589405496529823845001 81886942054122397367883751)
      ·
        refine ⟨122830413081183596051825627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81886942054122397367883751 122830413081183596051825627)
        ·
          refine ⟨184245619621775394077738441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122830413081183596051825627 184245619621775394077738441)
          ·
            refine ⟨138184214716331545558303831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184245619621775394077738441 138184214716331545558303831)
            ·
              refine ⟨207276322074497318337455747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138184214716331545558303831 207276322074497318337455747)
              ·
                refine ⟨310914483111745977506183621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207276322074497318337455747 310914483111745977506183621)
                ·
                  refine ⟨58296465583452370782409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310914483111745977506183621 58296465583452370782409429)
                  ·
                    refine ⟨1366323412112164940212721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58296465583452370782409429 1366323412112164940212721)
                    ·
                      rfl

theorem cell23_7982716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_7982716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982716 prefixEnd_7982716 := by exact prefixLift 7982716
  have htrace : WordTrace (prefixWord ++ tailWord_7982716) baseStart_7982716 baseEnd_7982716 := by
    simpa [prefixWord, tailWord_7982716, baseEnd_7982716] using wordTrace_append hprefix tailTrace_7982716
  have hstable : (prefixWord ++ tailWord_7982716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982716).length < 2 ^ (prefixWord ++ tailWord_7982716).sum := by decide
  have hdescent : baseEnd_7982716 < baseStart_7982716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982730 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_7982730 : Nat := 118140960795 + 7982730 * 2 ^ 59
def prefixEnd_7982730 : Nat := 4983230072969 + 3 ^ 40 * 7982730 * 2
def baseEnd_7982730 : Nat := 4098977425065657765863099

theorem tailTrace_7982730 : CollatzResearch.WordTrace tailWord_7982730 prefixEnd_7982730 4098977425065657765863099 := by
  unfold tailWord_7982730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72788520592485006646982411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194102721579960017725286429 72788520592485006646982411)
  ·
    refine ⟨109182780888727509970473617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72788520592485006646982411 109182780888727509970473617)
    ·
      refine ⟨81887085666545632477855213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109182780888727509970473617 81887085666545632477855213)
      ·
        refine ⟨30707657124954612179195705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81887085666545632477855213 30707657124954612179195705)
        ·
          refine ⟨23030742843715959134396779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30707657124954612179195705 23030742843715959134396779)
          ·
            refine ⟨34546114265573938701595169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23030742843715959134396779 34546114265573938701595169)
            ·
              refine ⟨25909585699180454026196377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34546114265573938701595169 25909585699180454026196377)
              ·
                refine ⟨19432189274385340519647283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25909585699180454026196377 19432189274385340519647283)
                ·
                  refine ⟨29148283911578010779470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19432189274385340519647283 29148283911578010779470925)
                  ·
                    refine ⟨10930606466841754042301597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29148283911578010779470925 10930606466841754042301597)
                    ·
                      refine ⟨4098977425065657765863099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930606466841754042301597 4098977425065657765863099)
                      ·
                        rfl

theorem cell23_7982730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_7982730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982730 prefixEnd_7982730 := by exact prefixLift 7982730
  have htrace : WordTrace (prefixWord ++ tailWord_7982730) baseStart_7982730 baseEnd_7982730 := by
    simpa [prefixWord, tailWord_7982730, baseEnd_7982730] using wordTrace_append hprefix tailTrace_7982730
  have hstable : (prefixWord ++ tailWord_7982730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982730).length < 2 ^ (prefixWord ++ tailWord_7982730).sum := by decide
  have hdescent : baseEnd_7982730 < baseStart_7982730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982734 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7982734 : Nat := 118140960795 + 7982734 * 2 ^ 59
def prefixEnd_7982734 : Nat := 4983230072969 + 3 ^ 40 * 7982734 * 2
def baseEnd_7982734 : Nat := 4098979478988275750213081

theorem tailTrace_7982734 : CollatzResearch.WordTrace tailWord_7982734 prefixEnd_7982734 4098979478988275750213081 := by
  unfold tailWord_7982734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36394278532740691908884407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194102818841283690180716837 36394278532740691908884407)
  ·
    refine ⟨54591417799111037863326611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36394278532740691908884407 54591417799111037863326611)
    ·
      refine ⟨81887126698666556794989917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54591417799111037863326611 81887126698666556794989917)
      ·
        refine ⟨30707672511999958798121219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81887126698666556794989917 30707672511999958798121219)
        ·
          refine ⟨46061508767999938197181829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30707672511999958798121219 46061508767999938197181829)
          ·
            refine ⟨8636532893999988411971593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46061508767999938197181829 8636532893999988411971593)
            ·
              refine ⟨6477399670499991308978695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8636532893999988411971593 6477399670499991308978695)
              ·
                refine ⟨9716099505749986963468043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6477399670499991308978695 9716099505749986963468043)
                ·
                  refine ⟨14574149258624980445202065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9716099505749986963468043 14574149258624980445202065)
                  ·
                    refine ⟨10930611943968735333901549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14574149258624980445202065 10930611943968735333901549)
                    ·
                      refine ⟨4098979478988275750213081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930611943968735333901549 4098979478988275750213081)
                      ·
                        rfl

theorem cell23_7982734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7982734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982734 prefixEnd_7982734 := by exact prefixLift 7982734
  have htrace : WordTrace (prefixWord ++ tailWord_7982734) baseStart_7982734 baseEnd_7982734 := by
    simpa [prefixWord, tailWord_7982734, baseEnd_7982734] using wordTrace_append hprefix tailTrace_7982734
  have hstable : (prefixWord ++ tailWord_7982734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982734).length < 2 ^ (prefixWord ++ tailWord_7982734).sum := by decide
  have hdescent : baseEnd_7982734 < baseStart_7982734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982804 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7982804 : Nat := 118140960795 + 7982804 * 2 ^ 59
def prefixEnd_7982804 : Nat := 4983230072969 + 3 ^ 40 * 7982804 * 2
def baseEnd_7982804 : Nat := 4099015422634090476337759

theorem tailTrace_7982804 : CollatzResearch.WordTrace tailWord_7982804 prefixEnd_7982804 4099015422634090476337759 := by
  unfold tailWord_7982804
  simp only [CollatzResearch.WordTrace]
  refine ⟨145578390685835968613061733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194104520914447958150748977 145578390685835968613061733)
  ·
    refine ⟨27295948253594244114949075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145578390685835968613061733 27295948253594244114949075)
    ·
      refine ⟨40943922380391366172423613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27295948253594244114949075 40943922380391366172423613)
      ·
        refine ⟨15353970892646762314658855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40943922380391366172423613 15353970892646762314658855)
        ·
          refine ⟨23030956338970143471988283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15353970892646762314658855 23030956338970143471988283)
          ·
            refine ⟨34546434508455215207982425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23030956338970143471988283 34546434508455215207982425)
            ·
              refine ⟨25909825881341411405986819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34546434508455215207982425 25909825881341411405986819)
              ·
                refine ⟨38864738822012117108980229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25909825881341411405986819 38864738822012117108980229)
                ·
                  refine ⟨7287138529127271957933793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38864738822012117108980229 7287138529127271957933793)
                  ·
                    refine ⟨5465353896845453968450345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7287138529127271957933793 5465353896845453968450345)
                    ·
                      refine ⟨4099015422634090476337759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465353896845453968450345 4099015422634090476337759)
                      ·
                        rfl

theorem cell23_7982804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7982804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982804 prefixEnd_7982804 := by exact prefixLift 7982804
  have htrace : WordTrace (prefixWord ++ tailWord_7982804) baseStart_7982804 baseEnd_7982804 := by
    simpa [prefixWord, tailWord_7982804, baseEnd_7982804] using wordTrace_append hprefix tailTrace_7982804
  have hstable : (prefixWord ++ tailWord_7982804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982804).length < 2 ^ (prefixWord ++ tailWord_7982804).sum := by decide
  have hdescent : baseEnd_7982804 < baseStart_7982804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
