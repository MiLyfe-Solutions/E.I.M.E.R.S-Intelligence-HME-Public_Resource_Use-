import V185TrunkScan23Chunk1120

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6639972 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_6639972 : Nat := 118140960795 + 6639972 * 2 ^ 59
def prefixEnd_6639972 : Nat := 4983230072969 + 3 ^ 40 * 6639972 * 2
def baseEnd_6639972 : Nat := 3409497168395800312713331

theorem tailTrace_6639972 : CollatzResearch.WordTrace tailWord_6639972 prefixEnd_6639972 3409497168395800312713331 := by
  unfold tailWord_6639972
  simp only [CollatzResearch.WordTrace]
  refine ⟨121089837350261467889505085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161453116467015290519340113 121089837350261467889505085)
  ·
    refine ⟨45408689006348050458564407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121089837350261467889505085 45408689006348050458564407)
    ·
      refine ⟨68113033509522075687846611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45408689006348050458564407 68113033509522075687846611)
      ·
        refine ⟨102169550264283113531769917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68113033509522075687846611 102169550264283113531769917)
        ·
          refine ⟨38313581349106167574413719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102169550264283113531769917 38313581349106167574413719)
          ·
            refine ⟨57470372023659251361620579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38313581349106167574413719 57470372023659251361620579)
            ·
              refine ⟨86205558035488877042430869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57470372023659251361620579 86205558035488877042430869)
              ·
                refine ⟨4040885532913541111363947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86205558035488877042430869 4040885532913541111363947)
                ·
                  refine ⟨6061328299370311667045921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040885532913541111363947 6061328299370311667045921)
                  ·
                    refine ⟨4545996224527733750284441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6061328299370311667045921 4545996224527733750284441)
                    ·
                      refine ⟨3409497168395800312713331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4545996224527733750284441 3409497168395800312713331)
                      ·
                        rfl

theorem cell23_6639972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_6639972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6639972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6639972 prefixEnd_6639972 := by exact prefixLift 6639972
  have htrace : WordTrace (prefixWord ++ tailWord_6639972) baseStart_6639972 baseEnd_6639972 := by
    simpa [prefixWord, tailWord_6639972, baseEnd_6639972] using wordTrace_append hprefix tailTrace_6639972
  have hstable : (prefixWord ++ tailWord_6639972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6639972).length < 2 ^ (prefixWord ++ tailWord_6639972).sum := by decide
  have hdescent : baseEnd_6639972 < baseStart_6639972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6639972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640031 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6640031 : Nat := 118140960795 + 6640031 * 2 ^ 59
def prefixEnd_6640031 : Nat := 4983230072969 + 3 ^ 40 * 6640031 * 2
def baseEnd_6640031 : Nat := 3409527463754415581875559

theorem tailTrace_6640031 : CollatzResearch.WordTrace tailWord_6640031 prefixEnd_6640031 3409527463754415581875559 := by
  unfold tailWord_6640031
  simp only [CollatzResearch.WordTrace]
  refine ⟨242181826607309188855407947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161454551071539459236938631 242181826607309188855407947)
  ·
    refine ⟨363272739910963783283111921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242181826607309188855407947 363272739910963783283111921)
    ·
      refine ⟨272454554933222837462333941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363272739910963783283111921 272454554933222837462333941)
      ·
        refine ⟨25542614524989641012093807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272454554933222837462333941 25542614524989641012093807)
        ·
          refine ⟨38313921787484461518140711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25542614524989641012093807 38313921787484461518140711)
          ·
            refine ⟨57470882681226692277211067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38313921787484461518140711 57470882681226692277211067)
            ·
              refine ⟨86206324021840038415816601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57470882681226692277211067 86206324021840038415816601)
              ·
                refine ⟨64654743016380028811862451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86206324021840038415816601 64654743016380028811862451)
                ·
                  refine ⟨96982114524570043217793677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64654743016380028811862451 96982114524570043217793677)
                  ·
                    refine ⟨36368292946713766206672629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96982114524570043217793677 36368292946713766206672629)
                    ·
                      refine ⟨3409527463754415581875559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36368292946713766206672629 3409527463754415581875559)
                      ·
                        rfl

theorem cell23_6640031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6640031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640031 prefixEnd_6640031 := by exact prefixLift 6640031
  have htrace : WordTrace (prefixWord ++ tailWord_6640031) baseStart_6640031 baseEnd_6640031 := by
    simpa [prefixWord, tailWord_6640031, baseEnd_6640031] using wordTrace_append hprefix tailTrace_6640031
  have hstable : (prefixWord ++ tailWord_6640031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640031).length < 2 ^ (prefixWord ++ tailWord_6640031).sum := by decide
  have hdescent : baseEnd_6640031 < baseStart_6640031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640039 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6640039 : Nat := 118140960795 + 6640039 * 2 ^ 59
def prefixEnd_6640039 : Nat := 4983230072969 + 3 ^ 40 * 6640039 * 2
def baseEnd_6640039 : Nat := 3409531571599651550575523

theorem tailTrace_6640039 : CollatzResearch.WordTrace tailWord_6640039 prefixEnd_6640039 3409531571599651550575523 := by
  unfold tailWord_6640039
  simp only [CollatzResearch.WordTrace]
  refine ⟨242182118391280206221699171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161454745594186804147799447 242182118391280206221699171)
  ·
    refine ⟨363273177586920309332548757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242182118391280206221699171 363273177586920309332548757)
    ·
      refine ⟨17028430199386889499963223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 363273177586920309332548757 17028430199386889499963223)
      ·
        refine ⟨25542645299080334249944835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17028430199386889499963223 25542645299080334249944835)
        ·
          refine ⟨38313967948620501374917253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25542645299080334249944835 38313967948620501374917253)
          ·
            refine ⟨7183868990366344007796985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38313967948620501374917253 7183868990366344007796985)
            ·
              refine ⟨5387901742774758005847739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183868990366344007796985 5387901742774758005847739)
              ·
                refine ⟨8081852614162137008771609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387901742774758005847739 8081852614162137008771609)
                ·
                  refine ⟨6061389460621602756578707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8081852614162137008771609 6061389460621602756578707)
                  ·
                    refine ⟨9092084190932404134868061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061389460621602756578707 9092084190932404134868061)
                    ·
                      refine ⟨3409531571599651550575523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092084190932404134868061 3409531571599651550575523)
                      ·
                        rfl

theorem cell23_6640039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6640039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640039 prefixEnd_6640039 := by exact prefixLift 6640039
  have htrace : WordTrace (prefixWord ++ tailWord_6640039) baseStart_6640039 baseEnd_6640039 := by
    simpa [prefixWord, tailWord_6640039, baseEnd_6640039] using wordTrace_append hprefix tailTrace_6640039
  have hstable : (prefixWord ++ tailWord_6640039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640039).length < 2 ^ (prefixWord ++ tailWord_6640039).sum := by decide
  have hdescent : baseEnd_6640039 < baseStart_6640039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640041 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_6640041 : Nat := 118140960795 + 6640041 * 2 ^ 59
def prefixEnd_6640041 : Nat := 4983230072969 + 3 ^ 40 * 6640041 * 2
def baseEnd_6640041 : Nat := 3409532598560960542750513

theorem tailTrace_6640041 : CollatzResearch.WordTrace tailWord_6640041 prefixEnd_6640041 3409532598560960542750513 := by
  unfold tailWord_6640041
  simp only [CollatzResearch.WordTrace]
  refine ⟨242182191337272960563271977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161454794224848640375514651 242182191337272960563271977)
  ·
    refine ⟨181636643502954720422453983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242182191337272960563271977 181636643502954720422453983)
    ·
      refine ⟨272454965254432080633680975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181636643502954720422453983 272454965254432080633680975)
      ·
        refine ⟨408682447881648120950521463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272454965254432080633680975 408682447881648120950521463)
        ·
          refine ⟨613023671822472181425782195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408682447881648120950521463 613023671822472181425782195)
          ·
            refine ⟨919535507733708272138673293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613023671822472181425782195 919535507733708272138673293)
            ·
              refine ⟨344825815400140602052002485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919535507733708272138673293 344825815400140602052002485)
              ·
                refine ⟨32327420193763181442375233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344825815400140602052002485 32327420193763181442375233)
                ·
                  refine ⟨24245565145322386081781425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32327420193763181442375233 24245565145322386081781425)
                  ·
                    refine ⟨18184173858991789561336069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24245565145322386081781425 18184173858991789561336069)
                    ·
                      refine ⟨3409532598560960542750513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18184173858991789561336069 3409532598560960542750513)
                      ·
                        rfl

theorem cell23_6640041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_6640041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640041 prefixEnd_6640041 := by exact prefixLift 6640041
  have htrace : WordTrace (prefixWord ++ tailWord_6640041) baseStart_6640041 baseEnd_6640041 := by
    simpa [prefixWord, tailWord_6640041, baseEnd_6640041] using wordTrace_append hprefix tailTrace_6640041
  have hstable : (prefixWord ++ tailWord_6640041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640041).length < 2 ^ (prefixWord ++ tailWord_6640041).sum := by decide
  have hdescent : baseEnd_6640041 < baseStart_6640041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640078 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_6640078 : Nat := 118140960795 + 6640078 * 2 ^ 59
def prefixEnd_6640078 : Nat := 4983230072969 + 3 ^ 40 * 6640078 * 2
def baseEnd_6640078 : Nat := 3409551597345176897987843

theorem tailTrace_6640078 : CollatzResearch.WordTrace tailWord_6640078 prefixEnd_6640078 3409551597345176897987843 := by
  unfold tailWord_6640078
  simp only [CollatzResearch.WordTrace]
  refine ⟨30272942604767364485296111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161455693892092610588245925 30272942604767364485296111)
  ·
    refine ⟨45409413907151046727944167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30272942604767364485296111 45409413907151046727944167)
    ·
      refine ⟨68114120860726570091916251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45409413907151046727944167 68114120860726570091916251)
      ·
        refine ⟨102171181291089855137874377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68114120860726570091916251 102171181291089855137874377)
        ·
          refine ⟨76628385968317391353405783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102171181291089855137874377 76628385968317391353405783)
          ·
            refine ⟨114942578952476087030108675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76628385968317391353405783 114942578952476087030108675)
            ·
              refine ⟨172413868428714130545163013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114942578952476087030108675 172413868428714130545163013)
              ·
                refine ⟨32327600330383899477218065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172413868428714130545163013 32327600330383899477218065)
                ·
                  refine ⟨24245700247787924607913549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32327600330383899477218065 24245700247787924607913549)
                  ·
                    refine ⟨9092137592920471727967581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24245700247787924607913549 9092137592920471727967581)
                    ·
                      refine ⟨3409551597345176897987843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092137592920471727967581 3409551597345176897987843)
                      ·
                        rfl

theorem cell23_6640078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_6640078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640078 prefixEnd_6640078 := by exact prefixLift 6640078
  have htrace : WordTrace (prefixWord ++ tailWord_6640078) baseStart_6640078 baseEnd_6640078 := by
    simpa [prefixWord, tailWord_6640078, baseEnd_6640078] using wordTrace_append hprefix tailTrace_6640078
  have hstable : (prefixWord ++ tailWord_6640078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640078).length < 2 ^ (prefixWord ++ tailWord_6640078).sum := by decide
  have hdescent : baseEnd_6640078 < baseStart_6640078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640085 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 5]
def baseStart_6640085 : Nat := 118140960795 + 6640085 * 2 ^ 59
def prefixEnd_6640085 : Nat := 4983230072969 + 3 ^ 40 * 6640085 * 2
def baseEnd_6640085 : Nat := 378839465745528707844479

theorem tailTrace_6640085 : CollatzResearch.WordTrace tailWord_6640085 prefixEnd_6640085 378839465745528707844479 := by
  unfold tailWord_6640085
  simp only [CollatzResearch.WordTrace]
  refine ⟨242183796149113556077873709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161455864099409037385249139 242183796149113556077873709)
  ·
    refine ⟨90818923555917583529202641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242183796149113556077873709 90818923555917583529202641)
    ·
      refine ⟨68114192666938187646901981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90818923555917583529202641 68114192666938187646901981)
      ·
        refine ⟨25542822250101820367588243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68114192666938187646901981 25542822250101820367588243)
        ·
          refine ⟨38314233375152730551382365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25542822250101820367588243 38314233375152730551382365)
          ·
            refine ⟨14367837515682273956768387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38314233375152730551382365 14367837515682273956768387)
            ·
              refine ⟨21551756273523410935152581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14367837515682273956768387 21551756273523410935152581)
              ·
                refine ⟨4040954301285639550341109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21551756273523410935152581 4040954301285639550341109)
                ·
                  refine ⟨378839465745528707844479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4040954301285639550341109 378839465745528707844479)
                  ·
                    rfl

theorem cell23_6640085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_6640085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640085 prefixEnd_6640085 := by exact prefixLift 6640085
  have htrace : WordTrace (prefixWord ++ tailWord_6640085) baseStart_6640085 baseEnd_6640085 := by
    simpa [prefixWord, tailWord_6640085, baseEnd_6640085] using wordTrace_append hprefix tailTrace_6640085
  have hstable : (prefixWord ++ tailWord_6640085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640085).length < 2 ^ (prefixWord ++ tailWord_6640085).sum := by decide
  have hdescent : baseEnd_6640085 < baseStart_6640085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640131 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_6640131 : Nat := 118140960795 + 6640131 * 2 ^ 59
def prefixEnd_6640131 : Nat := 4983230072969 + 3 ^ 40 * 6640131 * 2
def baseEnd_6640131 : Nat := 3409578811819865190625099

theorem tailTrace_6640131 : CollatzResearch.WordTrace tailWord_6640131 prefixEnd_6640131 3409578811819865190625099 := by
  unfold tailWord_6640131
  simp only [CollatzResearch.WordTrace]
  refine ⟨242185473906946905934048247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161456982604631270622698831 242185473906946905934048247)
  ·
    refine ⟨363278210860420358901072371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242185473906946905934048247 363278210860420358901072371)
    ·
      refine ⟨544917316290630538351608557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363278210860420358901072371 544917316290630538351608557)
      ·
        refine ⟨204343993608986451881853209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544917316290630538351608557 204343993608986451881853209)
        ·
          refine ⟨153257995206739838911389907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204343993608986451881853209 153257995206739838911389907)
          ·
            refine ⟨229886992810109758367084861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153257995206739838911389907 229886992810109758367084861)
            ·
              refine ⟨86207622303791159387656823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229886992810109758367084861 86207622303791159387656823)
              ·
                refine ⟨129311433455686739081485235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86207622303791159387656823 129311433455686739081485235)
                ·
                  refine ⟨193967150183530108622227853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129311433455686739081485235 193967150183530108622227853)
                  ·
                    refine ⟨72737681318823790733335445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193967150183530108622227853 72737681318823790733335445)
                    ·
                      refine ⟨3409578811819865190625099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72737681318823790733335445 3409578811819865190625099)
                      ·
                        rfl

theorem cell23_6640131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_6640131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640131 prefixEnd_6640131 := by exact prefixLift 6640131
  have htrace : WordTrace (prefixWord ++ tailWord_6640131) baseStart_6640131 baseEnd_6640131 := by
    simpa [prefixWord, tailWord_6640131, baseEnd_6640131] using wordTrace_append hprefix tailTrace_6640131
  have hstable : (prefixWord ++ tailWord_6640131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640131).length < 2 ^ (prefixWord ++ tailWord_6640131).sum := by decide
  have hdescent : baseEnd_6640131 < baseStart_6640131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640171 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 9]
def baseStart_6640171 : Nat := 118140960795 + 6640171 * 2 ^ 59
def prefixEnd_6640171 : Nat := 4983230072969 + 3 ^ 40 * 6640171 * 2
def baseEnd_6640171 : Nat := 1136533117015348344708305

theorem tailTrace_6640171 : CollatzResearch.WordTrace tailWord_6640171 prefixEnd_6640171 1136533117015348344708305 := by
  unfold tailWord_6640171
  simp only [CollatzResearch.WordTrace]
  refine ⟨242186932826801992765504367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161457955217867995177002911 242186932826801992765504367)
  ·
    refine ⟨363280399240202989148256551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242186932826801992765504367 363280399240202989148256551)
    ·
      refine ⟨544920598860304483722384827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363280399240202989148256551 544920598860304483722384827)
      ·
        refine ⟨817380898290456725583577241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544920598860304483722384827 817380898290456725583577241)
        ·
          refine ⟨613035673717842544187682931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817380898290456725583577241 613035673717842544187682931)
          ·
            refine ⟨919553510576763816281524397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613035673717842544187682931 919553510576763816281524397)
            ·
              refine ⟨344832566466286431105571649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919553510576763816281524397 344832566466286431105571649)
              ·
                refine ⟨258624424849714823329178737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344832566466286431105571649 258624424849714823329178737)
                ·
                  refine ⟨193968318637286117496884053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258624424849714823329178737 193968318637286117496884053)
                  ·
                    refine ⟨1136533117015348344708305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193968318637286117496884053 1136533117015348344708305)
                    ·
                      rfl

theorem cell23_6640171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_6640171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640171 prefixEnd_6640171 := by exact prefixLift 6640171
  have htrace : WordTrace (prefixWord ++ tailWord_6640171) baseStart_6640171 baseEnd_6640171 := by
    simpa [prefixWord, tailWord_6640171, baseEnd_6640171] using wordTrace_append hprefix tailTrace_6640171
  have hstable : (prefixWord ++ tailWord_6640171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640171).length < 2 ^ (prefixWord ++ tailWord_6640171).sum := by decide
  have hdescent : baseEnd_6640171 < baseStart_6640171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640202 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_6640202 : Nat := 118140960795 + 6640202 * 2 ^ 59
def prefixEnd_6640202 : Nat := 4983230072969 + 3 ^ 40 * 6640202 * 2
def baseEnd_6640202 : Nat := 3409615268946334412837273

theorem tailTrace_6640202 : CollatzResearch.WordTrace tailWord_6640202 prefixEnd_6640202 3409615268946334412837273 := by
  unfold tailWord_6640202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60547015872422421264970715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161458708993126456706588573 60547015872422421264970715)
  ·
    refine ⟨90820523808633631897456073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60547015872422421264970715 90820523808633631897456073)
    ·
      refine ⟨68115392856475223923092055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90820523808633631897456073 68115392856475223923092055)
      ·
        refine ⟨102173089284712835884638083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68115392856475223923092055 102173089284712835884638083)
        ·
          refine ⟨153259633927069253826957125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102173089284712835884638083 153259633927069253826957125)
          ·
            refine ⟨28736181361325485092554461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153259633927069253826957125 28736181361325485092554461)
            ·
              refine ⟨10776068010497056909707923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28736181361325485092554461 10776068010497056909707923)
              ·
                refine ⟨16164102015745585364561885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776068010497056909707923 16164102015745585364561885)
                ·
                  refine ⟨6061538255904594511710707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16164102015745585364561885 6061538255904594511710707)
                  ·
                    refine ⟨9092307383856891767566061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061538255904594511710707 9092307383856891767566061)
                    ·
                      refine ⟨3409615268946334412837273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092307383856891767566061 3409615268946334412837273)
                      ·
                        rfl

theorem cell23_6640202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_6640202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640202 prefixEnd_6640202 := by exact prefixLift 6640202
  have htrace : WordTrace (prefixWord ++ tailWord_6640202) baseStart_6640202 baseEnd_6640202 := by
    simpa [prefixWord, tailWord_6640202, baseEnd_6640202] using wordTrace_append hprefix tailTrace_6640202
  have hstable : (prefixWord ++ tailWord_6640202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640202).length < 2 ^ (prefixWord ++ tailWord_6640202).sum := by decide
  have hdescent : baseEnd_6640202 < baseStart_6640202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640225 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6640225 : Nat := 118140960795 + 6640225 * 2 ^ 59
def prefixEnd_6640225 : Nat := 4983230072969 + 3 ^ 40 * 6640225 * 2
def baseEnd_6640225 : Nat := 3409627079001387822849667

theorem tailTrace_6640225 : CollatzResearch.WordTrace tailWord_6640225 prefixEnd_6640225 3409627079001387822849667 := by
  unfold tailWord_6640225
  simp only [CollatzResearch.WordTrace]
  refine ⟨242188902368606359987970129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161459268245737573325313419 242188902368606359987970129)
  ·
    refine ⟨181641676776454769990977597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242188902368606359987970129 181641676776454769990977597)
    ·
      refine ⟨68115628791170538746616599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181641676776454769990977597 68115628791170538746616599)
      ·
        refine ⟨102173443186755808119924899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68115628791170538746616599 102173443186755808119924899)
        ·
          refine ⟨153260164780133712179887349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102173443186755808119924899 153260164780133712179887349)
          ·
            refine ⟨14368140448137535516864439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153260164780133712179887349 14368140448137535516864439)
            ·
              refine ⟨21552210672206303275296659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14368140448137535516864439 21552210672206303275296659)
              ·
                refine ⟨32328316008309454912944989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21552210672206303275296659 32328316008309454912944989)
                ·
                  refine ⟨12123118503116045592354371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32328316008309454912944989 12123118503116045592354371)
                  ·
                    refine ⟨18184677754674068388531557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12123118503116045592354371 18184677754674068388531557)
                    ·
                      refine ⟨3409627079001387822849667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18184677754674068388531557 3409627079001387822849667)
                      ·
                        rfl

theorem cell23_6640225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6640225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640225 prefixEnd_6640225 := by exact prefixLift 6640225
  have htrace : WordTrace (prefixWord ++ tailWord_6640225) baseStart_6640225 baseEnd_6640225 := by
    simpa [prefixWord, tailWord_6640225, baseEnd_6640225] using wordTrace_append hprefix tailTrace_6640225
  have hstable : (prefixWord ++ tailWord_6640225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640225).length < 2 ^ (prefixWord ++ tailWord_6640225).sum := by decide
  have hdescent : baseEnd_6640225 < baseStart_6640225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640229 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_6640229 : Nat := 118140960795 + 6640229 * 2 ^ 59
def prefixEnd_6640229 : Nat := 4983230072969 + 3 ^ 40 * 6640229 * 2
def baseEnd_6640229 : Nat := 3409629132924005807199649

theorem tailTrace_6640229 : CollatzResearch.WordTrace tailWord_6640229 prefixEnd_6640229 3409629132924005807199649 := by
  unfold tailWord_6640229
  simp only [CollatzResearch.WordTrace]
  refine ⟨242189048260591868671115741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161459365507061245780743827 242189048260591868671115741)
  ·
    refine ⟨90820893097721950751668403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242189048260591868671115741 90820893097721950751668403)
    ·
      refine ⟨136231339646582926127502605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90820893097721950751668403 136231339646582926127502605)
      ·
        refine ⟨51086752367468597297813477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136231339646582926127502605 51086752367468597297813477)
        ·
          refine ⟨9578766068900361993340027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51086752367468597297813477 9578766068900361993340027)
          ·
            refine ⟨14368149103350542990010041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578766068900361993340027 14368149103350542990010041)
            ·
              refine ⟨10776111827512907242507531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14368149103350542990010041 10776111827512907242507531)
              ·
                refine ⟨16164167741269360863761297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776111827512907242507531 16164167741269360863761297)
                ·
                  refine ⟨12123125805952020647820973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16164167741269360863761297 12123125805952020647820973)
                  ·
                    refine ⟨4546172177232007742932865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12123125805952020647820973 4546172177232007742932865)
                    ·
                      refine ⟨3409629132924005807199649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546172177232007742932865 3409629132924005807199649)
                      ·
                        rfl

theorem cell23_6640229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_6640229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640229 prefixEnd_6640229 := by exact prefixLift 6640229
  have htrace : WordTrace (prefixWord ++ tailWord_6640229) baseStart_6640229 baseEnd_6640229 := by
    simpa [prefixWord, tailWord_6640229, baseEnd_6640229] using wordTrace_append hprefix tailTrace_6640229
  have hstable : (prefixWord ++ tailWord_6640229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640229).length < 2 ^ (prefixWord ++ tailWord_6640229).sum := by decide
  have hdescent : baseEnd_6640229 < baseStart_6640229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640253 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_6640253 : Nat := 118140960795 + 6640253 * 2 ^ 59
def prefixEnd_6640253 : Nat := 4983230072969 + 3 ^ 40 * 6640253 * 2
def baseEnd_6640253 : Nat := 3409641456459713713299539

theorem tailTrace_6640253 : CollatzResearch.WordTrace tailWord_6640253 prefixEnd_6640253 3409641456459713713299539 := by
  unfold tailWord_6640253
  simp only [CollatzResearch.WordTrace]
  refine ⟨242189923612504920769989413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161459949075003280513326275 242189923612504920769989413)
  ·
    refine ⟨45410610677344672644373015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242189923612504920769989413 45410610677344672644373015)
    ·
      refine ⟨68115916016017008966559523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45410610677344672644373015 68115916016017008966559523)
      ·
        refine ⟨102173874024025513449839285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68115916016017008966559523 102173874024025513449839285)
        ·
          refine ⟨9578800689752391885922433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102173874024025513449839285 9578800689752391885922433)
          ·
            refine ⟨7184100517314293914441825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9578800689752391885922433 7184100517314293914441825)
            ·
              refine ⟨5388075387985720435831369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7184100517314293914441825 5388075387985720435831369)
              ·
                refine ⟨4041056540989290326873527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388075387985720435831369 4041056540989290326873527)
                ·
                  refine ⟨6061584811483935490310291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041056540989290326873527 6061584811483935490310291)
                  ·
                    refine ⟨9092377217225903235465437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061584811483935490310291 9092377217225903235465437)
                    ·
                      refine ⟨3409641456459713713299539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092377217225903235465437 3409641456459713713299539)
                      ·
                        rfl

theorem cell23_6640253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_6640253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640253 prefixEnd_6640253 := by exact prefixLift 6640253
  have htrace : WordTrace (prefixWord ++ tailWord_6640253) baseStart_6640253 baseEnd_6640253 := by
    simpa [prefixWord, tailWord_6640253, baseEnd_6640253] using wordTrace_append hprefix tailTrace_6640253
  have hstable : (prefixWord ++ tailWord_6640253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640253).length < 2 ^ (prefixWord ++ tailWord_6640253).sum := by decide
  have hdescent : baseEnd_6640253 < baseStart_6640253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640276 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6640276 : Nat := 118140960795 + 6640276 * 2 ^ 59
def prefixEnd_6640276 : Nat := 4983230072969 + 3 ^ 40 * 6640276 * 2
def baseEnd_6640276 : Nat := 3409653266514767123311933

theorem tailTrace_6640276 : CollatzResearch.WordTrace tailWord_6640276 prefixEnd_6640276 3409653266514767123311933 := by
  unfold tailWord_6640276
  simp only [CollatzResearch.WordTrace]
  refine ⟨121095381245710797849038341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161460508327614397132051121 121095381245710797849038341)
  ·
    refine ⟨22705383983570774596694689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121095381245710797849038341 22705383983570774596694689)
    ·
      refine ⟨17029037987678080947521017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22705383983570774596694689 17029037987678080947521017)
      ·
        refine ⟨12771778490758560710640763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17029037987678080947521017 12771778490758560710640763)
        ·
          refine ⟨19157667736137841065961145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771778490758560710640763 19157667736137841065961145)
          ·
            refine ⟨14368250802103380799470859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19157667736137841065961145 14368250802103380799470859)
            ·
              refine ⟨21552376203155071199206289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14368250802103380799470859 21552376203155071199206289)
              ·
                refine ⟨16164282152366303399404717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21552376203155071199206289 16164282152366303399404717)
                ·
                  refine ⟨6061605807137363774776769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16164282152366303399404717 6061605807137363774776769)
                  ·
                    refine ⟨4546204355353022831082577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6061605807137363774776769 4546204355353022831082577)
                    ·
                      refine ⟨3409653266514767123311933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546204355353022831082577 3409653266514767123311933)
                      ·
                        rfl

theorem cell23_6640276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6640276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640276 prefixEnd_6640276 := by exact prefixLift 6640276
  have htrace : WordTrace (prefixWord ++ tailWord_6640276) baseStart_6640276 baseEnd_6640276 := by
    simpa [prefixWord, tailWord_6640276, baseEnd_6640276] using wordTrace_append hprefix tailTrace_6640276
  have hstable : (prefixWord ++ tailWord_6640276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640276).length < 2 ^ (prefixWord ++ tailWord_6640276).sum := by decide
  have hdescent : baseEnd_6640276 < baseStart_6640276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640292 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_6640292 : Nat := 118140960795 + 6640292 * 2 ^ 59
def prefixEnd_6640292 : Nat := 4983230072969 + 3 ^ 40 * 6640292 * 2
def baseEnd_6640292 : Nat := 3409661482205239060711859

theorem tailTrace_6640292 : CollatzResearch.WordTrace tailWord_6640292 prefixEnd_6640292 3409661482205239060711859 := by
  unfold tailWord_6640292
  simp only [CollatzResearch.WordTrace]
  refine ⟨121095673029681815215329565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161460897372909086953772753 121095673029681815215329565)
  ·
    refine ⟨45410877386130680705748587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121095673029681815215329565 45410877386130680705748587)
    ·
      refine ⟨68116316079196021058622881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45410877386130680705748587 68116316079196021058622881)
      ·
        refine ⟨51087237059397015793967161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68116316079196021058622881 51087237059397015793967161)
        ·
          refine ⟨38315427794547761845475371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51087237059397015793967161 38315427794547761845475371)
          ·
            refine ⟨57473141691821642768213057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38315427794547761845475371 57473141691821642768213057)
            ·
              refine ⟨43104856268866232076159793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57473141691821642768213057 43104856268866232076159793)
              ·
                refine ⟨32328642201649674057119845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43104856268866232076159793 32328642201649674057119845)
                ·
                  refine ⟨6061620412809313885709971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32328642201649674057119845 6061620412809313885709971)
                  ·
                    refine ⟨9092430619213970828564957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061620412809313885709971 9092430619213970828564957)
                    ·
                      refine ⟨3409661482205239060711859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092430619213970828564957 3409661482205239060711859)
                      ·
                        rfl

theorem cell23_6640292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_6640292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640292 prefixEnd_6640292 := by exact prefixLift 6640292
  have htrace : WordTrace (prefixWord ++ tailWord_6640292) baseStart_6640292 baseEnd_6640292 := by
    simpa [prefixWord, tailWord_6640292, baseEnd_6640292] using wordTrace_append hprefix tailTrace_6640292
  have hstable : (prefixWord ++ tailWord_6640292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640292).length < 2 ^ (prefixWord ++ tailWord_6640292).sum := by decide
  have hdescent : baseEnd_6640292 < baseStart_6640292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640309 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6640309 : Nat := 118140960795 + 6640309 * 2 ^ 59
def prefixEnd_6640309 : Nat := 4983230072969 + 3 ^ 40 * 6640309 * 2
def baseEnd_6640309 : Nat := 3409670211376365494199281

theorem tailTrace_6640309 : CollatzResearch.WordTrace tailWord_6640309 prefixEnd_6640309 3409670211376365494199281 := by
  unfold tailWord_6640309
  simp only [CollatzResearch.WordTrace]
  refine ⟨242191966100302042334027981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161461310733534694889351987 242191966100302042334027981)
  ·
    refine ⟨90821987287613265875260493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242191966100302042334027981 90821987287613265875260493)
    ·
      refine ⟨34058245232854974703222685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90821987287613265875260493 34058245232854974703222685)
      ·
        refine ⟨12771841962320615513708507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34058245232854974703222685 12771841962320615513708507)
        ·
          refine ⟨19157762943480923270562761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771841962320615513708507 19157762943480923270562761)
          ·
            refine ⟨14368322207610692452922071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19157762943480923270562761 14368322207610692452922071)
            ·
              refine ⟨21552483311416038679383107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14368322207610692452922071 21552483311416038679383107)
              ·
                refine ⟨32328724967124058019074661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21552483311416038679383107 32328724967124058019074661)
                ·
                  refine ⟨6061635931335760878576499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32328724967124058019074661 6061635931335760878576499)
                  ·
                    refine ⟨9092453897003641317864749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061635931335760878576499 9092453897003641317864749)
                    ·
                      refine ⟨3409670211376365494199281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092453897003641317864749 3409670211376365494199281)
                      ·
                        rfl

theorem cell23_6640309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6640309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640309 prefixEnd_6640309 := by exact prefixLift 6640309
  have htrace : WordTrace (prefixWord ++ tailWord_6640309) baseStart_6640309 baseEnd_6640309 := by
    simpa [prefixWord, tailWord_6640309, baseEnd_6640309] using wordTrace_append hprefix tailTrace_6640309
  have hstable : (prefixWord ++ tailWord_6640309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640309).length < 2 ^ (prefixWord ++ tailWord_6640309).sum := by decide
  have hdescent : baseEnd_6640309 < baseStart_6640309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640315 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 8, 2]
def baseStart_6640315 : Nat := 118140960795 + 6640315 * 2 ^ 59
def prefixEnd_6640315 : Nat := 4983230072969 + 3 ^ 40 * 6640315 * 2
def baseEnd_6640315 : Nat := 3409673292260292470724253

theorem tailTrace_6640315 : CollatzResearch.WordTrace tailWord_6640315 prefixEnd_6640315 3409673292260292470724253 := by
  unfold tailWord_6640315
  simp only [CollatzResearch.WordTrace]
  refine ⟨242192184938280305358746399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161461456625520203572497599 242192184938280305358746399)
  ·
    refine ⟨363288277407420458038119599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242192184938280305358746399 363288277407420458038119599)
    ·
      refine ⟨544932416111130687057179399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363288277407420458038119599 544932416111130687057179399)
      ·
        refine ⟨817398624166696030585769099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544932416111130687057179399 817398624166696030585769099)
        ·
          refine ⟨1226097936250044045878653649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817398624166696030585769099 1226097936250044045878653649)
          ·
            refine ⟨919573452187533034408990237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226097936250044045878653649 919573452187533034408990237)
            ·
              refine ⟨344840044570324887903371339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 919573452187533034408990237 344840044570324887903371339)
              ·
                refine ⟨517260066855487331855057009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344840044570324887903371339 517260066855487331855057009)
                ·
                  refine ⟨387945050141615498891292757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517260066855487331855057009 387945050141615498891292757)
                  ·
                    refine ⟨4546231056347056627632337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 387945050141615498891292757 4546231056347056627632337)
                    ·
                      refine ⟨3409673292260292470724253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546231056347056627632337 3409673292260292470724253)
                      ·
                        rfl

theorem cell23_6640315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8, 2].length) (baseStart_6640315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640315 prefixEnd_6640315 := by exact prefixLift 6640315
  have htrace : WordTrace (prefixWord ++ tailWord_6640315) baseStart_6640315 baseEnd_6640315 := by
    simpa [prefixWord, tailWord_6640315, baseEnd_6640315] using wordTrace_append hprefix tailTrace_6640315
  have hstable : (prefixWord ++ tailWord_6640315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640315).length < 2 ^ (prefixWord ++ tailWord_6640315).sum := by decide
  have hdescent : baseEnd_6640315 < baseStart_6640315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640365 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6640365 : Nat := 118140960795 + 6640365 * 2 ^ 59
def prefixEnd_6640365 : Nat := 4983230072969 + 3 ^ 40 * 6640365 * 2
def baseEnd_6640365 : Nat := 3409698966293017275099023

theorem tailTrace_6640365 : CollatzResearch.WordTrace tailWord_6640365 prefixEnd_6640365 3409698966293017275099023 := by
  unfold tailWord_6640365
  simp only [CollatzResearch.WordTrace]
  refine ⟨242194008588099163898066549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161462672392066109265377699 242194008588099163898066549)
  ·
    refine ⟨22705688305134296615443739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242194008588099163898066549 22705688305134296615443739)
    ·
      refine ⟨34058532457701444923165609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22705688305134296615443739 34058532457701444923165609)
      ·
        refine ⟨25543899343276083692374207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34058532457701444923165609 25543899343276083692374207)
        ·
          refine ⟨38315849014914125538561311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25543899343276083692374207 38315849014914125538561311)
          ·
            refine ⟨57473773522371188307841967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38315849014914125538561311 57473773522371188307841967)
            ·
              refine ⟨86210660283556782461762951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57473773522371188307841967 86210660283556782461762951)
              ·
                refine ⟨129315990425335173692644427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86210660283556782461762951 129315990425335173692644427)
                ·
                  refine ⟨193973985638002760538966641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129315990425335173692644427 193973985638002760538966641)
                  ·
                    refine ⟨145480489228502070404224981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193973985638002760538966641 145480489228502070404224981)
                    ·
                      refine ⟨3409698966293017275099023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145480489228502070404224981 3409698966293017275099023)
                      ·
                        rfl

theorem cell23_6640365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6640365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640365 prefixEnd_6640365 := by exact prefixLift 6640365
  have htrace : WordTrace (prefixWord ++ tailWord_6640365) baseStart_6640365 baseEnd_6640365 := by
    simpa [prefixWord, tailWord_6640365, baseEnd_6640365] using wordTrace_append hprefix tailTrace_6640365
  have hstable : (prefixWord ++ tailWord_6640365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640365).length < 2 ^ (prefixWord ++ tailWord_6640365).sum := by decide
  have hdescent : baseEnd_6640365 < baseStart_6640365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640385 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_6640385 : Nat := 118140960795 + 6640385 * 2 ^ 59
def prefixEnd_6640385 : Nat := 4983230072969 + 3 ^ 40 * 6640385 * 2
def baseEnd_6640385 : Nat := 1136569745302035732282977

theorem tailTrace_6640385 : CollatzResearch.WordTrace tailWord_6640385 prefixEnd_6640385 1136569745302035732282977 := by
  unfold tailWord_6640385
  simp only [CollatzResearch.WordTrace]
  refine ⟨242194738048026707313794609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161463158698684471542529739 242194738048026707313794609)
  ·
    refine ⟨181646053536020030485345957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242194738048026707313794609 181646053536020030485345957)
    ·
      refine ⟨34058635038003755716002367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181646053536020030485345957 34058635038003755716002367)
      ·
        refine ⟨51087952557005633574003551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34058635038003755716002367 51087952557005633574003551)
        ·
          refine ⟨76631928835508450361005327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51087952557005633574003551 76631928835508450361005327)
          ·
            refine ⟨114947893253262675541507991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76631928835508450361005327 114947893253262675541507991)
            ·
              refine ⟨172421839879894013312261987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114947893253262675541507991 172421839879894013312261987)
              ·
                refine ⟨258632759819841019968392981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172421839879894013312261987 258632759819841019968392981)
                ·
                  refine ⟨12123410616555047811018421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258632759819841019968392981 12123410616555047811018421)
                  ·
                    refine ⟨1136569745302035732282977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12123410616555047811018421 1136569745302035732282977)
                    ·
                      rfl

theorem cell23_6640385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_6640385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640385 prefixEnd_6640385 := by exact prefixLift 6640385
  have htrace : WordTrace (prefixWord ++ tailWord_6640385) baseStart_6640385 baseEnd_6640385 := by
    simpa [prefixWord, tailWord_6640385, baseEnd_6640385] using wordTrace_append hprefix tailTrace_6640385
  have hstable : (prefixWord ++ tailWord_6640385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640385).length < 2 ^ (prefixWord ++ tailWord_6640385).sum := by decide
  have hdescent : baseEnd_6640385 < baseStart_6640385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640466 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_6640466 : Nat := 118140960795 + 6640466 * 2 ^ 59
def prefixEnd_6640466 : Nat := 4983230072969 + 3 ^ 40 * 6640466 * 2
def baseEnd_6640466 : Nat := 1136583609279707126645353

theorem tailTrace_6640466 : CollatzResearch.WordTrace tailWord_6640466 prefixEnd_6640466 1136583609279707126645353 := by
  unfold tailWord_6640466
  simp only [CollatzResearch.WordTrace]
  refine ⟨60549423090183314536873313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161465128240488838764995501 60549423090183314536873313)
  ·
    refine ⟨45412067317637485902654985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60549423090183314536873313 45412067317637485902654985)
    ·
      refine ⟨34059050488228114426991239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45412067317637485902654985 34059050488228114426991239)
      ·
        refine ⟨51088575732342171640486859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34059050488228114426991239 51088575732342171640486859)
        ·
          refine ⟨76632863598513257460730289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51088575732342171640486859 76632863598513257460730289)
          ·
            refine ⟨57474647698884943095547717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76632863598513257460730289 57474647698884943095547717)
            ·
              refine ⟨10776496443540926830415197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57474647698884943095547717 10776496443540926830415197)
              ·
                refine ⟨4041186166327847561405699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10776496443540926830415197 4041186166327847561405699)
                ·
                  refine ⟨6061779249491771342108549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041186166327847561405699 6061779249491771342108549)
                  ·
                    refine ⟨1136583609279707126645353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6061779249491771342108549 1136583609279707126645353)
                    ·
                      rfl

theorem cell23_6640466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_6640466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640466 prefixEnd_6640466 := by exact prefixLift 6640466
  have htrace : WordTrace (prefixWord ++ tailWord_6640466) baseStart_6640466 baseEnd_6640466 := by
    simpa [prefixWord, tailWord_6640466, baseEnd_6640466] using wordTrace_append hprefix tailTrace_6640466
  have hstable : (prefixWord ++ tailWord_6640466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640466).length < 2 ^ (prefixWord ++ tailWord_6640466).sum := by decide
  have hdescent : baseEnd_6640466 < baseStart_6640466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640540 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6640540 : Nat := 118140960795 + 6640540 * 2 ^ 59
def prefixEnd_6640540 : Nat := 4983230072969 + 3 ^ 40 * 6640540 * 2
def baseEnd_6640540 : Nat := 3409788825407554090410719

theorem tailTrace_6640540 : CollatzResearch.WordTrace tailWord_6640540 prefixEnd_6640540 3409788825407554090410719 := by
  unfold tailWord_6640540
  simp only [CollatzResearch.WordTrace]
  refine ⟨121100195681232584392843537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161466927574976779190458049 121100195681232584392843537)
  ·
    refine ⟨90825146760924438294632653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121100195681232584392843537 90825146760924438294632653)
    ·
      refine ⟨34059430035346664360487245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90825146760924438294632653 34059430035346664360487245)
      ·
        refine ⟨12772286263254999135182717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34059430035346664360487245 12772286263254999135182717)
        ·
          refine ⟨4789607348720624675693519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12772286263254999135182717 4789607348720624675693519)
          ·
            refine ⟨7184411023080937013540279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789607348720624675693519 7184411023080937013540279)
            ·
              refine ⟨10776616534621405520310419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184411023080937013540279 10776616534621405520310419)
              ·
                refine ⟨16164924801932108280465629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776616534621405520310419 16164924801932108280465629)
                ·
                  refine ⟨6061846800724540605174611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16164924801932108280465629 6061846800724540605174611)
                  ·
                    refine ⟨9092770201086810907761917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061846800724540605174611 9092770201086810907761917)
                    ·
                      refine ⟨3409788825407554090410719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092770201086810907761917 3409788825407554090410719)
                      ·
                        rfl

theorem cell23_6640540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6640540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640540 prefixEnd_6640540 := by exact prefixLift 6640540
  have htrace : WordTrace (prefixWord ++ tailWord_6640540) baseStart_6640540 baseEnd_6640540 := by
    simpa [prefixWord, tailWord_6640540, baseEnd_6640540] using wordTrace_append hprefix tailTrace_6640540
  have hstable : (prefixWord ++ tailWord_6640540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640540).length < 2 ^ (prefixWord ++ tailWord_6640540).sum := by decide
  have hdescent : baseEnd_6640540 < baseStart_6640540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640580 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6640580 : Nat := 118140960795 + 6640580 * 2 ^ 59
def prefixEnd_6640580 : Nat := 4983230072969 + 3 ^ 40 * 6640580 * 2
def baseEnd_6640580 : Nat := 3409809364633733933910535

theorem tailTrace_6640580 : CollatzResearch.WordTrace tailWord_6640580 prefixEnd_6640580 3409809364633733933910535 := by
  unfold tailWord_6640580
  simp only [CollatzResearch.WordTrace]
  refine ⟨121100925141160127808571597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161467900188213503744762129 121100925141160127808571597)
  ·
    refine ⟨45412846927935047928214349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121100925141160127808571597 45412846927935047928214349)
    ·
      refine ⟨17029817597975642973080381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45412846927935047928214349 17029817597975642973080381)
      ·
        refine ⟨6386181599240866114905143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17029817597975642973080381 6386181599240866114905143)
        ·
          refine ⟨9579272398861299172357715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386181599240866114905143 9579272398861299172357715)
          ·
            refine ⟨14368908598291948758536573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579272398861299172357715 14368908598291948758536573)
            ·
              refine ⟨5388340724359480784451215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14368908598291948758536573 5388340724359480784451215)
              ·
                refine ⟨8082511086539221176676823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388340724359480784451215 8082511086539221176676823)
                ·
                  refine ⟨12123766629808831765015235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8082511086539221176676823 12123766629808831765015235)
                  ·
                    refine ⟨18185649944713247647522853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12123766629808831765015235 18185649944713247647522853)
                    ·
                      refine ⟨3409809364633733933910535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18185649944713247647522853 3409809364633733933910535)
                      ·
                        rfl

theorem cell23_6640580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6640580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640580 prefixEnd_6640580 := by exact prefixLift 6640580
  have htrace : WordTrace (prefixWord ++ tailWord_6640580) baseStart_6640580 baseEnd_6640580 := by
    simpa [prefixWord, tailWord_6640580, baseEnd_6640580] using wordTrace_append hprefix tailTrace_6640580
  have hstable : (prefixWord ++ tailWord_6640580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640580).length < 2 ^ (prefixWord ++ tailWord_6640580).sum := by decide
  have hdescent : baseEnd_6640580 < baseStart_6640580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640613 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6640613 : Nat := 118140960795 + 6640613 * 2 ^ 59
def prefixEnd_6640613 : Nat := 4983230072969 + 3 ^ 40 * 6640613 * 2
def baseEnd_6640613 : Nat := 3409826309495332304797883

theorem tailTrace_6640613 : CollatzResearch.WordTrace tailWord_6640613 prefixEnd_6640613 3409826309495332304797883 := by
  unfold tailWord_6640613
  simp only [CollatzResearch.WordTrace]
  refine ⟨242203053891200702253094493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161468702594133801502062995 242203053891200702253094493)
  ·
    refine ⟨90826145209200263344910435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242203053891200702253094493 90826145209200263344910435)
    ·
      refine ⟨136239217813800395017365653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90826145209200263344910435 136239217813800395017365653)
      ·
        refine ⟨6386213335021893516439015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136239217813800395017365653 6386213335021893516439015)
        ·
          refine ⟨9579320002532840274658523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386213335021893516439015 9579320002532840274658523)
          ·
            refine ⟨14368980003799260411987785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579320002532840274658523 14368980003799260411987785)
            ·
              refine ⟨10776735002849445308990839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14368980003799260411987785 10776735002849445308990839)
              ·
                refine ⟨16165102504274167963486259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776735002849445308990839 16165102504274167963486259)
                ·
                  refine ⟨24247653756411251945229389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16165102504274167963486259 24247653756411251945229389)
                  ·
                    refine ⟨9092870158654219479461021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24247653756411251945229389 9092870158654219479461021)
                    ·
                      refine ⟨3409826309495332304797883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9092870158654219479461021 3409826309495332304797883)
                      ·
                        rfl

theorem cell23_6640613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6640613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640613 prefixEnd_6640613 := by exact prefixLift 6640613
  have htrace : WordTrace (prefixWord ++ tailWord_6640613) baseStart_6640613 baseEnd_6640613 := by
    simpa [prefixWord, tailWord_6640613, baseEnd_6640613] using wordTrace_append hprefix tailTrace_6640613
  have hstable : (prefixWord ++ tailWord_6640613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640613).length < 2 ^ (prefixWord ++ tailWord_6640613).sum := by decide
  have hdescent : baseEnd_6640613 < baseStart_6640613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640632 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_6640632 : Nat := 118140960795 + 6640632 * 2 ^ 59
def prefixEnd_6640632 : Nat := 4983230072969 + 3 ^ 40 * 6640632 * 2
def baseEnd_6640632 : Nat := 3409836065627767730460295

theorem tailTrace_6640632 : CollatzResearch.WordTrace tailWord_6640632 prefixEnd_6640632 3409836065627767730460295 := by
  unfold tailWord_6640632
  simp only [CollatzResearch.WordTrace]
  refine ⟨121101873439065934249018075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161469164585421245665357433 121101873439065934249018075)
  ·
    refine ⟨181652810158598901373527113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121101873439065934249018075 181652810158598901373527113)
    ·
      refine ⟨136239607618949176030145335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181652810158598901373527113 136239607618949176030145335)
      ·
        refine ⟨204359411428423764045218003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136239607618949176030145335 204359411428423764045218003)
        ·
          refine ⟨306539117142635646067827005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204359411428423764045218003 306539117142635646067827005)
          ·
            refine ⟨114952168928488367275435127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306539117142635646067827005 114952168928488367275435127)
            ·
              refine ⟨172428253392732550913152691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114952168928488367275435127 172428253392732550913152691)
              ·
                refine ⟨258642380089098826369729037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172428253392732550913152691 258642380089098826369729037)
                ·
                  refine ⟨96990892533412059888648389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258642380089098826369729037 96990892533412059888648389)
                  ·
                    refine ⟨18185792350014761229121573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96990892533412059888648389 18185792350014761229121573)
                    ·
                      refine ⟨3409836065627767730460295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18185792350014761229121573 3409836065627767730460295)
                      ·
                        rfl

theorem cell23_6640632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_6640632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640632 prefixEnd_6640632 := by exact prefixLift 6640632
  have htrace : WordTrace (prefixWord ++ tailWord_6640632) baseStart_6640632 baseEnd_6640632 := by
    simpa [prefixWord, tailWord_6640632, baseEnd_6640632] using wordTrace_append hprefix tailTrace_6640632
  have hstable : (prefixWord ++ tailWord_6640632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640632).length < 2 ^ (prefixWord ++ tailWord_6640632).sum := by decide
  have hdescent : baseEnd_6640632 < baseStart_6640632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640636 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_6640636 : Nat := 118140960795 + 6640636 * 2 ^ 59
def prefixEnd_6640636 : Nat := 4983230072969 + 3 ^ 40 * 6640636 * 2
def baseEnd_6640636 : Nat := 3409838119550385714810277

theorem tailTrace_6640636 : CollatzResearch.WordTrace tailWord_6640636 prefixEnd_6640636 3409838119550385714810277 := by
  unfold tailWord_6640636
  simp only [CollatzResearch.WordTrace]
  refine ⟨121101946385058688590590881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161469261846744918120787841 121101946385058688590590881)
  ·
    refine ⟨90826459788794016442943161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121101946385058688590590881 90826459788794016442943161)
    ·
      refine ⟨68119844841595512332207371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90826459788794016442943161 68119844841595512332207371)
      ·
        refine ⟨102179767262393268498311057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68119844841595512332207371 102179767262393268498311057)
        ·
          refine ⟨76634825446794951373733293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102179767262393268498311057 76634825446794951373733293)
          ·
            refine ⟨28738059542548106765149985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76634825446794951373733293 28738059542548106765149985)
            ·
              refine ⟨21553544656911080073862489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28738059542548106765149985 21553544656911080073862489)
              ·
                refine ⟨16165158492683310055396867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21553544656911080073862489 16165158492683310055396867)
                ·
                  refine ⟨24247737739024965083095301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16165158492683310055396867 24247737739024965083095301)
                  ·
                    refine ⟨4546450826067180953080369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24247737739024965083095301 4546450826067180953080369)
                    ·
                      refine ⟨3409838119550385714810277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546450826067180953080369 3409838119550385714810277)
                      ·
                        rfl

theorem cell23_6640636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_6640636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640636 prefixEnd_6640636 := by exact prefixLift 6640636
  have htrace : WordTrace (prefixWord ++ tailWord_6640636) baseStart_6640636 baseEnd_6640636 := by
    simpa [prefixWord, tailWord_6640636, baseEnd_6640636] using wordTrace_append hprefix tailTrace_6640636
  have hstable : (prefixWord ++ tailWord_6640636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640636).length < 2 ^ (prefixWord ++ tailWord_6640636).sum := by decide
  have hdescent : baseEnd_6640636 < baseStart_6640636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640689 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_6640689 : Nat := 118140960795 + 6640689 * 2 ^ 59
def prefixEnd_6640689 : Nat := 4983230072969 + 3 ^ 40 * 6640689 * 2
def baseEnd_6640689 : Nat := 1136621778008358002482511

theorem tailTrace_6640689 : CollatzResearch.WordTrace tailWord_6640689 prefixEnd_6640689 1136621778008358002482511 := by
  unfold tailWord_6640689
  simp only [CollatzResearch.WordTrace]
  refine ⟨242205825838925367232861121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161470550559283578155240747 242205825838925367232861121)
  ·
    refine ⟨181654369379194025424645841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242205825838925367232861121 181654369379194025424645841)
    ·
      refine ⟨136240777034395519068484381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181654369379194025424645841 136240777034395519068484381)
      ·
        refine ⟨51090291387898319650681643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136240777034395519068484381 51090291387898319650681643)
        ·
          refine ⟨76635437081847479476022465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51090291387898319650681643 76635437081847479476022465)
          ·
            refine ⟨57476577811385609607016849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76635437081847479476022465 57476577811385609607016849)
            ·
              refine ⟨43107433358539207205262637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57476577811385609607016849 43107433358539207205262637)
              ·
                refine ⟨16165287509452202701973489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43107433358539207205262637 16165287509452202701973489)
                ·
                  refine ⟨12123965632089152026480117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16165287509452202701973489 12123965632089152026480117)
                  ·
                    refine ⟨1136621778008358002482511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12123965632089152026480117 1136621778008358002482511)
                    ·
                      rfl

theorem cell23_6640689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_6640689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640689 prefixEnd_6640689 := by exact prefixLift 6640689
  have htrace : WordTrace (prefixWord ++ tailWord_6640689) baseStart_6640689 baseEnd_6640689 := by
    simpa [prefixWord, tailWord_6640689, baseEnd_6640689] using wordTrace_append hprefix tailTrace_6640689
  have hstable : (prefixWord ++ tailWord_6640689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640689).length < 2 ^ (prefixWord ++ tailWord_6640689).sum := by decide
  have hdescent : baseEnd_6640689 < baseStart_6640689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640709 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_6640709 : Nat := 118140960795 + 6640709 * 2 ^ 59
def prefixEnd_6640709 : Nat := 4983230072969 + 3 ^ 40 * 6640709 * 2
def baseEnd_6640709 : Nat := 3409875603638163929197441

theorem tailTrace_6640709 : CollatzResearch.WordTrace tailWord_6640709 prefixEnd_6640709 3409875603638163929197441 := by
  unfold tailWord_6640709
  simp only [CollatzResearch.WordTrace]
  refine ⟨242206555298852910648589181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161471036865901940432392787 242206555298852910648589181)
  ·
    refine ⟨90827458237069841493220943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242206555298852910648589181 90827458237069841493220943)
    ·
      refine ⟨136241187355604762239831415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90827458237069841493220943 136241187355604762239831415)
      ·
        refine ⟨204361781033407143359747123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136241187355604762239831415 204361781033407143359747123)
        ·
          refine ⟨306542671550110715039620685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204361781033407143359747123 306542671550110715039620685)
          ·
            refine ⟨114953501831291518139857757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306542671550110715039620685 114953501831291518139857757)
            ·
              refine ⟨43107563186734319302446659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114953501831291518139857757 43107563186734319302446659)
              ·
                refine ⟨64661344780101478953669989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43107563186734319302446659 64661344780101478953669989)
                ·
                  refine ⟨12124002146269027303813123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64661344780101478953669989 12124002146269027303813123)
                  ·
                    refine ⟨18186003219403540955719685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12124002146269027303813123 18186003219403540955719685)
                    ·
                      refine ⟨3409875603638163929197441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18186003219403540955719685 3409875603638163929197441)
                      ·
                        rfl

theorem cell23_6640709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_6640709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640709 prefixEnd_6640709 := by exact prefixLift 6640709
  have htrace : WordTrace (prefixWord ++ tailWord_6640709) baseStart_6640709 baseEnd_6640709 := by
    simpa [prefixWord, tailWord_6640709, baseEnd_6640709] using wordTrace_append hprefix tailTrace_6640709
  have hstable : (prefixWord ++ tailWord_6640709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640709).length < 2 ^ (prefixWord ++ tailWord_6640709).sum := by decide
  have hdescent : baseEnd_6640709 < baseStart_6640709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640729 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_6640729 : Nat := 118140960795 + 6640729 * 2 ^ 59
def prefixEnd_6640729 : Nat := 4983230072969 + 3 ^ 40 * 6640729 * 2
def baseEnd_6640729 : Nat := 3409885873251253850947349

theorem tailTrace_6640729 : CollatzResearch.WordTrace tailWord_6640729 prefixEnd_6640729 3409885873251253850947349 := by
  unfold tailWord_6640729
  simp only [CollatzResearch.WordTrace]
  refine ⟨242207284758780454064317241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161471523172520302709544827 242207284758780454064317241)
  ·
    refine ⟨181655463569085340548237931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242207284758780454064317241 181655463569085340548237931)
    ·
      refine ⟨272483195353628010822356897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181655463569085340548237931 272483195353628010822356897)
      ·
        refine ⟨204362396515221008116767673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272483195353628010822356897 204362396515221008116767673)
        ·
          refine ⟨153271797386415756087575755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204362396515221008116767673 153271797386415756087575755)
          ·
            refine ⟨229907696079623634131363633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153271797386415756087575755 229907696079623634131363633)
            ·
              refine ⟨172430772059717725598522725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229907696079623634131363633 172430772059717725598522725)
              ·
                refine ⟨32330769761197073549723011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172430772059717725598522725 32330769761197073549723011)
                ·
                  refine ⟨48496154641795610324584517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32330769761197073549723011 48496154641795610324584517)
                  ·
                    refine ⟨9093028995336676935859597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48496154641795610324584517 9093028995336676935859597)
                    ·
                      refine ⟨3409885873251253850947349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093028995336676935859597 3409885873251253850947349)
                      ·
                        rfl

theorem cell23_6640729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_6640729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640729 prefixEnd_6640729 := by exact prefixLift 6640729
  have htrace : WordTrace (prefixWord ++ tailWord_6640729) baseStart_6640729 baseEnd_6640729 := by
    simpa [prefixWord, tailWord_6640729, baseEnd_6640729] using wordTrace_append hprefix tailTrace_6640729
  have hstable : (prefixWord ++ tailWord_6640729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640729).length < 2 ^ (prefixWord ++ tailWord_6640729).sum := by decide
  have hdescent : baseEnd_6640729 < baseStart_6640729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640796 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6640796 : Nat := 118140960795 + 6640796 * 2 ^ 59
def prefixEnd_6640796 : Nat := 4983230072969 + 3 ^ 40 * 6640796 * 2
def baseEnd_6640796 : Nat := 1136640092151701696269847

theorem tailTrace_6640796 : CollatzResearch.WordTrace tailWord_6640796 prefixEnd_6640796 1136640092151701696269847 := by
  unfold tailWord_6640796
  simp only [CollatzResearch.WordTrace]
  refine ⟨121104864224768862253503121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161473152299691816338004161 121104864224768862253503121)
  ·
    refine ⟨90828648168576646690127341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121104864224768862253503121 90828648168576646690127341)
    ·
      refine ⟨34060743063216242508797753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90828648168576646690127341 34060743063216242508797753)
      ·
        refine ⟨25545557297412181881598315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34060743063216242508797753 25545557297412181881598315)
        ·
          refine ⟨38318335946118272822397473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25545557297412181881598315 38318335946118272822397473)
          ·
            refine ⟨28738751959588704616798105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38318335946118272822397473 28738751959588704616798105)
            ·
              refine ⟨21554063969691528462598579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28738751959588704616798105 21554063969691528462598579)
              ·
                refine ⟨32331095954537292693897869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21554063969691528462598579 32331095954537292693897869)
                ·
                  refine ⟨12124160982951484760211701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32331095954537292693897869 12124160982951484760211701)
                  ·
                    refine ⟨1136640092151701696269847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12124160982951484760211701 1136640092151701696269847)
                    ·
                      rfl

theorem cell23_6640796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6640796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640796 prefixEnd_6640796 := by exact prefixLift 6640796
  have htrace : WordTrace (prefixWord ++ tailWord_6640796) baseStart_6640796 baseEnd_6640796 := by
    simpa [prefixWord, tailWord_6640796, baseEnd_6640796] using wordTrace_append hprefix tailTrace_6640796
  have hstable : (prefixWord ++ tailWord_6640796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640796).length < 2 ^ (prefixWord ++ tailWord_6640796).sum := by decide
  have hdescent : baseEnd_6640796 < baseStart_6640796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640816 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_6640816 : Nat := 118140960795 + 6640816 * 2 ^ 59
def prefixEnd_6640816 : Nat := 4983230072969 + 3 ^ 40 * 6640816 * 2
def baseEnd_6640816 : Nat := 3409930546068195010559449

theorem tailTrace_6640816 : CollatzResearch.WordTrace tailWord_6640816 prefixEnd_6640816 3409930546068195010559449 := by
  unfold tailWord_6640816
  simp only [CollatzResearch.WordTrace]
  refine ⟨121105228954732633961367151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161473638606310178615156201 121105228954732633961367151)
  ·
    refine ⟨181657843432098950942050727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121105228954732633961367151 181657843432098950942050727)
    ·
      refine ⟨272486765148148426413076091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181657843432098950942050727 272486765148148426413076091)
      ·
        refine ⟨408730147722222639619614137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272486765148148426413076091 408730147722222639619614137)
        ·
          refine ⟨306547610791666979714710603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408730147722222639619614137 306547610791666979714710603)
          ·
            refine ⟨459821416187500469572065905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306547610791666979714710603 459821416187500469572065905)
            ·
              refine ⟨344866062140625352179049429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459821416187500469572065905 344866062140625352179049429)
              ·
                refine ⟨8082798331420906691696471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 344866062140625352179049429 8082798331420906691696471)
                ·
                  refine ⟨12124197497131360037544707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8082798331420906691696471 12124197497131360037544707)
                  ·
                    refine ⟨18186296245697040056317061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12124197497131360037544707 18186296245697040056317061)
                    ·
                      refine ⟨3409930546068195010559449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18186296245697040056317061 3409930546068195010559449)
                      ·
                        rfl

theorem cell23_6640816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_6640816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640816 prefixEnd_6640816 := by exact prefixLift 6640816
  have htrace : WordTrace (prefixWord ++ tailWord_6640816) baseStart_6640816 baseEnd_6640816 := by
    simpa [prefixWord, tailWord_6640816, baseEnd_6640816] using wordTrace_append hprefix tailTrace_6640816
  have hstable : (prefixWord ++ tailWord_6640816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640816).length < 2 ^ (prefixWord ++ tailWord_6640816).sum := by decide
  have hdescent : baseEnd_6640816 < baseStart_6640816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640850 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6640850 : Nat := 118140960795 + 6640850 * 2 ^ 59
def prefixEnd_6640850 : Nat := 4983230072969 + 3 ^ 40 * 6640850 * 2
def baseEnd_6640850 : Nat := 3409948004410447877534293

theorem tailTrace_6640850 : CollatzResearch.WordTrace tailWord_6640850 prefixEnd_6640850 3409948004410447877534293 := by
  unfold tailWord_6640850
  simp only [CollatzResearch.WordTrace]
  refine ⟨60552924497835522932368001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161474465327561394486314669 60552924497835522932368001)
  ·
    refine ⟨45414693373376642199276001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60552924497835522932368001 45414693373376642199276001)
    ·
      refine ⟨34061020030032481649457001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45414693373376642199276001 34061020030032481649457001)
      ·
        refine ⟨25545765022524361237092751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34061020030032481649457001 25545765022524361237092751)
        ·
          refine ⟨38318647533786541855639127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25545765022524361237092751 38318647533786541855639127)
          ·
            refine ⟨57477971300679812783458691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38318647533786541855639127 57477971300679812783458691)
            ·
              refine ⟨86216956951019719175188037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57477971300679812783458691 86216956951019719175188037)
              ·
                refine ⟨16165679428316197345347757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86216956951019719175188037 16165679428316197345347757)
                ·
                  refine ⟨6062129785618574004505409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16165679428316197345347757 6062129785618574004505409)
                  ·
                    refine ⟨4546597339213930503379057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6062129785618574004505409 4546597339213930503379057)
                    ·
                      refine ⟨3409948004410447877534293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546597339213930503379057 3409948004410447877534293)
                      ·
                        rfl

theorem cell23_6640850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6640850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640850 prefixEnd_6640850 := by exact prefixLift 6640850
  have htrace : WordTrace (prefixWord ++ tailWord_6640850) baseStart_6640850 baseEnd_6640850 := by
    simpa [prefixWord, tailWord_6640850, baseEnd_6640850] using wordTrace_append hprefix tailTrace_6640850
  have hstable : (prefixWord ++ tailWord_6640850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640850).length < 2 ^ (prefixWord ++ tailWord_6640850).sum := by decide
  have hdescent : baseEnd_6640850 < baseStart_6640850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640856 : List Nat := [2, 1, 2, 2, 5, 1, 1, 9]
def baseStart_6640856 : Nat := 118140960795 + 6640856 * 2 ^ 59
def prefixEnd_6640856 : Nat := 4983230072969 + 3 ^ 40 * 6640856 * 2
def baseEnd_6640856 : Nat := 126294484640532402002195

theorem tailTrace_6640856 : CollatzResearch.WordTrace tailWord_6640856 prefixEnd_6640856 126294484640532402002195 := by
  unfold tailWord_6640856
  simp only [CollatzResearch.WordTrace]
  refine ⟨121105958414660177377095211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161474611219546903169460281 121105958414660177377095211)
  ·
    refine ⟨181658937621990266065642817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121105958414660177377095211 181658937621990266065642817)
    ·
      refine ⟨136244203216492699549232113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181658937621990266065642817 136244203216492699549232113)
      ·
        refine ⟨102183152412369524661924085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136244203216492699549232113 102183152412369524661924085)
        ·
          refine ⟨9579670538659642937055383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102183152412369524661924085 9579670538659642937055383)
          ·
            refine ⟨14369505807989464405583075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579670538659642937055383 14369505807989464405583075)
            ·
              refine ⟨21554258711984196608374613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14369505807989464405583075 21554258711984196608374613)
              ·
                refine ⟨126294484640532402002195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21554258711984196608374613 126294484640532402002195)
                ·
                  rfl

theorem cell23_6640856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 9].length) (baseStart_6640856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640856 prefixEnd_6640856 := by exact prefixLift 6640856
  have htrace : WordTrace (prefixWord ++ tailWord_6640856) baseStart_6640856 baseEnd_6640856 := by
    simpa [prefixWord, tailWord_6640856, baseEnd_6640856] using wordTrace_append hprefix tailTrace_6640856
  have hstable : (prefixWord ++ tailWord_6640856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640856).length < 2 ^ (prefixWord ++ tailWord_6640856).sum := by decide
  have hdescent : baseEnd_6640856 < baseStart_6640856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640861 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6640861 : Nat := 118140960795 + 6640861 * 2 ^ 59
def prefixEnd_6640861 : Nat := 4983230072969 + 3 ^ 40 * 6640861 * 2
def baseEnd_6640861 : Nat := 3409953652697647334496743

theorem tailTrace_6640861 : CollatzResearch.WordTrace tailWord_6640861 prefixEnd_6640861 3409953652697647334496743 := by
  unfold tailWord_6640861
  simp only [CollatzResearch.WordTrace]
  refine ⟨242212099194302240608122437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161474732796201493738748291 242212099194302240608122437)
  ·
    refine ⟨45414768598931670114022957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242212099194302240608122437 45414768598931670114022957)
    ·
      refine ⟨17030538224599376292758609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45414768598931670114022957 17030538224599376292758609)
      ·
        refine ⟨12772903668449532219568957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17030538224599376292758609 12772903668449532219568957)
        ·
          refine ⟨4789838875668574582338359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12772903668449532219568957 4789838875668574582338359)
          ·
            refine ⟨7184758313502861873507539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789838875668574582338359 7184758313502861873507539)
            ·
              refine ⟨10777137470254292810261309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184758313502861873507539 10777137470254292810261309)
              ·
                refine ⟨4041426551345359803847991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10777137470254292810261309 4041426551345359803847991)
                ·
                  refine ⟨6062139827018039705771987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041426551345359803847991 6062139827018039705771987)
                  ·
                    refine ⟨9093209740527059558657981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062139827018039705771987 9093209740527059558657981)
                    ·
                      refine ⟨3409953652697647334496743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093209740527059558657981 3409953652697647334496743)
                      ·
                        rfl

theorem cell23_6640861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6640861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640861 prefixEnd_6640861 := by exact prefixLift 6640861
  have htrace : WordTrace (prefixWord ++ tailWord_6640861) baseStart_6640861 baseEnd_6640861 := by
    simpa [prefixWord, tailWord_6640861, baseEnd_6640861] using wordTrace_append hprefix tailTrace_6640861
  have hstable : (prefixWord ++ tailWord_6640861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640861).length < 2 ^ (prefixWord ++ tailWord_6640861).sum := by decide
  have hdescent : baseEnd_6640861 < baseStart_6640861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640883 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 3]
def baseStart_6640883 : Nat := 118140960795 + 6640883 * 2 ^ 59
def prefixEnd_6640883 : Nat := 4983230072969 + 3 ^ 40 * 6640883 * 2
def baseEnd_6640883 : Nat := 3409964949272046248421641

theorem tailTrace_6640883 : CollatzResearch.WordTrace tailWord_6640883 prefixEnd_6640883 3409964949272046248421641 := by
  unfold tailWord_6640883
  simp only [CollatzResearch.WordTrace]
  refine ⟨242212901600222538365423303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161475267733481692243615535 242212901600222538365423303)
  ·
    refine ⟨363319352400333807548134955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242212901600222538365423303 363319352400333807548134955)
    ·
      refine ⟨544979028600500711322202433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363319352400333807548134955 544979028600500711322202433)
      ·
        refine ⟨408734271450375533491651825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544979028600500711322202433 408734271450375533491651825)
        ·
          refine ⟨306550703587781650118738869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408734271450375533491651825 306550703587781650118738869)
          ·
            refine ⟨28739128461354529698631769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306550703587781650118738869 28739128461354529698631769)
            ·
              refine ⟨21554346346015897273973827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28739128461354529698631769 21554346346015897273973827)
              ·
                refine ⟨32331519519023845910960741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21554346346015897273973827 32331519519023845910960741)
                ·
                  refine ⟨6062159909816971108305139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32331519519023845910960741 6062159909816971108305139)
                  ·
                    refine ⟨9093239864725456662457709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062159909816971108305139 9093239864725456662457709)
                    ·
                      refine ⟨3409964949272046248421641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093239864725456662457709 3409964949272046248421641)
                      ·
                        rfl

theorem cell23_6640883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_6640883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640883 prefixEnd_6640883 := by exact prefixLift 6640883
  have htrace : WordTrace (prefixWord ++ tailWord_6640883) baseStart_6640883 baseEnd_6640883 := by
    simpa [prefixWord, tailWord_6640883, baseEnd_6640883] using wordTrace_append hprefix tailTrace_6640883
  have hstable : (prefixWord ++ tailWord_6640883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640883).length < 2 ^ (prefixWord ++ tailWord_6640883).sum := by decide
  have hdescent : baseEnd_6640883 < baseStart_6640883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640886 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6640886 : Nat := 118140960795 + 6640886 * 2 ^ 59
def prefixEnd_6640886 : Nat := 4983230072969 + 3 ^ 40 * 6640886 * 2
def baseEnd_6640886 : Nat := 1136655496571336578894709

theorem tailTrace_6640886 : CollatzResearch.WordTrace tailWord_6640886 prefixEnd_6640886 1136655496571336578894709 := by
  unfold tailWord_6640886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138313188700729367361407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161475340679474446585188341 15138313188700729367361407)
  ·
    refine ⟨22707469783051094051042111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15138313188700729367361407 22707469783051094051042111)
    ·
      refine ⟨34061204674576641076563167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22707469783051094051042111 34061204674576641076563167)
      ·
        refine ⟨51091807011864961614844751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34061204674576641076563167 51091807011864961614844751)
        ·
          refine ⟨76637710517797442422267127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51091807011864961614844751 76637710517797442422267127)
          ·
            refine ⟨114956565776696163633400691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76637710517797442422267127 114956565776696163633400691)
            ·
              refine ⟨172434848665044245450101037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114956565776696163633400691 172434848665044245450101037)
              ·
                refine ⟨64663068249391592043787889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172434848665044245450101037 64663068249391592043787889)
                ·
                  refine ⟨48497301187043694032840917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64663068249391592043787889 48497301187043694032840917)
                  ·
                    refine ⟨1136655496571336578894709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48497301187043694032840917 1136655496571336578894709)
                    ·
                      rfl

theorem cell23_6640886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6640886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640886 prefixEnd_6640886 := by exact prefixLift 6640886
  have htrace : WordTrace (prefixWord ++ tailWord_6640886) baseStart_6640886 baseEnd_6640886 := by
    simpa [prefixWord, tailWord_6640886, baseEnd_6640886] using wordTrace_append hprefix tailTrace_6640886
  have hstable : (prefixWord ++ tailWord_6640886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640886).length < 2 ^ (prefixWord ++ tailWord_6640886).sum := by decide
  have hdescent : baseEnd_6640886 < baseStart_6640886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640910 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6640910 : Nat := 118140960795 + 6640910 * 2 ^ 59
def prefixEnd_6640910 : Nat := 4983230072969 + 3 ^ 40 * 6640910 * 2
def baseEnd_6640910 : Nat := 3409978813249717642784017

theorem tailTrace_6640910 : CollatzResearch.WordTrace tailWord_6640910 prefixEnd_6640910 3409978813249717642784017 := by
  unfold tailWord_6640910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30276735796390590247082023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161475924247416481317770789 30276735796390590247082023)
  ·
    refine ⟨45415103694585885370623035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30276735796390590247082023 45415103694585885370623035)
    ·
      refine ⟨68122655541878828055934553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45415103694585885370623035 68122655541878828055934553)
      ·
        refine ⟨51091991656409121041950915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68122655541878828055934553 51091991656409121041950915)
        ·
          refine ⟨76637987484613681562926373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51091991656409121041950915 76637987484613681562926373)
          ·
            refine ⟨14369622653365065293048695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76637987484613681562926373 14369622653365065293048695)
            ·
              refine ⟨21554433980047597939573043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14369622653365065293048695 21554433980047597939573043)
              ·
                refine ⟨32331650970071396909359565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21554433980047597939573043 32331650970071396909359565)
                ·
                  refine ⟨12124369113776773841009837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32331650970071396909359565 12124369113776773841009837)
                  ·
                    refine ⟨4546638417666290190378689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12124369113776773841009837 4546638417666290190378689)
                    ·
                      refine ⟨3409978813249717642784017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546638417666290190378689 3409978813249717642784017)
                      ·
                        rfl

theorem cell23_6640910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6640910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640910 prefixEnd_6640910 := by exact prefixLift 6640910
  have htrace : WordTrace (prefixWord ++ tailWord_6640910) baseStart_6640910 baseEnd_6640910 := by
    simpa [prefixWord, tailWord_6640910, baseEnd_6640910] using wordTrace_append hprefix tailTrace_6640910
  have hstable : (prefixWord ++ tailWord_6640910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640910).length < 2 ^ (prefixWord ++ tailWord_6640910).sum := by decide
  have hdescent : baseEnd_6640910 < baseStart_6640910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640976 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_6640976 : Nat := 118140960795 + 6640976 * 2 ^ 59
def prefixEnd_6640976 : Nat := 4983230072969 + 3 ^ 40 * 6640976 * 2
def baseEnd_6640976 : Nat := 1136670900990971461519571

theorem tailTrace_6640976 : CollatzResearch.WordTrace tailWord_6640976 prefixEnd_6640976 1136670900990971461519571 := by
  unfold tailWord_6640976
  simp only [CollatzResearch.WordTrace]
  refine ⟨121108146794442807624279391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161477529059257076832372521 121108146794442807624279391)
  ·
    refine ⟨181662220191664211436419087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121108146794442807624279391 181662220191664211436419087)
    ·
      refine ⟨272493330287496317154628631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181662220191664211436419087 272493330287496317154628631)
      ·
        refine ⟨408739995431244475731942947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272493330287496317154628631 408739995431244475731942947)
        ·
          refine ⟨613109993146866713597914421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408739995431244475731942947 613109993146866713597914421)
          ·
            refine ⟨57479061857518754399804477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613109993146866713597914421 57479061857518754399804477)
            ·
              refine ⟨21554648196569532899926679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57479061857518754399804477 21554648196569532899926679)
              ·
                refine ⟨32331972294854299349890019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21554648196569532899926679 32331972294854299349890019)
                ·
                  refine ⟨48497958442281449024835029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32331972294854299349890019 48497958442281449024835029)
                  ·
                    refine ⟨1136670900990971461519571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48497958442281449024835029 1136670900990971461519571)
                    ·
                      rfl

theorem cell23_6640976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_6640976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640976 prefixEnd_6640976 := by exact prefixLift 6640976
  have htrace : WordTrace (prefixWord ++ tailWord_6640976) baseStart_6640976 baseEnd_6640976 := by
    simpa [prefixWord, tailWord_6640976, baseEnd_6640976] using wordTrace_append hprefix tailTrace_6640976
  have hstable : (prefixWord ++ tailWord_6640976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640976).length < 2 ^ (prefixWord ++ tailWord_6640976).sum := by decide
  have hdescent : baseEnd_6640976 < baseStart_6640976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640980 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6640980 : Nat := 118140960795 + 6640980 * 2 ^ 59
def prefixEnd_6640980 : Nat := 4983230072969 + 3 ^ 40 * 6640980 * 2
def baseEnd_6640980 : Nat := 378890528543948040989855

theorem tailTrace_6640980 : CollatzResearch.WordTrace tailWord_6640980 prefixEnd_6640980 378890528543948040989855 := by
  unfold tailWord_6640980
  simp only [CollatzResearch.WordTrace]
  refine ⟨121108219740435561965852197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161477626320580749287802929 121108219740435561965852197)
  ·
    refine ⟨22707791201331667868597287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121108219740435561965852197 22707791201331667868597287)
    ·
      refine ⟨34061686801997501802895931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22707791201331667868597287 34061686801997501802895931)
      ·
        refine ⟨51092530202996252704343897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34061686801997501802895931 51092530202996252704343897)
        ·
          refine ⟨38319397652247189528257923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51092530202996252704343897 38319397652247189528257923)
          ·
            refine ⟨57479096478370784292386885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38319397652247189528257923 57479096478370784292386885)
            ·
              refine ⟨10777330589694522054822541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57479096478370784292386885 10777330589694522054822541)
              ·
                refine ⟨4041498971135445770558453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10777330589694522054822541 4041498971135445770558453)
                ·
                  refine ⟨378890528543948040989855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041498971135445770558453 378890528543948040989855)
                  ·
                    rfl

theorem cell23_6640980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6640980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640980 prefixEnd_6640980 := by exact prefixLift 6640980
  have htrace : WordTrace (prefixWord ++ tailWord_6640980) baseStart_6640980 baseEnd_6640980 := by
    simpa [prefixWord, tailWord_6640980, baseEnd_6640980] using wordTrace_append hprefix tailTrace_6640980
  have hstable : (prefixWord ++ tailWord_6640980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640980).length < 2 ^ (prefixWord ++ tailWord_6640980).sum := by decide
  have hdescent : baseEnd_6640980 < baseStart_6640980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6640986 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_6640986 : Nat := 118140960795 + 6640986 * 2 ^ 59
def prefixEnd_6640986 : Nat := 4983230072969 + 3 ^ 40 * 6640986 * 2
def baseEnd_6640986 : Nat := 3410017837779459345433667

theorem tailTrace_6640986 : CollatzResearch.WordTrace tailWord_6640986 prefixEnd_6640986 3410017837779459345433667 := by
  unfold tailWord_6640986
  simp only [CollatzResearch.WordTrace]
  refine ⟨60554164579712346739105703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161477772212566257970948541 60554164579712346739105703)
  ·
    refine ⟨90831246869568520108658555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60554164579712346739105703 90831246869568520108658555)
    ·
      refine ⟨136246870304352780162987833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90831246869568520108658555 136246870304352780162987833)
      ·
        refine ⟨102185152728264585122240875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136246870304352780162987833 102185152728264585122240875)
        ·
          refine ⟨153277729092396877683361313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102185152728264585122240875 153277729092396877683361313)
          ·
            refine ⟨114958296819297658262520985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153277729092396877683361313 114958296819297658262520985)
            ·
              refine ⟨86218722614473243696890739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114958296819297658262520985 86218722614473243696890739)
              ·
                refine ⟨129328083921709865545336109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86218722614473243696890739 129328083921709865545336109)
                ·
                  refine ⟨48498031470641199579501041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129328083921709865545336109 48498031470641199579501041)
                  ·
                    refine ⟨36373523602980899684625781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48498031470641199579501041 36373523602980899684625781)
                    ·
                      refine ⟨3410017837779459345433667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36373523602980899684625781 3410017837779459345433667)
                      ·
                        rfl

theorem cell23_6640986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_6640986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6640986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6640986 prefixEnd_6640986 := by exact prefixLift 6640986
  have htrace : WordTrace (prefixWord ++ tailWord_6640986) baseStart_6640986 baseEnd_6640986 := by
    simpa [prefixWord, tailWord_6640986, baseEnd_6640986] using wordTrace_append hprefix tailTrace_6640986
  have hstable : (prefixWord ++ tailWord_6640986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6640986).length < 2 ^ (prefixWord ++ tailWord_6640986).sum := by decide
  have hdescent : baseEnd_6640986 < baseStart_6640986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6640986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641036 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 10]
def baseStart_6641036 : Nat := 118140960795 + 6641036 * 2 ^ 59
def prefixEnd_6641036 : Nat := 4983230072969 + 3 ^ 40 * 6641036 * 2
def baseEnd_6641036 : Nat := 378893723534687127756493

theorem tailTrace_6641036 : CollatzResearch.WordTrace tailWord_6641036 prefixEnd_6641036 378893723534687127756493 := by
  unfold tailWord_6641036
  simp only [CollatzResearch.WordTrace]
  refine ⟨121109240984334122747871481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161478987979112163663828641 121109240984334122747871481)
  ·
    refine ⟨90831930738250592060903611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121109240984334122747871481 90831930738250592060903611)
    ·
      refine ⟨136247896107375888091355417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90831930738250592060903611 136247896107375888091355417)
      ·
        refine ⟨102185922080531916068516563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136247896107375888091355417 102185922080531916068516563)
        ·
          refine ⟨153278883120797874102774845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102185922080531916068516563 153278883120797874102774845)
          ·
            refine ⟨57479581170299202788540567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153278883120797874102774845 57479581170299202788540567)
            ·
              refine ⟨86219371755448804182810851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57479581170299202788540567 86219371755448804182810851)
              ·
                refine ⟨129329057633173206274216277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86219371755448804182810851 129329057633173206274216277)
                ·
                  refine ⟨378893723534687127756493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129329057633173206274216277 378893723534687127756493)
                  ·
                    rfl

theorem cell23_6641036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_6641036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641036 prefixEnd_6641036 := by exact prefixLift 6641036
  have htrace : WordTrace (prefixWord ++ tailWord_6641036) baseStart_6641036 baseEnd_6641036 := by
    simpa [prefixWord, tailWord_6641036, baseEnd_6641036] using wordTrace_append hprefix tailTrace_6641036
  have hstable : (prefixWord ++ tailWord_6641036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641036).length < 2 ^ (prefixWord ++ tailWord_6641036).sum := by decide
  have hdescent : baseEnd_6641036 < baseStart_6641036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641050 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6641050 : Nat := 118140960795 + 6641050 * 2 ^ 59
def prefixEnd_6641050 : Nat := 4983230072969 + 3 ^ 40 * 6641050 * 2
def baseEnd_6641050 : Nat := 3410050700541347095033373

theorem tailTrace_6641050 : CollatzResearch.WordTrace tailWord_6641050 prefixEnd_6641050 3410050700541347095033373 := by
  unfold tailWord_6641050
  simp only [CollatzResearch.WordTrace]
  refine ⟨60554748147654381471688151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161479328393745017257835069 60554748147654381471688151)
  ·
    refine ⟨90832122221481572207532227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60554748147654381471688151 90832122221481572207532227)
    ·
      refine ⟨136248183332222358311298341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90832122221481572207532227 136248183332222358311298341)
      ·
        refine ⟨25546534374791692183368439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136248183332222358311298341 25546534374791692183368439)
        ·
          refine ⟨38319801562187538275052659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25546534374791692183368439 38319801562187538275052659)
          ·
            refine ⟨57479702343281307412578989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38319801562187538275052659 57479702343281307412578989)
            ·
              refine ⟨21554888378730490279717121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57479702343281307412578989 21554888378730490279717121)
              ·
                refine ⟨16166166284047867709787841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21554888378730490279717121 16166166284047867709787841)
                ·
                  refine ⟨12124624713035900782340881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166166284047867709787841 12124624713035900782340881)
                  ·
                    refine ⟨9093468534776925586755661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12124624713035900782340881 9093468534776925586755661)
                    ·
                      refine ⟨3410050700541347095033373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093468534776925586755661 3410050700541347095033373)
                      ·
                        rfl

theorem cell23_6641050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6641050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641050 prefixEnd_6641050 := by exact prefixLift 6641050
  have htrace : WordTrace (prefixWord ++ tailWord_6641050) baseStart_6641050 baseEnd_6641050 := by
    simpa [prefixWord, tailWord_6641050, baseEnd_6641050] using wordTrace_append hprefix tailTrace_6641050
  have hstable : (prefixWord ++ tailWord_6641050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641050).length < 2 ^ (prefixWord ++ tailWord_6641050).sum := by decide
  have hdescent : baseEnd_6641050 < baseStart_6641050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641053 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 8]
def baseStart_6641053 : Nat := 118140960795 + 6641053 * 2 ^ 59
def prefixEnd_6641053 : Nat := 4983230072969 + 3 ^ 40 * 6641053 * 2
def baseEnd_6641053 : Nat := 378894693442590064810651

theorem tailTrace_6641053 : CollatzResearch.WordTrace tailWord_6641053 prefixEnd_6641053 378894693442590064810651 := by
  unfold tailWord_6641053
  simp only [CollatzResearch.WordTrace]
  refine ⟨242219102009606657399111813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161479401339737771599407875 242219102009606657399111813)
  ·
    refine ⟨45416081626801248262333465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242219102009606657399111813 45416081626801248262333465)
    ·
      refine ⟨34062061220100936196750099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45416081626801248262333465 34062061220100936196750099)
      ·
        refine ⟨51093091830151404295125149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34062061220100936196750099 51093091830151404295125149)
        ·
          refine ⟨19159909436306776610671931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51093091830151404295125149 19159909436306776610671931)
          ·
            refine ⟨28739864154460164916007897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19159909436306776610671931 28739864154460164916007897)
            ·
              refine ⟨21554898115845123687005923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28739864154460164916007897 21554898115845123687005923)
              ·
                refine ⟨32332347173767685530508885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21554898115845123687005923 32332347173767685530508885)
                ·
                  refine ⟨378894693442590064810651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32332347173767685530508885 378894693442590064810651)
                  ·
                    rfl

theorem cell23_6641053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_6641053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641053 prefixEnd_6641053 := by exact prefixLift 6641053
  have htrace : WordTrace (prefixWord ++ tailWord_6641053) baseStart_6641053 baseEnd_6641053 := by
    simpa [prefixWord, tailWord_6641053, baseEnd_6641053] using wordTrace_append hprefix tailTrace_6641053
  have hstable : (prefixWord ++ tailWord_6641053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641053).length < 2 ^ (prefixWord ++ tailWord_6641053).sum := by decide
  have hdescent : baseEnd_6641053 < baseStart_6641053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641080 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_6641080 : Nat := 118140960795 + 6641080 * 2 ^ 59
def prefixEnd_6641080 : Nat := 4983230072969 + 3 ^ 40 * 6641080 * 2
def baseEnd_6641080 : Nat := 3410066104960981977658235

theorem tailTrace_6641080 : CollatzResearch.WordTrace tailWord_6641080 prefixEnd_6641080 3410066104960981977658235 := by
  unfold tailWord_6641080
  simp only [CollatzResearch.WordTrace]
  refine ⟨121110043390254420505172347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161480057853672560673563129 121110043390254420505172347)
  ·
    refine ⟨181665065085381630757758521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121110043390254420505172347 181665065085381630757758521)
    ·
      refine ⟨136248798814036223068318891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181665065085381630757758521 136248798814036223068318891)
      ·
        refine ⟨204373198221054334602478337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136248798814036223068318891 204373198221054334602478337)
        ·
          refine ⟨153279898665790750951858753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204373198221054334602478337 153279898665790750951858753)
          ·
            refine ⟨114959923999343063213894065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153279898665790750951858753 114959923999343063213894065)
            ·
              refine ⟨86219942999507297410420549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114959923999343063213894065 86219942999507297410420549)
              ·
                refine ⟨16166239312407618264453853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86219942999507297410420549 16166239312407618264453853)
                ·
                  refine ⟨6062339742152856849170195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16166239312407618264453853 6062339742152856849170195)
                  ·
                    refine ⟨9093509613229285273755293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062339742152856849170195 9093509613229285273755293)
                    ·
                      refine ⟨3410066104960981977658235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093509613229285273755293 3410066104960981977658235)
                      ·
                        rfl

theorem cell23_6641080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_6641080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641080 prefixEnd_6641080 := by exact prefixLift 6641080
  have htrace : WordTrace (prefixWord ++ tailWord_6641080) baseStart_6641080 baseEnd_6641080 := by
    simpa [prefixWord, tailWord_6641080, baseEnd_6641080] using wordTrace_append hprefix tailTrace_6641080
  have hstable : (prefixWord ++ tailWord_6641080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641080).length < 2 ^ (prefixWord ++ tailWord_6641080).sum := by decide
  have hdescent : baseEnd_6641080 < baseStart_6641080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641097 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 1, 1, 3]
def baseStart_6641097 : Nat := 118140960795 + 6641097 * 2 ^ 59
def prefixEnd_6641097 : Nat := 4983230072969 + 3 ^ 40 * 6641097 * 2
def baseEnd_6641097 : Nat := 3410074834132108411145657

theorem tailTrace_6641097 : CollatzResearch.WordTrace tailWord_6641097 prefixEnd_6641097 3410074834132108411145657 := by
  unfold tailWord_6641097
  simp only [CollatzResearch.WordTrace]
  refine ⟨242220706821447252913713545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161480471214298168609142363 242220706821447252913713545)
  ·
    refine ⟨181665530116085439685285159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242220706821447252913713545 181665530116085439685285159)
    ·
      refine ⟨272498295174128159527927739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181665530116085439685285159 272498295174128159527927739)
      ·
        refine ⟨408747442761192239291891609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272498295174128159527927739 408747442761192239291891609)
        ·
          refine ⟨306560582070894179468918707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408747442761192239291891609 306560582070894179468918707)
          ·
            refine ⟨459840873106341269203378061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306560582070894179468918707 459840873106341269203378061)
            ·
              refine ⟨172440327414877975951266773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459840873106341269203378061 172440327414877975951266773)
              ·
                refine ⟨4041570173786202561357815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172440327414877975951266773 4041570173786202561357815)
                ·
                  refine ⟨6062355260679303842036723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041570173786202561357815 6062355260679303842036723)
                  ·
                    refine ⟨9093532891018955763055085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062355260679303842036723 9093532891018955763055085)
                    ·
                      refine ⟨3410074834132108411145657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093532891018955763055085 3410074834132108411145657)
                      ·
                        rfl

theorem cell23_6641097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 1, 3].length) (baseStart_6641097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641097 prefixEnd_6641097 := by exact prefixLift 6641097
  have htrace : WordTrace (prefixWord ++ tailWord_6641097) baseStart_6641097 baseEnd_6641097 := by
    simpa [prefixWord, tailWord_6641097, baseEnd_6641097] using wordTrace_append hprefix tailTrace_6641097
  have hstable : (prefixWord ++ tailWord_6641097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641097).length < 2 ^ (prefixWord ++ tailWord_6641097).sum := by decide
  have hdescent : baseEnd_6641097 < baseStart_6641097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641108 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_6641108 : Nat := 118140960795 + 6641108 * 2 ^ 59
def prefixEnd_6641108 : Nat := 4983230072969 + 3 ^ 40 * 6641108 * 2
def baseEnd_6641108 : Nat := 1136693494139769289369369

theorem tailTrace_6641108 : CollatzResearch.WordTrace tailWord_6641108 prefixEnd_6641108 1136693494139769289369369 := by
  unfold tailWord_6641108
  simp only [CollatzResearch.WordTrace]
  refine ⟨121110554012203700896181989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161480738682938267861575985 121110554012203700896181989)
  ·
    refine ⟨22708228877288193918034123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121110554012203700896181989 22708228877288193918034123)
    ·
      refine ⟨34062343315932290877051185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22708228877288193918034123 34062343315932290877051185)
      ·
        refine ⟨25546757486949218157788389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34062343315932290877051185 25546757486949218157788389)
        ·
          refine ⟨4790017028802978404585323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25546757486949218157788389 4790017028802978404585323)
          ·
            refine ⟨7185025543204467606877985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790017028802978404585323 7185025543204467606877985)
            ·
              refine ⟨5388769157403350705158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185025543204467606877985 5388769157403350705158489)
              ·
                refine ⟨4041576868052513028868867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388769157403350705158489 4041576868052513028868867)
                ·
                  refine ⟨6062365302078769543303301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041576868052513028868867 6062365302078769543303301)
                  ·
                    refine ⟨1136693494139769289369369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6062365302078769543303301 1136693494139769289369369)
                    ·
                      rfl

theorem cell23_6641108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_6641108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641108 prefixEnd_6641108 := by exact prefixLift 6641108
  have htrace : WordTrace (prefixWord ++ tailWord_6641108) baseStart_6641108 baseEnd_6641108 := by
    simpa [prefixWord, tailWord_6641108, baseEnd_6641108] using wordTrace_append hprefix tailTrace_6641108
  have hstable : (prefixWord ++ tailWord_6641108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641108).length < 2 ^ (prefixWord ++ tailWord_6641108).sum := by decide
  have hdescent : baseEnd_6641108 < baseStart_6641108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641114 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3]
def baseStart_6641114 : Nat := 118140960795 + 6641114 * 2 ^ 59
def prefixEnd_6641114 : Nat := 4983230072969 + 3 ^ 40 * 6641114 * 2
def baseEnd_6641114 : Nat := 3410083563303234844633079

theorem tailTrace_6641114 : CollatzResearch.WordTrace tailWord_6641114 prefixEnd_6641114 3410083563303234844633079 := by
  unfold tailWord_6641114
  simp only [CollatzResearch.WordTrace]
  refine ⟨60555331715596416204270599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161480884574923776544721597 60555331715596416204270599)
  ·
    refine ⟨90832997573394624306405899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60555331715596416204270599 90832997573394624306405899)
    ·
      refine ⟨136249496360091936459608849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90832997573394624306405899 136249496360091936459608849)
      ·
        refine ⟨102187122270068952344706637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136249496360091936459608849 102187122270068952344706637)
        ·
          refine ⟨38320170851275857129264989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102187122270068952344706637 38320170851275857129264989)
          ·
            refine ⟨14370064069228446423474371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38320170851275857129264989 14370064069228446423474371)
            ·
              refine ⟨21555096103842669635211557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14370064069228446423474371 21555096103842669635211557)
              ·
                refine ⟨4041580519470500556602167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21555096103842669635211557 4041580519470500556602167)
                ·
                  refine ⟨6062370779205750834903251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041580519470500556602167 6062370779205750834903251)
                  ·
                    refine ⟨9093556168808626252354877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062370779205750834903251 9093556168808626252354877)
                    ·
                      refine ⟨3410083563303234844633079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093556168808626252354877 3410083563303234844633079)
                      ·
                        rfl

theorem cell23_6641114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_6641114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641114 prefixEnd_6641114 := by exact prefixLift 6641114
  have htrace : WordTrace (prefixWord ++ tailWord_6641114) baseStart_6641114 baseEnd_6641114 := by
    simpa [prefixWord, tailWord_6641114, baseEnd_6641114] using wordTrace_append hprefix tailTrace_6641114
  have hstable : (prefixWord ++ tailWord_6641114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641114).length < 2 ^ (prefixWord ++ tailWord_6641114).sum := by decide
  have hdescent : baseEnd_6641114 < baseStart_6641114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641137 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_6641137 : Nat := 118140960795 + 6641137 * 2 ^ 59
def prefixEnd_6641137 : Nat := 4983230072969 + 3 ^ 40 * 6641137 * 2
def baseEnd_6641137 : Nat := 3410095373358288254645473

theorem tailTrace_6641137 : CollatzResearch.WordTrace tailWord_6641137 prefixEnd_6641137 3410095373358288254645473 := by
  unfold tailWord_6641137
  simp only [CollatzResearch.WordTrace]
  refine ⟨242222165741302339745169665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161481443827534893163446443 242222165741302339745169665)
  ·
    refine ⟨181666624305976754808877249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242222165741302339745169665 181666624305976754808877249)
    ·
      refine ⟨136249968229482566106657937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181666624305976754808877249 136249968229482566106657937)
      ·
        refine ⟨102187476172111924579993453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136249968229482566106657937 102187476172111924579993453)
        ·
          refine ⟨38320303564541971717497545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102187476172111924579993453 38320303564541971717497545)
          ·
            refine ⟨28740227673406478788123159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38320303564541971717497545 28740227673406478788123159)
            ·
              refine ⟨43110341510109718182184739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28740227673406478788123159 43110341510109718182184739)
              ·
                refine ⟨64665512265164577273277109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43110341510109718182184739 64665512265164577273277109)
                ·
                  refine ⟨6062391774859179119369729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64665512265164577273277109 6062391774859179119369729)
                  ·
                    refine ⟨4546793831144384339527297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6062391774859179119369729 4546793831144384339527297)
                    ·
                      refine ⟨3410095373358288254645473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546793831144384339527297 3410095373358288254645473)
                      ·
                        rfl

theorem cell23_6641137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_6641137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641137 prefixEnd_6641137 := by exact prefixLift 6641137
  have htrace : WordTrace (prefixWord ++ tailWord_6641137) baseStart_6641137 baseEnd_6641137 := by
    simpa [prefixWord, tailWord_6641137, baseEnd_6641137] using wordTrace_append hprefix tailTrace_6641137
  have hstable : (prefixWord ++ tailWord_6641137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641137).length < 2 ^ (prefixWord ++ tailWord_6641137).sum := by decide
  have hdescent : baseEnd_6641137 < baseStart_6641137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641141 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6641141 : Nat := 118140960795 + 6641141 * 2 ^ 59
def prefixEnd_6641141 : Nat := 4983230072969 + 3 ^ 40 * 6641141 * 2
def baseEnd_6641141 : Nat := 3410097427280906238995455

theorem tailTrace_6641141 : CollatzResearch.WordTrace tailWord_6641141 prefixEnd_6641141 3410097427280906238995455 := by
  unfold tailWord_6641141
  simp only [CollatzResearch.WordTrace]
  refine ⟨242222311633287848428315277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161481541088858565618876851 242222311633287848428315277)
  ·
    refine ⟨90833366862482943160618229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242222311633287848428315277 90833366862482943160618229)
    ·
      refine ⟨8515628143357775921307959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90833366862482943160618229 8515628143357775921307959)
      ·
        refine ⟨12773442215036663881961939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8515628143357775921307959 12773442215036663881961939)
        ·
          refine ⟨19160163322554995822942909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12773442215036663881961939 19160163322554995822942909)
          ·
            refine ⟨7185061245958123433603591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19160163322554995822942909 7185061245958123433603591)
            ·
              refine ⟨10777591868937185150405387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185061245958123433603591 10777591868937185150405387)
              ·
                refine ⟨16166387803405777725608081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10777591868937185150405387 16166387803405777725608081)
                ·
                  refine ⟨12124790852554333294206061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166387803405777725608081 12124790852554333294206061)
                  ·
                    refine ⟨4546796569707874985327273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12124790852554333294206061 4546796569707874985327273)
                    ·
                      refine ⟨3410097427280906238995455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546796569707874985327273 3410097427280906238995455)
                      ·
                        rfl

theorem cell23_6641141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6641141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641141 prefixEnd_6641141 := by exact prefixLift 6641141
  have htrace : WordTrace (prefixWord ++ tailWord_6641141) baseStart_6641141 baseEnd_6641141 := by
    simpa [prefixWord, tailWord_6641141, baseEnd_6641141] using wordTrace_append hprefix tailTrace_6641141
  have hstable : (prefixWord ++ tailWord_6641141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641141).length < 2 ^ (prefixWord ++ tailWord_6641141).sum := by decide
  have hdescent : baseEnd_6641141 < baseStart_6641141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641154 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6641154 : Nat := 118140960795 + 6641154 * 2 ^ 59
def prefixEnd_6641154 : Nat := 4983230072969 + 3 ^ 40 * 6641154 * 2
def baseEnd_6641154 : Nat := 3410104102529414688132895

theorem tailTrace_6641154 : CollatzResearch.WordTrace tailWord_6641154 prefixEnd_6641154 3410104102529414688132895 := by
  unfold tailWord_6641154
  simp only [CollatzResearch.WordTrace]
  refine ⟨60555696445560187912134629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161481857188160501099025677 60555696445560187912134629)
  ·
    refine ⟨11354193083542535233525243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60555696445560187912134629 11354193083542535233525243)
    ·
      refine ⟨17031289625313802850287865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354193083542535233525243 17031289625313802850287865)
      ·
        refine ⟨12773467218985352137715899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17031289625313802850287865 12773467218985352137715899)
        ·
          refine ⟨19160200828478028206573849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12773467218985352137715899 19160200828478028206573849)
          ·
            refine ⟨14370150621358521154930387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19160200828478028206573849 14370150621358521154930387)
            ·
              refine ⟨21555225932037781732395581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14370150621358521154930387 21555225932037781732395581)
              ·
                refine ⟨8083209724514168149648343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21555225932037781732395581 8083209724514168149648343)
                ·
                  refine ⟨12124814586771252224472515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083209724514168149648343 12124814586771252224472515)
                  ·
                    refine ⟨18187221880156878336708773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12124814586771252224472515 18187221880156878336708773)
                    ·
                      refine ⟨3410104102529414688132895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18187221880156878336708773 3410104102529414688132895)
                      ·
                        rfl

theorem cell23_6641154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6641154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641154 prefixEnd_6641154 := by exact prefixLift 6641154
  have htrace : WordTrace (prefixWord ++ tailWord_6641154) baseStart_6641154 baseEnd_6641154 := by
    simpa [prefixWord, tailWord_6641154, baseEnd_6641154] using wordTrace_append hprefix tailTrace_6641154
  have hstable : (prefixWord ++ tailWord_6641154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641154).length < 2 ^ (prefixWord ++ tailWord_6641154).sum := by decide
  have hdescent : baseEnd_6641154 < baseStart_6641154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641164 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_6641164 : Nat := 118140960795 + 6641164 * 2 ^ 59
def prefixEnd_6641164 : Nat := 4983230072969 + 3 ^ 40 * 6641164 * 2
def baseEnd_6641164 : Nat := 1136703079111986549669283

theorem tailTrace_6641164 : CollatzResearch.WordTrace tailWord_6641164 prefixEnd_6641164 1136703079111986549669283 := by
  unfold tailWord_6641164
  simp only [CollatzResearch.WordTrace]
  refine ⟨121111575256102261678201273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161482100341469682237601697 121111575256102261678201273)
  ·
    refine ⟨90833681442076696258650955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121111575256102261678201273 90833681442076696258650955)
    ·
      refine ⟨136250522163115044387976433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90833681442076696258650955 136250522163115044387976433)
      ·
        refine ⟨102187891622336283290982325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136250522163115044387976433 102187891622336283290982325)
        ·
          refine ⟨9580114839594026558529593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102187891622336283290982325 9580114839594026558529593)
          ·
            refine ⟨7185086129695519918897195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580114839594026558529593 7185086129695519918897195)
            ·
              refine ⟨10777629194543279878345793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185086129695519918897195 10777629194543279878345793)
              ·
                refine ⟨8083221895907459908759345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10777629194543279878345793 8083221895907459908759345)
                ·
                  refine ⟨6062416421930594931569509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8083221895907459908759345 6062416421930594931569509)
                  ·
                    refine ⟨1136703079111986549669283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6062416421930594931569509 1136703079111986549669283)
                    ·
                      rfl

theorem cell23_6641164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_6641164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641164 prefixEnd_6641164 := by exact prefixLift 6641164
  have htrace : WordTrace (prefixWord ++ tailWord_6641164) baseStart_6641164 baseEnd_6641164 := by
    simpa [prefixWord, tailWord_6641164, baseEnd_6641164] using wordTrace_append hprefix tailTrace_6641164
  have hstable : (prefixWord ++ tailWord_6641164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641164).length < 2 ^ (prefixWord ++ tailWord_6641164).sum := by decide
  have hdescent : baseEnd_6641164 < baseStart_6641164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641222 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6641222 : Nat := 118140960795 + 6641222 * 2 ^ 59
def prefixEnd_6641222 : Nat := 4983230072969 + 3 ^ 40 * 6641222 * 2
def baseEnd_6641222 : Nat := 3410139019213920422082583

theorem tailTrace_6641222 : CollatzResearch.WordTrace tailWord_6641222 prefixEnd_6641222 3410139019213920422082583 := by
  unfold tailWord_6641222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569539560812324976937935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161483510630662932841342613 7569539560812324976937935)
  ·
    refine ⟨11354309341218487465406903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569539560812324976937935 11354309341218487465406903)
    ·
      refine ⟨17031464011827731198110355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354309341218487465406903 17031464011827731198110355)
      ·
        refine ⟨25547196017741596797165533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17031464011827731198110355 25547196017741596797165533)
        ·
          refine ⟨9580198506653098798937075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25547196017741596797165533 9580198506653098798937075)
          ·
            refine ⟨14370297759979648198405613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580198506653098798937075 14370297759979648198405613)
            ·
              refine ⟨5388861659992368074402105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14370297759979648198405613 5388861659992368074402105)
              ·
                refine ⟨4041646244994276055801579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388861659992368074402105 4041646244994276055801579)
                ·
                  refine ⟨6062469367491414083702369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041646244994276055801579 6062469367491414083702369)
                  ·
                    refine ⟨4546852025618560562776777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6062469367491414083702369 4546852025618560562776777)
                    ·
                      refine ⟨3410139019213920422082583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546852025618560562776777 3410139019213920422082583)
                      ·
                        rfl

theorem cell23_6641222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6641222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641222 prefixEnd_6641222 := by exact prefixLift 6641222
  have htrace : WordTrace (prefixWord ++ tailWord_6641222) baseStart_6641222 baseEnd_6641222 := by
    simpa [prefixWord, tailWord_6641222, baseEnd_6641222] using wordTrace_append hprefix tailTrace_6641222
  have hstable : (prefixWord ++ tailWord_6641222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641222).length < 2 ^ (prefixWord ++ tailWord_6641222).sum := by decide
  have hdescent : baseEnd_6641222 < baseStart_6641222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641230 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_6641230 : Nat := 118140960795 + 6641230 * 2 ^ 59
def prefixEnd_6641230 : Nat := 4983230072969 + 3 ^ 40 * 6641230 * 2
def baseEnd_6641230 : Nat := 3410143127059156390782545

theorem tailTrace_6641230 : CollatzResearch.WordTrace tailWord_6641230 prefixEnd_6641230 3410143127059156390782545 := by
  unfold tailWord_6641230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30278194716245677078538143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161483705153310277752203429 30278194716245677078538143)
  ·
    refine ⟨45417292074368515617807215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30278194716245677078538143 45417292074368515617807215)
    ·
      refine ⟨68125938111552773426710823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45417292074368515617807215 68125938111552773426710823)
      ·
        refine ⟨102188907167329160140066235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68125938111552773426710823 102188907167329160140066235)
        ·
          refine ⟨153283360750993740210099353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102188907167329160140066235 153283360750993740210099353)
          ·
            refine ⟨114962520563245305157574515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153283360750993740210099353 114962520563245305157574515)
            ·
              refine ⟨172443780844867957736361773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114962520563245305157574515 172443780844867957736361773)
              ·
                refine ⟨64666417816825484151135665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172443780844867957736361773 64666417816825484151135665)
                ·
                  refine ⟨48499813362619113113351749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64666417816825484151135665 48499813362619113113351749)
                  ·
                    refine ⟨9093715005491083708753453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48499813362619113113351749 9093715005491083708753453)
                    ·
                      refine ⟨3410143127059156390782545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093715005491083708753453 3410143127059156390782545)
                      ·
                        rfl

theorem cell23_6641230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_6641230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641230 prefixEnd_6641230 := by exact prefixLift 6641230
  have htrace : WordTrace (prefixWord ++ tailWord_6641230) baseStart_6641230 baseEnd_6641230 := by
    simpa [prefixWord, tailWord_6641230, baseEnd_6641230] using wordTrace_append hprefix tailTrace_6641230
  have hstable : (prefixWord ++ tailWord_6641230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641230).length < 2 ^ (prefixWord ++ tailWord_6641230).sum := by decide
  have hdescent : baseEnd_6641230 < baseStart_6641230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641260 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_6641260 : Nat := 118140960795 + 6641260 * 2 ^ 59
def prefixEnd_6641260 : Nat := 4983230072969 + 3 ^ 40 * 6641260 * 2
def baseEnd_6641260 : Nat := 3410158531478791273407407

theorem tailTrace_6641260 : CollatzResearch.WordTrace tailWord_6641260 prefixEnd_6641260 3410158531478791273407407 := by
  unfold tailWord_6641260
  simp only [CollatzResearch.WordTrace]
  refine ⟨121113325959928365875948617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161484434613237821167931489 121113325959928365875948617)
  ·
    refine ⟨90834994469946274406961463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121113325959928365875948617 90834994469946274406961463)
    ·
      refine ⟨136252491704919411610442195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90834994469946274406961463 136252491704919411610442195)
      ·
        refine ⟨204378737557379117415663293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136252491704919411610442195 204378737557379117415663293)
        ·
          refine ⟨76642026584017169030873735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204378737557379117415663293 76642026584017169030873735)
          ·
            refine ⟨114963039876025753546310603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76642026584017169030873735 114963039876025753546310603)
            ·
              refine ⟨172444559814038630319465905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114963039876025753546310603 172444559814038630319465905)
              ·
                refine ⟨129333419860528972739599429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172444559814038630319465905 129333419860528972739599429)
                ·
                  refine ⟨24250016223849182388674893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129333419860528972739599429 24250016223849182388674893)
                  ·
                    refine ⟨9093756083943443395753085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24250016223849182388674893 9093756083943443395753085)
                    ·
                      refine ⟨3410158531478791273407407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093756083943443395753085 3410158531478791273407407)
                      ·
                        rfl

theorem cell23_6641260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_6641260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641260 prefixEnd_6641260 := by exact prefixLift 6641260
  have htrace : WordTrace (prefixWord ++ tailWord_6641260) baseStart_6641260 baseEnd_6641260 := by
    simpa [prefixWord, tailWord_6641260, baseEnd_6641260] using wordTrace_append hprefix tailTrace_6641260
  have hstable : (prefixWord ++ tailWord_6641260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641260).length < 2 ^ (prefixWord ++ tailWord_6641260).sum := by decide
  have hdescent : baseEnd_6641260 < baseStart_6641260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641280 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_6641280 : Nat := 118140960795 + 6641280 * 2 ^ 59
def prefixEnd_6641280 : Nat := 4983230072969 + 3 ^ 40 * 6641280 * 2
def baseEnd_6641280 : Nat := 1136722933697293731719105

theorem tailTrace_6641280 : CollatzResearch.WordTrace tailWord_6641280 prefixEnd_6641280 1136722933697293731719105 := by
  unfold tailWord_6641280
  simp only [CollatzResearch.WordTrace]
  refine ⟨121113690689892137583812647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161484920919856183445083529 121113690689892137583812647)
  ·
    refine ⟨181670536034838206375718971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121113690689892137583812647 181670536034838206375718971)
    ·
      refine ⟨272505804052257309563578457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181670536034838206375718971 272505804052257309563578457)
      ·
        refine ⟨204379353039192982172683843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272505804052257309563578457 204379353039192982172683843)
        ·
          refine ⟨306569029558789473259025765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204379353039192982172683843 306569029558789473259025765)
          ·
            refine ⟨57481693042273026236067331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306569029558789473259025765 57481693042273026236067331)
            ·
              refine ⟨86222539563409539354100997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57481693042273026236067331 86222539563409539354100997)
              ·
                refine ⟨16166726168139288628893937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86222539563409539354100997 16166726168139288628893937)
                ·
                  refine ⟨12125044626104466471670453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166726168139288628893937 12125044626104466471670453)
                  ·
                    refine ⟨1136722933697293731719105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12125044626104466471670453 1136722933697293731719105)
                    ·
                      rfl

theorem cell23_6641280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_6641280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641280 prefixEnd_6641280 := by exact prefixLift 6641280
  have htrace : WordTrace (prefixWord ++ tailWord_6641280) baseStart_6641280 baseEnd_6641280 := by
    simpa [prefixWord, tailWord_6641280, baseEnd_6641280] using wordTrace_append hprefix tailTrace_6641280
  have hstable : (prefixWord ++ tailWord_6641280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641280).length < 2 ^ (prefixWord ++ tailWord_6641280).sum := by decide
  have hdescent : baseEnd_6641280 < baseStart_6641280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641284 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 5]
def baseStart_6641284 : Nat := 118140960795 + 6641284 * 2 ^ 59
def prefixEnd_6641284 : Nat := 4983230072969 + 3 ^ 40 * 6641284 * 2
def baseEnd_6641284 : Nat := 378907872779388797723033

theorem tailTrace_6641284 : CollatzResearch.WordTrace tailWord_6641284 prefixEnd_6641284 378907872779388797723033 := by
  unfold tailWord_6641284
  simp only [CollatzResearch.WordTrace]
  refine ⟨121113763635884891925385453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161485018181179855900513937 121113763635884891925385453)
  ·
    refine ⟨45417661363456834472019545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121113763635884891925385453 45417661363456834472019545)
    ·
      refine ⟨34063246022592625854014659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45417661363456834472019545 34063246022592625854014659)
      ·
        refine ⟨51094869033888938781021989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34063246022592625854014659 51094869033888938781021989)
        ·
          refine ⟨9580287943854176021441623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51094869033888938781021989 9580287943854176021441623)
          ·
            refine ⟨14370431915781264032162435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580287943854176021441623 14370431915781264032162435)
            ·
              refine ⟨21555647873671896048243653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14370431915781264032162435 21555647873671896048243653)
              ·
                refine ⟨4041683976313480509045685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21555647873671896048243653 4041683976313480509045685)
                ·
                  refine ⟨378907872779388797723033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041683976313480509045685 378907872779388797723033)
                  ·
                    rfl

theorem cell23_6641284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_6641284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641284 prefixEnd_6641284 := by exact prefixLift 6641284
  have htrace : WordTrace (prefixWord ++ tailWord_6641284) baseStart_6641284 baseEnd_6641284 := by
    simpa [prefixWord, tailWord_6641284, baseEnd_6641284] using wordTrace_append hprefix tailTrace_6641284
  have hstable : (prefixWord ++ tailWord_6641284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641284).length < 2 ^ (prefixWord ++ tailWord_6641284).sum := by decide
  have hdescent : baseEnd_6641284 < baseStart_6641284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641287 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_6641287 : Nat := 118140960795 + 6641287 * 2 ^ 59
def prefixEnd_6641287 : Nat := 4983230072969 + 3 ^ 40 * 6641287 * 2
def baseEnd_6641287 : Nat := 3410172395456462667769783

theorem tailTrace_6641287 : CollatzResearch.WordTrace tailWord_6641287 prefixEnd_6641287 3410172395456462667769783 := by
  unfold tailWord_6641287
  simp only [CollatzResearch.WordTrace]
  refine ⟨242227636690758915363130115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161485091127172610242086743 242227636690758915363130115)
  ·
    refine ⟨363341455036138373044695173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242227636690758915363130115 363341455036138373044695173)
    ·
      refine ⟨68126522819275944945880345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363341455036138373044695173 68126522819275944945880345)
      ·
        refine ⟨51094892114456958709410259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68126522819275944945880345 51094892114456958709410259)
        ·
          refine ⟨76642338171685438064115389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51094892114456958709410259 76642338171685438064115389)
          ·
            refine ⟨28740876814382039274043271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76642338171685438064115389 28740876814382039274043271)
            ·
              refine ⟨43111315221573058911064907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28740876814382039274043271 43111315221573058911064907)
              ·
                refine ⟨64666972832359588366597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43111315221573058911064907 64666972832359588366597361)
                ·
                  refine ⟨48500229624269691274948021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64666972832359588366597361 48500229624269691274948021)
                  ·
                    refine ⟨4546896527275283557026377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48500229624269691274948021 4546896527275283557026377)
                    ·
                      refine ⟨3410172395456462667769783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4546896527275283557026377 3410172395456462667769783)
                      ·
                        rfl

theorem cell23_6641287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_6641287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641287 prefixEnd_6641287 := by exact prefixLift 6641287
  have htrace : WordTrace (prefixWord ++ tailWord_6641287) baseStart_6641287 baseEnd_6641287 := by
    simpa [prefixWord, tailWord_6641287, baseEnd_6641287] using wordTrace_append hprefix tailTrace_6641287
  have hstable : (prefixWord ++ tailWord_6641287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641287).length < 2 ^ (prefixWord ++ tailWord_6641287).sum := by decide
  have hdescent : baseEnd_6641287 < baseStart_6641287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641314 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_6641314 : Nat := 118140960795 + 6641314 * 2 ^ 59
def prefixEnd_6641314 : Nat := 4983230072969 + 3 ^ 40 * 6641314 * 2
def baseEnd_6641314 : Nat := 1136728753144711354044053

theorem tailTrace_6641314 : CollatzResearch.WordTrace tailWord_6641314 prefixEnd_6641314 1136728753144711354044053 := by
  unfold tailWord_6641314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60557155365415274743590749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161485747641107399316241997 60557155365415274743590749)
  ·
    refine ⟨22708933262030728028846531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60557155365415274743590749 22708933262030728028846531)
    ·
      refine ⟨34063399893046092043269797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22708933262030728028846531 34063399893046092043269797)
      ·
        refine ⟨6386887479946142258113087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34063399893046092043269797 6386887479946142258113087)
        ·
          refine ⟨9580331219919213387169631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386887479946142258113087 9580331219919213387169631)
          ·
            refine ⟨14370496829878820080754447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580331219919213387169631 14370496829878820080754447)
            ·
              refine ⟨21555745244818230121131671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14370496829878820080754447 21555745244818230121131671)
              ·
                refine ⟨32333617867227345181697507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21555745244818230121131671 32333617867227345181697507)
                ·
                  refine ⟨48500426800841017772546261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32333617867227345181697507 48500426800841017772546261)
                  ·
                    refine ⟨1136728753144711354044053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48500426800841017772546261 1136728753144711354044053)
                    ·
                      rfl

theorem cell23_6641314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_6641314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641314 prefixEnd_6641314 := by exact prefixLift 6641314
  have htrace : WordTrace (prefixWord ++ tailWord_6641314) baseStart_6641314 baseEnd_6641314 := by
    simpa [prefixWord, tailWord_6641314, baseEnd_6641314] using wordTrace_append hprefix tailTrace_6641314
  have hstable : (prefixWord ++ tailWord_6641314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641314).length < 2 ^ (prefixWord ++ tailWord_6641314).sum := by decide
  have hdescent : baseEnd_6641314 < baseStart_6641314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641317 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_6641317 : Nat := 118140960795 + 6641317 * 2 ^ 59
def prefixEnd_6641317 : Nat := 4983230072969 + 3 ^ 40 * 6641317 * 2
def baseEnd_6641317 : Nat := 3410187799876097550394645

theorem tailTrace_6641317 : CollatzResearch.WordTrace tailWord_6641317 prefixEnd_6641317 3410187799876097550394645 := by
  unfold tailWord_6641317
  simp only [CollatzResearch.WordTrace]
  refine ⟨242228730880650230486722205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161485820587100153657814803 242228730880650230486722205)
  ·
    refine ⟨90835774080243836432520827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242228730880650230486722205 90835774080243836432520827)
    ·
      refine ⟨136253661120365754648781241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90835774080243836432520827 136253661120365754648781241)
      ·
        refine ⟨102190245840274315986585931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136253661120365754648781241 102190245840274315986585931)
        ·
          refine ⟨153285368760411473979878897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102190245840274315986585931 153285368760411473979878897)
          ·
            refine ⟨114964026570308605484909173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153285368760411473979878897 114964026570308605484909173)
            ·
              refine ⟨10777877490966431764210235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114964026570308605484909173 10777877490966431764210235)
              ·
                refine ⟨16166816236449647646315353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10777877490966431764210235 16166816236449647646315353)
                ·
                  refine ⟨12125112177337235734736515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166816236449647646315353 12125112177337235734736515)
                  ·
                    refine ⟨18187668266005853602104773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12125112177337235734736515 18187668266005853602104773)
                    ·
                      refine ⟨3410187799876097550394645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18187668266005853602104773 3410187799876097550394645)
                      ·
                        rfl

theorem cell23_6641317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_6641317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641317 prefixEnd_6641317 := by exact prefixLift 6641317
  have htrace : WordTrace (prefixWord ++ tailWord_6641317) baseStart_6641317 baseEnd_6641317 := by
    simpa [prefixWord, tailWord_6641317, baseEnd_6641317] using wordTrace_append hprefix tailTrace_6641317
  have hstable : (prefixWord ++ tailWord_6641317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641317).length < 2 ^ (prefixWord ++ tailWord_6641317).sum := by decide
  have hdescent : baseEnd_6641317 < baseStart_6641317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641330 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6641330 : Nat := 118140960795 + 6641330 * 2 ^ 59
def prefixEnd_6641330 : Nat := 4983230072969 + 3 ^ 40 * 6641330 * 2
def baseEnd_6641330 : Nat := 3410194475124605999532085

theorem tailTrace_6641330 : CollatzResearch.WordTrace tailWord_6641330 prefixEnd_6641330 3410194475124605999532085 := by
  unfold tailWord_6641330
  simp only [CollatzResearch.WordTrace]
  refine ⟨60557301257400783426736361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161486136686402089137963629 60557301257400783426736361)
  ·
    refine ⟨45417975943050587570052271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60557301257400783426736361 45417975943050587570052271)
    ·
      refine ⟨68126963914575881355078407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45417975943050587570052271 68126963914575881355078407)
      ·
        refine ⟨102190445871863822032617611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68126963914575881355078407 102190445871863822032617611)
        ·
          refine ⟨153285668807795733048926417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102190445871863822032617611 153285668807795733048926417)
          ·
            refine ⟨114964251605846799786694813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153285668807795733048926417 114964251605846799786694813)
            ·
              refine ⟨43111594352192549920010555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114964251605846799786694813 43111594352192549920010555)
              ·
                refine ⟨64667391528288824880015833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43111594352192549920010555 64667391528288824880015833)
                ·
                  refine ⟨48500543646216618660011875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64667391528288824880015833 48500543646216618660011875)
                  ·
                    refine ⟨72750815469324927990017813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48500543646216618660011875 72750815469324927990017813)
                    ·
                      refine ⟨3410194475124605999532085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72750815469324927990017813 3410194475124605999532085)
                      ·
                        rfl

theorem cell23_6641330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6641330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641330 prefixEnd_6641330 := by exact prefixLift 6641330
  have htrace : WordTrace (prefixWord ++ tailWord_6641330) baseStart_6641330 baseEnd_6641330 := by
    simpa [prefixWord, tailWord_6641330, baseEnd_6641330] using wordTrace_append hprefix tailTrace_6641330
  have hstable : (prefixWord ++ tailWord_6641330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641330).length < 2 ^ (prefixWord ++ tailWord_6641330).sum := by decide
  have hdescent : baseEnd_6641330 < baseStart_6641330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641337 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6641337 : Nat := 118140960795 + 6641337 * 2 ^ 59
def prefixEnd_6641337 : Nat := 4983230072969 + 3 ^ 40 * 6641337 * 2
def baseEnd_6641337 : Nat := 3410198069489187472144553

theorem tailTrace_6641337 : CollatzResearch.WordTrace tailWord_6641337 prefixEnd_6641337 3410198069489187472144553 := by
  unfold tailWord_6641337
  simp only [CollatzResearch.WordTrace]
  refine ⟨242229460340577773902450265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161486306893718515934966843 242229460340577773902450265)
  ·
    refine ⟨181672095255433330426837699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242229460340577773902450265 181672095255433330426837699)
    ·
      refine ⟨272508142883149995640256549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181672095255433330426837699 272508142883149995640256549)
      ·
        refine ⟨51095276790590624182548103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272508142883149995640256549 51095276790590624182548103)
        ·
          refine ⟨76642915185885936273822155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51095276790590624182548103 76642915185885936273822155)
          ·
            refine ⟨114964372778828904410733233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76642915185885936273822155 114964372778828904410733233)
            ·
              refine ⟨86223279584121678308049925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114964372778828904410733233 86223279584121678308049925)
              ·
                refine ⟨16166864922022814682759361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86223279584121678308049925 16166864922022814682759361)
                ·
                  refine ⟨12125148691517111012069521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166864922022814682759361 12125148691517111012069521)
                  ·
                    refine ⟨9093861518637833259052141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12125148691517111012069521 9093861518637833259052141)
                    ·
                      refine ⟨3410198069489187472144553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9093861518637833259052141 3410198069489187472144553)
                      ·
                        rfl

theorem cell23_6641337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6641337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641337 prefixEnd_6641337 := by exact prefixLift 6641337
  have htrace : WordTrace (prefixWord ++ tailWord_6641337) baseStart_6641337 baseEnd_6641337 := by
    simpa [prefixWord, tailWord_6641337, baseEnd_6641337] using wordTrace_append hprefix tailTrace_6641337
  have hstable : (prefixWord ++ tailWord_6641337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641337).length < 2 ^ (prefixWord ++ tailWord_6641337).sum := by decide
  have hdescent : baseEnd_6641337 < baseStart_6641337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641344 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 1, 4]
def baseStart_6641344 : Nat := 118140960795 + 6641344 * 2 ^ 59
def prefixEnd_6641344 : Nat := 4983230072969 + 3 ^ 40 * 6641344 * 2
def baseEnd_6641344 : Nat := 1136733887951256314919007

theorem tailTrace_6641344 : CollatzResearch.WordTrace tailWord_6641344 prefixEnd_6641344 1136733887951256314919007 := by
  unfold tailWord_6641344
  simp only [CollatzResearch.WordTrace]
  refine ⟨121114857825776207048977543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161486477101034942731970057 121114857825776207048977543)
  ·
    refine ⟨181672286738664310573466315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121114857825776207048977543 181672286738664310573466315)
    ·
      refine ⟨272508430107996465860199473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181672286738664310573466315 272508430107996465860199473)
      ·
        refine ⟨204381322580997349395149605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272508430107996465860199473 204381322580997349395149605)
        ·
          refine ⟨38321497983937003011590551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204381322580997349395149605 38321497983937003011590551)
          ·
            refine ⟨57482246975905504517385827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38321497983937003011590551 57482246975905504517385827)
            ·
              refine ⟨86223370463858256776078741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57482246975905504517385827 86223370463858256776078741)
              ·
                refine ⟨4041720490493355786378691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86223370463858256776078741 4041720490493355786378691)
                ·
                  refine ⟨6062580735740033679568037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041720490493355786378691 6062580735740033679568037)
                  ·
                    refine ⟨1136733887951256314919007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6062580735740033679568037 1136733887951256314919007)
                    ·
                      rfl

theorem cell23_6641344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 4].length) (baseStart_6641344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641344 prefixEnd_6641344 := by exact prefixLift 6641344
  have htrace : WordTrace (prefixWord ++ tailWord_6641344) baseStart_6641344 baseEnd_6641344 := by
    simpa [prefixWord, tailWord_6641344, baseEnd_6641344] using wordTrace_append hprefix tailTrace_6641344
  have hstable : (prefixWord ++ tailWord_6641344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641344).length < 2 ^ (prefixWord ++ tailWord_6641344).sum := by decide
  have hdescent : baseEnd_6641344 < baseStart_6641344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641387 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 1, 5]
def baseStart_6641387 : Nat := 118140960795 + 6641387 * 2 ^ 59
def prefixEnd_6641387 : Nat := 4983230072969 + 3 ^ 40 * 6641387 * 2
def baseEnd_6641387 : Nat := 1136741247840637425506441

theorem tailTrace_6641387 : CollatzResearch.WordTrace tailWord_6641387 prefixEnd_6641387 1136741247840637425506441 := by
  unfold tailWord_6641387
  simp only [CollatzResearch.WordTrace]
  refine ⟨242231283990396632441770415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161487522660264421627846943 242231283990396632441770415)
  ·
    refine ⟨363346925985594948662655623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242231283990396632441770415 363346925985594948662655623)
    ·
      refine ⟨545020388978392422993983435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363346925985594948662655623 545020388978392422993983435)
      ·
        refine ⟨817530583467588634490975153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545020388978392422993983435 817530583467588634490975153)
        ·
          refine ⟨613147937600691475868231365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817530583467588634490975153 613147937600691475868231365)
          ·
            refine ⟨114965238300129651725293381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 613147937600691475868231365 114965238300129651725293381)
            ·
              refine ⟨21555982181274309698492509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114965238300129651725293381 21555982181274309698492509)
              ·
                refine ⟨8083493317977866136934691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21555982181274309698492509 8083493317977866136934691)
                ·
                  refine ⟨12125239976966799205402037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083493317977866136934691 12125239976966799205402037)
                  ·
                    refine ⟨1136741247840637425506441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12125239976966799205402037 1136741247840637425506441)
                    ·
                      rfl

theorem cell23_6641387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 5].length) (baseStart_6641387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641387 prefixEnd_6641387 := by exact prefixLift 6641387
  have htrace : WordTrace (prefixWord ++ tailWord_6641387) baseStart_6641387 baseEnd_6641387 := by
    simpa [prefixWord, tailWord_6641387, baseEnd_6641387] using wordTrace_append hprefix tailTrace_6641387
  have hstable : (prefixWord ++ tailWord_6641387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641387).length < 2 ^ (prefixWord ++ tailWord_6641387).sum := by decide
  have hdescent : baseEnd_6641387 < baseStart_6641387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641400 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_6641400 : Nat := 118140960795 + 6641400 * 2 ^ 59
def prefixEnd_6641400 : Nat := 4983230072969 + 3 ^ 40 * 6641400 * 2
def baseEnd_6641400 : Nat := 1136743472923473575218921

theorem tailTrace_6641400 : CollatzResearch.WordTrace tailWord_6641400 prefixEnd_6641400 1136743472923473575218921 := by
  unfold tailWord_6641400
  simp only [CollatzResearch.WordTrace]
  refine ⟨121115879069674767830996827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161487838759566357107995769 121115879069674767830996827)
  ·
    refine ⟨181673818604512151746495241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121115879069674767830996827 181673818604512151746495241)
    ·
      refine ⟨136255363953384113809871431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181673818604512151746495241 136255363953384113809871431)
      ·
        refine ⟨204383045930076170714807147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136255363953384113809871431 204383045930076170714807147)
        ·
          refine ⟨306574568895114256072210721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204383045930076170714807147 306574568895114256072210721)
          ·
            refine ⟨229930926671335692054158041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306574568895114256072210721 229930926671335692054158041)
            ·
              refine ⟨172448195003501769040618531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229930926671335692054158041 172448195003501769040618531)
              ·
                refine ⟨258672292505252653560927797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172448195003501769040618531 258672292505252653560927797)
                ·
                  refine ⟨24250527422367436271336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258672292505252653560927797 24250527422367436271336981)
                  ·
                    refine ⟨1136743472923473575218921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24250527422367436271336981 1136743472923473575218921)
                    ·
                      rfl

theorem cell23_6641400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_6641400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641400 prefixEnd_6641400 := by exact prefixLift 6641400
  have htrace : WordTrace (prefixWord ++ tailWord_6641400) baseStart_6641400 baseEnd_6641400 := by
    simpa [prefixWord, tailWord_6641400, baseEnd_6641400] using wordTrace_append hprefix tailTrace_6641400
  have hstable : (prefixWord ++ tailWord_6641400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641400).length < 2 ^ (prefixWord ++ tailWord_6641400).sum := by decide
  have hdescent : baseEnd_6641400 < baseStart_6641400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641441 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6641441 : Nat := 118140960795 + 6641441 * 2 ^ 59
def prefixEnd_6641441 : Nat := 4983230072969 + 3 ^ 40 * 6641441 * 2
def baseEnd_6641441 : Nat := 3410251471477255065244075

theorem tailTrace_6641441 : CollatzResearch.WordTrace tailWord_6641441 prefixEnd_6641441 3410251471477255065244075 := by
  unfold tailWord_6641441
  simp only [CollatzResearch.WordTrace]
  refine ⟨242233253532200999664236177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161488835688133999776157451 242233253532200999664236177)
  ·
    refine ⟨181674940149150749748177133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242233253532200999664236177 181674940149150749748177133)
    ·
      refine ⟨68128102555931531155566425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181674940149150749748177133 68128102555931531155566425)
      ·
        refine ⟨51096076916948648366674819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68128102555931531155566425 51096076916948648366674819)
        ·
          refine ⟨76644115375422972550012229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51096076916948648366674819 76644115375422972550012229)
          ·
            refine ⟨14370771632891807353127293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76644115375422972550012229 14370771632891807353127293)
            ·
              refine ⟨5389039362334427757422735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14370771632891807353127293 5389039362334427757422735)
              ·
                refine ⟨8083559043501641636134103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389039362334427757422735 8083559043501641636134103)
                ·
                  refine ⟨12125338565252462454201155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083559043501641636134103 12125338565252462454201155)
                  ·
                    refine ⟨18188007847878693681301733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12125338565252462454201155 18188007847878693681301733)
                    ·
                      refine ⟨3410251471477255065244075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18188007847878693681301733 3410251471477255065244075)
                      ·
                        rfl

theorem cell23_6641441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6641441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641441 prefixEnd_6641441 := by exact prefixLift 6641441
  have htrace : WordTrace (prefixWord ++ tailWord_6641441) baseStart_6641441 baseEnd_6641441 := by
    simpa [prefixWord, tailWord_6641441, baseEnd_6641441] using wordTrace_append hprefix tailTrace_6641441
  have hstable : (prefixWord ++ tailWord_6641441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641441).length < 2 ^ (prefixWord ++ tailWord_6641441).sum := by decide
  have hdescent : baseEnd_6641441 < baseStart_6641441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641444 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_6641444 : Nat := 118140960795 + 6641444 * 2 ^ 59
def prefixEnd_6641444 : Nat := 4983230072969 + 3 ^ 40 * 6641444 * 2
def baseEnd_6641444 : Nat := 3410253011919218553506561

theorem tailTrace_6641444 : CollatzResearch.WordTrace tailWord_6641444 prefixEnd_6641444 3410253011919218553506561 := by
  unfold tailWord_6641444
  simp only [CollatzResearch.WordTrace]
  refine ⟨121116681475595065588297693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161488908634126754117730257 121116681475595065588297693)
  ·
    refine ⟨45418755553348149595611635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121116681475595065588297693 45418755553348149595611635)
    ·
      refine ⟨68128133330022224393417453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45418755553348149595611635 68128133330022224393417453)
      ·
        refine ⟨25548049998758334147531545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68128133330022224393417453 25548049998758334147531545)
        ·
          refine ⟨19161037499068750610648659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25548049998758334147531545 19161037499068750610648659)
          ·
            refine ⟨28741556248603125915972989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19161037499068750610648659 28741556248603125915972989)
            ·
              refine ⟨10778083593226172218489871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28741556248603125915972989 10778083593226172218489871)
              ·
                refine ⟨16167125389839258327734807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778083593226172218489871 16167125389839258327734807)
                ·
                  refine ⟨24250688084758887491602211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16167125389839258327734807 24250688084758887491602211)
                  ·
                    refine ⟨36376032127138331237403317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24250688084758887491602211 36376032127138331237403317)
                    ·
                      refine ⟨3410253011919218553506561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36376032127138331237403317 3410253011919218553506561)
                      ·
                        rfl

theorem cell23_6641444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_6641444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641444 prefixEnd_6641444 := by exact prefixLift 6641444
  have htrace : WordTrace (prefixWord ++ tailWord_6641444) baseStart_6641444 baseEnd_6641444 := by
    simpa [prefixWord, tailWord_6641444, baseEnd_6641444] using wordTrace_append hprefix tailTrace_6641444
  have hstable : (prefixWord ++ tailWord_6641444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641444).length < 2 ^ (prefixWord ++ tailWord_6641444).sum := by decide
  have hdescent : baseEnd_6641444 < baseStart_6641444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641478 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6641478 : Nat := 118140960795 + 6641478 * 2 ^ 59
def prefixEnd_6641478 : Nat := 4983230072969 + 3 ^ 40 * 6641478 * 2
def baseEnd_6641478 : Nat := 3410270470261471420481405

theorem tailTrace_6641478 : CollatzResearch.WordTrace tailWord_6641478 prefixEnd_6641478 3410270470261471420481405 := by
  unfold tailWord_6641478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569831344783342343229159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161489735355377969988888725 7569831344783342343229159)
  ·
    refine ⟨11354747017175013514843739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569831344783342343229159 11354747017175013514843739)
    ·
      refine ⟨17032120525762520272265609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354747017175013514843739 17032120525762520272265609)
      ·
        refine ⟨12774090394321890204199207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17032120525762520272265609 12774090394321890204199207)
        ·
          refine ⟨19161135591482835306298811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12774090394321890204199207 19161135591482835306298811)
          ·
            refine ⟨28741703387224252959448217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19161135591482835306298811 28741703387224252959448217)
            ·
              refine ⟨21556277540418189719586163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28741703387224252959448217 21556277540418189719586163)
              ·
                refine ⟨32334416310627284579379245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21556277540418189719586163 32334416310627284579379245)
                ·
                  refine ⟨12125406116485231717267217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32334416310627284579379245 12125406116485231717267217)
                  ·
                    refine ⟨9094054587363923787950413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12125406116485231717267217 9094054587363923787950413)
                    ·
                      refine ⟨3410270470261471420481405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094054587363923787950413 3410270470261471420481405)
                      ·
                        rfl

theorem cell23_6641478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6641478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641478 prefixEnd_6641478 := by exact prefixLift 6641478
  have htrace : WordTrace (prefixWord ++ tailWord_6641478) baseStart_6641478 baseEnd_6641478 := by
    simpa [prefixWord, tailWord_6641478, baseEnd_6641478] using wordTrace_append hprefix tailTrace_6641478
  have hstable : (prefixWord ++ tailWord_6641478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641478).length < 2 ^ (prefixWord ++ tailWord_6641478).sum := by decide
  have hdescent : baseEnd_6641478 < baseStart_6641478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641495 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_6641495 : Nat := 118140960795 + 6641495 * 2 ^ 59
def prefixEnd_6641495 : Nat := 4983230072969 + 3 ^ 40 * 6641495 * 2
def baseEnd_6641495 : Nat := 3410279199432597853968827

theorem tailTrace_6641495 : CollatzResearch.WordTrace tailWord_6641495 prefixEnd_6641495 3410279199432597853968827 := by
  unfold tailWord_6641495
  simp only [CollatzResearch.WordTrace]
  refine ⟨242235223074005366886701939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161490148716003577924467959 242235223074005366886701939)
  ·
    refine ⟨363352834611008050330052909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242235223074005366886701939 363352834611008050330052909)
    ·
      refine ⟨136257312979128018873769841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363352834611008050330052909 136257312979128018873769841)
      ·
        refine ⟨102192984734346014155327381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136257312979128018873769841 102192984734346014155327381)
        ·
          refine ⟨4790296159422469413530971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102192984734346014155327381 4790296159422469413530971)
          ·
            refine ⟨7185444239133704120296457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790296159422469413530971 7185444239133704120296457)
            ·
              refine ⟨5389083179350278090222343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185444239133704120296457 5389083179350278090222343)
              ·
                refine ⟨8083624769025417135333515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389083179350278090222343 8083624769025417135333515)
                ·
                  refine ⟨12125437153538125703000273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083624769025417135333515 12125437153538125703000273)
                  ·
                    refine ⟨9094077865153594277250205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12125437153538125703000273 9094077865153594277250205)
                    ·
                      refine ⟨3410279199432597853968827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094077865153594277250205 3410279199432597853968827)
                      ·
                        rfl

theorem cell23_6641495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_6641495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641495 prefixEnd_6641495 := by exact prefixLift 6641495
  have htrace : WordTrace (prefixWord ++ tailWord_6641495) baseStart_6641495 baseEnd_6641495 := by
    simpa [prefixWord, tailWord_6641495, baseEnd_6641495] using wordTrace_append hprefix tailTrace_6641495
  have hstable : (prefixWord ++ tailWord_6641495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641495).length < 2 ^ (prefixWord ++ tailWord_6641495).sum := by decide
  have hdescent : baseEnd_6641495 < baseStart_6641495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641621 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6641621 : Nat := 118140960795 + 6641621 * 2 ^ 59
def prefixEnd_6641621 : Nat := 4983230072969 + 3 ^ 40 * 6641621 * 2
def baseEnd_6641621 : Nat := 3410343897995064360993247

theorem tailTrace_6641621 : CollatzResearch.WordTrace tailWord_6641621 prefixEnd_6641621 3410343897995064360993247 := by
  unfold tailWord_6641621
  simp only [CollatzResearch.WordTrace]
  refine ⟨242239818671548890405788717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161493212447699260270525811 242239818671548890405788717)
  ·
    refine ⟨90839932001830833902170769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242239818671548890405788717 90839932001830833902170769)
    ·
      refine ⟨68129949001373125426628077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90839932001830833902170769 68129949001373125426628077)
      ·
        refine ⟨25548730875514922034985529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68129949001373125426628077 25548730875514922034985529)
        ·
          refine ⟨19161548156636191526239147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25548730875514922034985529 19161548156636191526239147)
          ·
            refine ⟨28742322234954287289358721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19161548156636191526239147 28742322234954287289358721)
            ·
              refine ⟨21556741676215715467019041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28742322234954287289358721 21556741676215715467019041)
              ·
                refine ⟨16167556257161786600264281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21556741676215715467019041 16167556257161786600264281)
                ·
                  refine ⟨12125667192871339950198211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16167556257161786600264281 12125667192871339950198211)
                  ·
                    refine ⟨18188500789307009925297317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12125667192871339950198211 18188500789307009925297317)
                    ·
                      refine ⟨3410343897995064360993247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18188500789307009925297317 3410343897995064360993247)
                      ·
                        rfl

theorem cell23_6641621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6641621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641621 prefixEnd_6641621 := by exact prefixLift 6641621
  have htrace : WordTrace (prefixWord ++ tailWord_6641621) baseStart_6641621 baseEnd_6641621 := by
    simpa [prefixWord, tailWord_6641621, baseEnd_6641621] using wordTrace_append hprefix tailTrace_6641621
  have hstable : (prefixWord ++ tailWord_6641621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641621).length < 2 ^ (prefixWord ++ tailWord_6641621).sum := by decide
  have hdescent : baseEnd_6641621 < baseStart_6641621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641622 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_6641622 : Nat := 118140960795 + 6641622 * 2 ^ 59
def prefixEnd_6641622 : Nat := 4983230072969 + 3 ^ 40 * 6641622 * 2
def baseEnd_6641622 : Nat := 378927156830635428564527

theorem tailTrace_6641622 : CollatzResearch.WordTrace tailWord_6641622 prefixEnd_6641622 378927156830635428564527 := by
  unfold tailWord_6641622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15139990946534079223535945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161493236763030178384383413 15139990946534079223535945)
  ·
    refine ⟨11354993209900559417651959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15139990946534079223535945 11354993209900559417651959)
    ·
      refine ⟨17032489814850839126477939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354993209900559417651959 17032489814850839126477939)
      ·
        refine ⟨25548734722276258689716909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17032489814850839126477939 25548734722276258689716909)
        ·
          refine ⟨9580775520853597008643841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25548734722276258689716909 9580775520853597008643841)
          ·
            refine ⟨7185581640640197756482881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580775520853597008643841 7185581640640197756482881)
            ·
              refine ⟨5389186230480148317362161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185581640640197756482881 5389186230480148317362161)
              ·
                refine ⟨4041889672860111238021621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389186230480148317362161 4041889672860111238021621)
                ·
                  refine ⟨378927156830635428564527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041889672860111238021621 378927156830635428564527)
                  ·
                    rfl

theorem cell23_6641622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_6641622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641622 prefixEnd_6641622 := by exact prefixLift 6641622
  have htrace : WordTrace (prefixWord ++ tailWord_6641622) baseStart_6641622 baseEnd_6641622 := by
    simpa [prefixWord, tailWord_6641622, baseEnd_6641622] using wordTrace_append hprefix tailTrace_6641622
  have hstable : (prefixWord ++ tailWord_6641622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641622).length < 2 ^ (prefixWord ++ tailWord_6641622).sum := by decide
  have hdescent : baseEnd_6641622 < baseStart_6641622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641688 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_6641688 : Nat := 118140960795 + 6641688 * 2 ^ 59
def prefixEnd_6641688 : Nat := 4983230072969 + 3 ^ 40 * 6641688 * 2
def baseEnd_6641688 : Nat := 3410378301198915598855439

theorem tailTrace_6641688 : CollatzResearch.WordTrace tailWord_6641688 prefixEnd_6641688 3410378301198915598855439 := by
  unfold tailWord_6641688
  simp only [CollatzResearch.WordTrace]
  refine ⟨121121131181153080424238859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161494841574870773898985145 121121131181153080424238859)
  ·
    refine ⟨181681696771729620636358289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121121131181153080424238859 181681696771729620636358289)
    ·
      refine ⟨136261272578797215477268717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181681696771729620636358289 136261272578797215477268717)
      ·
        refine ⟨51097977217048955803975769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136261272578797215477268717 51097977217048955803975769)
        ·
          refine ⟨38323482912786716852981827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51097977217048955803975769 38323482912786716852981827)
          ·
            refine ⟨57485224369180075279472741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38323482912786716852981827 57485224369180075279472741)
            ·
              refine ⟨10778479569221264114901139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57485224369180075279472741 10778479569221264114901139)
              ·
                refine ⟨16167719353831896172351709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778479569221264114901139 16167719353831896172351709)
                ·
                  refine ⟨6062894757686961064631891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16167719353831896172351709 6062894757686961064631891)
                  ·
                    refine ⟨9094342136530441596947837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062894757686961064631891 9094342136530441596947837)
                    ·
                      refine ⟨3410378301198915598855439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094342136530441596947837 3410378301198915598855439)
                      ·
                        rfl

theorem cell23_6641688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_6641688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641688 prefixEnd_6641688 := by exact prefixLift 6641688
  have htrace : WordTrace (prefixWord ++ tailWord_6641688) baseStart_6641688 baseEnd_6641688 := by
    simpa [prefixWord, tailWord_6641688, baseEnd_6641688] using wordTrace_append hprefix tailTrace_6641688
  have hstable : (prefixWord ++ tailWord_6641688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641688).length < 2 ^ (prefixWord ++ tailWord_6641688).sum := by decide
  have hdescent : baseEnd_6641688 < baseStart_6641688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641741 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6641741 : Nat := 118140960795 + 6641741 * 2 ^ 59
def prefixEnd_6641741 : Nat := 4983230072969 + 3 ^ 40 * 6641741 * 2
def baseEnd_6641741 : Nat := 3410405515673603891492695

theorem tailTrace_6641741 : CollatzResearch.WordTrace tailWord_6641741 prefixEnd_6641741 3410405515673603891492695 := by
  unfold tailWord_6641741
  simp only [CollatzResearch.WordTrace]
  refine ⟨242244195431114150900157077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161496130287409433933438051 242244195431114150900157077)
  ·
    refine ⟨11355196660833475823444863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 242244195431114150900157077 11355196660833475823444863)
    ·
      refine ⟨17032794991250213735167295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11355196660833475823444863 17032794991250213735167295)
      ·
        refine ⟨25549192486875320602750943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17032794991250213735167295 25549192486875320602750943)
        ·
          refine ⟨38323788730312980904126415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25549192486875320602750943 38323788730312980904126415)
          ·
            refine ⟨57485683095469471356189623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38323788730312980904126415 57485683095469471356189623)
            ·
              refine ⟨86228524643204207034284435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57485683095469471356189623 86228524643204207034284435)
              ·
                refine ⟨129342786964806310551426653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86228524643204207034284435 129342786964806310551426653)
                ·
                  refine ⟨48503545111802366456784995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129342786964806310551426653 48503545111802366456784995)
                  ·
                    refine ⟨72755317667703549685177493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48503545111802366456784995 72755317667703549685177493)
                    ·
                      refine ⟨3410405515673603891492695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72755317667703549685177493 3410405515673603891492695)
                      ·
                        rfl

theorem cell23_6641741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6641741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641741 prefixEnd_6641741 := by exact prefixLift 6641741
  have htrace : WordTrace (prefixWord ++ tailWord_6641741) baseStart_6641741 baseEnd_6641741 := by
    simpa [prefixWord, tailWord_6641741, baseEnd_6641741] using wordTrace_append hprefix tailTrace_6641741
  have hstable : (prefixWord ++ tailWord_6641741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641741).length < 2 ^ (prefixWord ++ tailWord_6641741).sum := by decide
  have hdescent : baseEnd_6641741 < baseStart_6641741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641754 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_6641754 : Nat := 118140960795 + 6641754 * 2 ^ 59
def prefixEnd_6641754 : Nat := 4983230072969 + 3 ^ 40 * 6641754 * 2
def baseEnd_6641754 : Nat := 3410412190922112340630135

theorem tailTrace_6641754 : CollatzResearch.WordTrace tailWord_6641754 prefixEnd_6641754 3410412190922112340630135 := by
  unfold tailWord_6641754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60561167395016763530095079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161496446386711369413586877 60561167395016763530095079)
  ·
    refine ⟨90841751092525145295142619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60561167395016763530095079 90841751092525145295142619)
    ·
      refine ⟨136262626638787717942713929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90841751092525145295142619 136262626638787717942713929)
      ·
        refine ⟨102196969979090788457035447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136262626638787717942713929 102196969979090788457035447)
        ·
          refine ⟨153295454968636182685553171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102196969979090788457035447 153295454968636182685553171)
          ·
            refine ⟨229943182452954274028329757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153295454968636182685553171 229943182452954274028329757)
            ·
              refine ⟨86228693419857852760623659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229943182452954274028329757 86228693419857852760623659)
              ·
                refine ⟨129343040129786779140935489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86228693419857852760623659 129343040129786779140935489)
                ·
                  refine ⟨97007280097340084355701617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129343040129786779140935489 97007280097340084355701617)
                  ·
                    refine ⟨72755460073005063266776213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97007280097340084355701617 72755460073005063266776213)
                    ·
                      refine ⟨3410412190922112340630135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72755460073005063266776213 3410412190922112340630135)
                      ·
                        rfl

theorem cell23_6641754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_6641754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641754 prefixEnd_6641754 := by exact prefixLift 6641754
  have htrace : WordTrace (prefixWord ++ tailWord_6641754) baseStart_6641754 baseEnd_6641754 := by
    simpa [prefixWord, tailWord_6641754, baseEnd_6641754] using wordTrace_append hprefix tailTrace_6641754
  have hstable : (prefixWord ++ tailWord_6641754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641754).length < 2 ^ (prefixWord ++ tailWord_6641754).sum := by decide
  have hdescent : baseEnd_6641754 < baseStart_6641754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641761 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_6641761 : Nat := 118140960795 + 6641761 * 2 ^ 59
def prefixEnd_6641761 : Nat := 4983230072969 + 3 ^ 40 * 6641761 * 2
def baseEnd_6641761 : Nat := 3410415785286693813242603

theorem tailTrace_6641761 : CollatzResearch.WordTrace tailWord_6641761 prefixEnd_6641761 3410415785286693813242603 := by
  unfold tailWord_6641761
  simp only [CollatzResearch.WordTrace]
  refine ⟨242244924891041694315885137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161496616594027796210590091 242244924891041694315885137)
  ·
    refine ⟨181683693668281270736913853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242244924891041694315885137 181683693668281270736913853)
    ·
      refine ⟨68131385125605476526342695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181683693668281270736913853 68131385125605476526342695)
      ·
        refine ⟨102197077688408214789514043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68131385125605476526342695 102197077688408214789514043)
        ·
          refine ⟨153295616532612322184271065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102197077688408214789514043 153295616532612322184271065)
          ·
            refine ⟨114971712399459241638203299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153295616532612322184271065 114971712399459241638203299)
            ·
              refine ⟨172457568599188862457304949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114971712399459241638203299 172457568599188862457304949)
              ·
                refine ⟨16167897056173955855372339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172457568599188862457304949 16167897056173955855372339)
                ·
                  refine ⟨24251845584260933783058509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16167897056173955855372339 24251845584260933783058509)
                  ·
                    refine ⟨9094442094097850168646941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24251845584260933783058509 9094442094097850168646941)
                    ·
                      refine ⟨3410415785286693813242603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094442094097850168646941 3410415785286693813242603)
                      ·
                        rfl

theorem cell23_6641761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_6641761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641761 prefixEnd_6641761 := by exact prefixLift 6641761
  have htrace : WordTrace (prefixWord ++ tailWord_6641761) baseStart_6641761 baseEnd_6641761 := by
    simpa [prefixWord, tailWord_6641761, baseEnd_6641761] using wordTrace_append hprefix tailTrace_6641761
  have hstable : (prefixWord ++ tailWord_6641761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641761).length < 2 ^ (prefixWord ++ tailWord_6641761).sum := by decide
  have hdescent : baseEnd_6641761 < baseStart_6641761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641762 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6641762 : Nat := 118140960795 + 6641762 * 2 ^ 59
def prefixEnd_6641762 : Nat := 4983230072969 + 3 ^ 40 * 6641762 * 2
def baseEnd_6641762 : Nat := 3410416298767348309330099

theorem tailTrace_6641762 : CollatzResearch.WordTrace tailWord_6641762 prefixEnd_6641762 3410416298767348309330099 := by
  unfold tailWord_6641762
  simp only [CollatzResearch.WordTrace]
  refine ⟨60561240341009517871667885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161496640909358714324447693 60561240341009517871667885)
  ·
    refine ⟨22710465127878569201875457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60561240341009517871667885 22710465127878569201875457)
    ·
      refine ⟨17032848845908926901406593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22710465127878569201875457 17032848845908926901406593)
      ·
        refine ⟨12774636634431695176054945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17032848845908926901406593 12774636634431695176054945)
        ·
          refine ⟨9580977475823771382041209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12774636634431695176054945 9580977475823771382041209)
          ·
            refine ⟨7185733106867828536530907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580977475823771382041209 7185733106867828536530907)
            ·
              refine ⟨10778599660301742804796361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185733106867828536530907 10778599660301742804796361)
              ·
                refine ⟨8083949745226307103597271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778599660301742804796361 8083949745226307103597271)
                ·
                  refine ⟨12125924617839460655395907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083949745226307103597271 12125924617839460655395907)
                  ·
                    refine ⟨18188886926759190983093861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12125924617839460655395907 18188886926759190983093861)
                    ·
                      refine ⟨3410416298767348309330099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18188886926759190983093861 3410416298767348309330099)
                      ·
                        rfl

theorem cell23_6641762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6641762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641762 prefixEnd_6641762 := by exact prefixLift 6641762
  have htrace : WordTrace (prefixWord ++ tailWord_6641762) baseStart_6641762 baseEnd_6641762 := by
    simpa [prefixWord, tailWord_6641762, baseEnd_6641762] using wordTrace_append hprefix tailTrace_6641762
  have hstable : (prefixWord ++ tailWord_6641762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641762).length < 2 ^ (prefixWord ++ tailWord_6641762).sum := by decide
  have hdescent : baseEnd_6641762 < baseStart_6641762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641765 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_6641765 : Nat := 118140960795 + 6641765 * 2 ^ 59
def prefixEnd_6641765 : Nat := 4983230072969 + 3 ^ 40 * 6641765 * 2
def baseEnd_6641765 : Nat := 3410417839209311797592585

theorem tailTrace_6641765 : CollatzResearch.WordTrace tailWord_6641765 prefixEnd_6641765 3410417839209311797592585 := by
  unfold tailWord_6641765
  simp only [CollatzResearch.WordTrace]
  refine ⟨242245070783027202999030749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161496713855351468666020499 242245070783027202999030749)
  ·
    refine ⟨90841901543635201124636531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242245070783027202999030749 90841901543635201124636531)
    ·
      refine ⟨136262852315452801686954797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90841901543635201124636531 136262852315452801686954797)
      ·
        refine ⟨51098569618294800632608049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136262852315452801686954797 51098569618294800632608049)
        ·
          refine ⟨38323927213721100474456037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51098569618294800632608049 38323927213721100474456037)
          ·
            refine ⟨7185736352572706338960507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38323927213721100474456037 7185736352572706338960507)
            ·
              refine ⟨10778604528859059508440761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185736352572706338960507 10778604528859059508440761)
              ·
                refine ⟨8083953396644294631330571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778604528859059508440761 8083953396644294631330571)
                ·
                  refine ⟨12125930094966441946995857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083953396644294631330571 12125930094966441946995857)
                  ·
                    refine ⟨9094447571224831460246893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12125930094966441946995857 9094447571224831460246893)
                    ·
                      refine ⟨3410417839209311797592585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094447571224831460246893 3410417839209311797592585)
                      ·
                        rfl

theorem cell23_6641765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_6641765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641765 prefixEnd_6641765 := by exact prefixLift 6641765
  have htrace : WordTrace (prefixWord ++ tailWord_6641765) baseStart_6641765 baseEnd_6641765 := by
    simpa [prefixWord, tailWord_6641765, baseEnd_6641765] using wordTrace_append hprefix tailTrace_6641765
  have hstable : (prefixWord ++ tailWord_6641765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641765).length < 2 ^ (prefixWord ++ tailWord_6641765).sum := by decide
  have hdescent : baseEnd_6641765 < baseStart_6641765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641778 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_6641778 : Nat := 118140960795 + 6641778 * 2 ^ 59
def prefixEnd_6641778 : Nat := 4983230072969 + 3 ^ 40 * 6641778 * 2
def baseEnd_6641778 : Nat := 3410424514457820246730025

theorem tailTrace_6641778 : CollatzResearch.WordTrace tailWord_6641778 prefixEnd_6641778 3410424514457820246730025 := by
  unfold tailWord_6641778
  simp only [CollatzResearch.WordTrace]
  refine ⟨60561386232995026554813497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161497029954653404146169325 60561386232995026554813497)
  ·
    refine ⟨45421039674746269916110123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60561386232995026554813497 45421039674746269916110123)
    ·
      refine ⟨68131559512119404874165185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45421039674746269916110123 68131559512119404874165185)
      ·
        refine ⟨51098669634089553655623889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68131559512119404874165185 51098669634089553655623889)
        ·
          refine ⟨38324002225567165241717917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51098669634089553655623889 38324002225567165241717917)
          ·
            refine ⟨14371500834587686965644219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38324002225567165241717917 14371500834587686965644219)
            ·
              refine ⟨21557251251881530448466329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14371500834587686965644219 21557251251881530448466329)
              ·
                refine ⟨16167938438911147836349747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21557251251881530448466329 16167938438911147836349747)
                ·
                  refine ⟨24251907658366721754524621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16167938438911147836349747 24251907658366721754524621)
                  ·
                    refine ⟨9094465371887520657946733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24251907658366721754524621 9094465371887520657946733)
                    ·
                      refine ⟨3410424514457820246730025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094465371887520657946733 3410424514457820246730025)
                      ·
                        rfl

theorem cell23_6641778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_6641778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641778 prefixEnd_6641778 := by exact prefixLift 6641778
  have htrace : WordTrace (prefixWord ++ tailWord_6641778) baseStart_6641778 baseEnd_6641778 := by
    simpa [prefixWord, tailWord_6641778, baseEnd_6641778] using wordTrace_append hprefix tailTrace_6641778
  have hstable : (prefixWord ++ tailWord_6641778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641778).length < 2 ^ (prefixWord ++ tailWord_6641778).sum := by decide
  have hdescent : baseEnd_6641778 < baseStart_6641778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641782 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6641782 : Nat := 118140960795 + 6641782 * 2 ^ 59
def prefixEnd_6641782 : Nat := 4983230072969 + 3 ^ 40 * 6641782 * 2
def baseEnd_6641782 : Nat := 3410426568380438231080007

theorem tailTrace_6641782 : CollatzResearch.WordTrace tailWord_6641782 prefixEnd_6641782 3410426568380438231080007 := by
  unfold tailWord_6641782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140355676497850931399975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161497127215977076601599733 15140355676497850931399975)
  ·
    refine ⟨22710533514746776397099963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15140355676497850931399975 22710533514746776397099963)
    ·
      refine ⟨34065800272120164595649945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22710533514746776397099963 34065800272120164595649945)
      ·
        refine ⟨25549350204090123446737459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34065800272120164595649945 25549350204090123446737459)
        ·
          refine ⟨38324025306135185170106189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25549350204090123446737459 38324025306135185170106189)
          ·
            refine ⟨14371509489800694438789821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38324025306135185170106189 14371509489800694438789821)
            ·
              refine ⟨5389316058675260414546183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14371509489800694438789821 5389316058675260414546183)
              ·
                refine ⟨8083974088012890621819275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389316058675260414546183 8083974088012890621819275)
                ·
                  refine ⟨12125961132019335932728913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083974088012890621819275 12125961132019335932728913)
                  ·
                    refine ⟨9094470849014501949546685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12125961132019335932728913 9094470849014501949546685)
                    ·
                      refine ⟨3410426568380438231080007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094470849014501949546685 3410426568380438231080007)
                      ·
                        rfl

theorem cell23_6641782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6641782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641782 prefixEnd_6641782 := by exact prefixLift 6641782
  have htrace : WordTrace (prefixWord ++ tailWord_6641782) baseStart_6641782 baseEnd_6641782 := by
    simpa [prefixWord, tailWord_6641782, baseEnd_6641782] using wordTrace_append hprefix tailTrace_6641782
  have hstable : (prefixWord ++ tailWord_6641782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641782).length < 2 ^ (prefixWord ++ tailWord_6641782).sum := by decide
  have hdescent : baseEnd_6641782 < baseStart_6641782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641795 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 3]
def baseStart_6641795 : Nat := 118140960795 + 6641795 * 2 ^ 59
def prefixEnd_6641795 : Nat := 4983230072969 + 3 ^ 40 * 6641795 * 2
def baseEnd_6641795 : Nat := 3410433243628946680217447

theorem tailTrace_6641795 : CollatzResearch.WordTrace tailWord_6641795 prefixEnd_6641795 3410433243628946680217447 := by
  unfold tailWord_6641795
  simp only [CollatzResearch.WordTrace]
  refine ⟨242246164972918518122622839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161497443315279012081748559 242246164972918518122622839)
  ·
    refine ⟨363369247459377777183934259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242246164972918518122622839 363369247459377777183934259)
    ·
      refine ⟨545053871189066665775901389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363369247459377777183934259 545053871189066665775901389)
      ·
        refine ⟨204395201695899999665963021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545053871189066665775901389 204395201695899999665963021)
        ·
          refine ⟨76648200635962499874736133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204395201695899999665963021 76648200635962499874736133)
          ·
            refine ⟨14371537619242968726513025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76648200635962499874736133 14371537619242968726513025)
            ·
              refine ⟨10778653214432226544884769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14371537619242968726513025 10778653214432226544884769)
              ·
                refine ⟨8083989910824169908663577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778653214432226544884769 8083989910824169908663577)
                ·
                  refine ⟨6062992433118127431497683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8083989910824169908663577 6062992433118127431497683)
                  ·
                    refine ⟨9094488649677191147246525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062992433118127431497683 9094488649677191147246525)
                    ·
                      refine ⟨3410433243628946680217447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094488649677191147246525 3410433243628946680217447)
                      ·
                        rfl

theorem cell23_6641795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_6641795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641795 prefixEnd_6641795 := by exact prefixLift 6641795
  have htrace : WordTrace (prefixWord ++ tailWord_6641795) baseStart_6641795 baseEnd_6641795 := by
    simpa [prefixWord, tailWord_6641795, baseEnd_6641795] using wordTrace_append hprefix tailTrace_6641795
  have hstable : (prefixWord ++ tailWord_6641795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641795).length < 2 ^ (prefixWord ++ tailWord_6641795).sum := by decide
  have hdescent : baseEnd_6641795 < baseStart_6641795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641812 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6641812 : Nat := 118140960795 + 6641812 * 2 ^ 59
def prefixEnd_6641812 : Nat := 4983230072969 + 3 ^ 40 * 6641812 * 2
def baseEnd_6641812 : Nat := 3410441972800073113704869

theorem tailTrace_6641812 : CollatzResearch.WordTrace tailWord_6641812 prefixEnd_6641812 3410441972800073113704869 := by
  unfold tailWord_6641812
  simp only [CollatzResearch.WordTrace]
  refine ⟨121123392506928465012995845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161497856675904620017327793 121123392506928465012995845)
  ·
    refine ⟨22710636095049087189936721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121123392506928465012995845 22710636095049087189936721)
    ·
      refine ⟨17032977071286815392452541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22710636095049087189936721 17032977071286815392452541)
      ·
        refine ⟨6387366401732555772169703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17032977071286815392452541 6387366401732555772169703)
        ·
          refine ⟨9581049602598833658254555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387366401732555772169703 9581049602598833658254555)
          ·
            refine ⟨14371574403898250487381833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9581049602598833658254555 14371574403898250487381833)
            ·
              refine ⟨10778680802923687865536375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14371574403898250487381833 10778680802923687865536375)
              ·
                refine ⟨16168021204385531798304563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778680802923687865536375 16168021204385531798304563)
                ·
                  refine ⟨24252031806578297697456845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16168021204385531798304563 24252031806578297697456845)
                  ·
                    refine ⟨9094511927466861636546317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24252031806578297697456845 9094511927466861636546317)
                    ·
                      refine ⟨3410441972800073113704869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094511927466861636546317 3410441972800073113704869)
                      ·
                        rfl

theorem cell23_6641812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6641812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641812 prefixEnd_6641812 := by exact prefixLift 6641812
  have htrace : WordTrace (prefixWord ++ tailWord_6641812) baseStart_6641812 baseEnd_6641812 := by
    simpa [prefixWord, tailWord_6641812, baseEnd_6641812] using wordTrace_append hprefix tailTrace_6641812
  have hstable : (prefixWord ++ tailWord_6641812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641812).length < 2 ^ (prefixWord ++ tailWord_6641812).sum := by decide
  have hdescent : baseEnd_6641812 < baseStart_6641812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641851 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3]
def baseStart_6641851 : Nat := 118140960795 + 6641851 * 2 ^ 59
def prefixEnd_6641851 : Nat := 4983230072969 + 3 ^ 40 * 6641851 * 2
def baseEnd_6641851 : Nat := 3410461998545598461117189

theorem tailTrace_6641851 : CollatzResearch.WordTrace tailWord_6641851 prefixEnd_6641851 3410461998545598461117189 := by
  unfold tailWord_6641851
  simp only [CollatzResearch.WordTrace]
  refine ⟨242248207460715639686661407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161498804973810426457774271 242248207460715639686661407)
  ·
    refine ⟨363372311191073459529992111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242248207460715639686661407 363372311191073459529992111)
    ·
      refine ⟨545058466786610189294988167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363372311191073459529992111 545058466786610189294988167)
      ·
        refine ⟨817587700179915283942482251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545058466786610189294988167 817587700179915283942482251)
        ·
          refine ⟨1226381550269872925913723377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817587700179915283942482251 1226381550269872925913723377)
          ·
            refine ⟨919786162702404694435292533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226381550269872925913723377 919786162702404694435292533)
            ·
              refine ⟨86229952753350440103308675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 919786162702404694435292533 86229952753350440103308675)
              ·
                refine ⟨129344929130025660154963013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86229952753350440103308675 129344929130025660154963013)
                ·
                  refine ⟨24252174211879811279055565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129344929130025660154963013 24252174211879811279055565)
                  ·
                    refine ⟨9094565329454929229645837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24252174211879811279055565 9094565329454929229645837)
                    ·
                      refine ⟨3410461998545598461117189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094565329454929229645837 3410461998545598461117189)
                      ·
                        rfl

theorem cell23_6641851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 3].length) (baseStart_6641851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641851 prefixEnd_6641851 := by exact prefixLift 6641851
  have htrace : WordTrace (prefixWord ++ tailWord_6641851) baseStart_6641851 baseEnd_6641851 := by
    simpa [prefixWord, tailWord_6641851, baseEnd_6641851] using wordTrace_append hprefix tailTrace_6641851
  have hstable : (prefixWord ++ tailWord_6641851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641851).length < 2 ^ (prefixWord ++ tailWord_6641851).sum := by decide
  have hdescent : baseEnd_6641851 < baseStart_6641851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641852 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_6641852 : Nat := 118140960795 + 6641852 * 2 ^ 59
def prefixEnd_6641852 : Nat := 4983230072969 + 3 ^ 40 * 6641852 * 2
def baseEnd_6641852 : Nat := 3410462512026252957204685

theorem tailTrace_6641852 : CollatzResearch.WordTrace tailWord_6641852 prefixEnd_6641852 3410462512026252957204685 := by
  unfold tailWord_6641852
  simp only [CollatzResearch.WordTrace]
  refine ⟨121124121966856008428723905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161498829289141344571631873 121124121966856008428723905)
  ·
    refine ⟨90843091475142006321542929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121124121966856008428723905 90843091475142006321542929)
    ·
      refine ⟨68132318606356504741157197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90843091475142006321542929 68132318606356504741157197)
      ·
        refine ⟨25549619477383689277933949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68132318606356504741157197 25549619477383689277933949)
        ·
          refine ⟨9581107304018883479225231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25549619477383689277933949 9581107304018883479225231)
          ·
            refine ⟨14371660956028325218837847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9581107304018883479225231 14371660956028325218837847)
            ·
              refine ⟨21557491434042487828256771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14371660956028325218837847 21557491434042487828256771)
              ·
                refine ⟨32336237151063731742385157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21557491434042487828256771 32336237151063731742385157)
                ·
                  refine ⟨6063044465824449701697217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32336237151063731742385157 6063044465824449701697217)
                  ·
                    refine ⟨4547283349368337276272913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063044465824449701697217 4547283349368337276272913)
                    ·
                      refine ⟨3410462512026252957204685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547283349368337276272913 3410462512026252957204685)
                      ·
                        rfl

theorem cell23_6641852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_6641852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641852 prefixEnd_6641852 := by exact prefixLift 6641852
  have htrace : WordTrace (prefixWord ++ tailWord_6641852) baseStart_6641852 baseEnd_6641852 := by
    simpa [prefixWord, tailWord_6641852, baseEnd_6641852] using wordTrace_append hprefix tailTrace_6641852
  have hstable : (prefixWord ++ tailWord_6641852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641852).length < 2 ^ (prefixWord ++ tailWord_6641852).sum := by decide
  have hdescent : baseEnd_6641852 < baseStart_6641852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6641978 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_6641978 : Nat := 118140960795 + 6641978 * 2 ^ 59
def prefixEnd_6641978 : Nat := 4983230072969 + 3 ^ 40 * 6641978 * 2
def baseEnd_6641978 : Nat := 1136842403529573154743035

theorem tailTrace_6641978 : CollatzResearch.WordTrace tailWord_6641978 prefixEnd_6641978 1136842403529573154743035 := by
  unfold tailWord_6641978
  simp only [CollatzResearch.WordTrace]
  refine ⟨60563209882813885094133647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161501893020837026917689725 60563209882813885094133647)
  ·
    refine ⟨90844814824220827641200471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60563209882813885094133647 90844814824220827641200471)
    ·
      refine ⟨136267222236331241461800707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90844814824220827641200471 136267222236331241461800707)
      ·
        refine ⟨204400833354496862192701061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136267222236331241461800707 204400833354496862192701061)
        ·
          refine ⟨38325156253968161661131449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204400833354496862192701061 38325156253968161661131449)
          ·
            refine ⟨28743867190476121245848587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38325156253968161661131449 28743867190476121245848587)
            ·
              refine ⟨43115800785714181868772881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28743867190476121245848587 43115800785714181868772881)
              ·
                refine ⟨32336850589285636401579661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43115800785714181868772881 32336850589285636401579661)
                ·
                  refine ⟨12126318970982113650592373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32336850589285636401579661 12126318970982113650592373)
                  ·
                    refine ⟨1136842403529573154743035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12126318970982113650592373 1136842403529573154743035)
                    ·
                      rfl

theorem cell23_6641978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_6641978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6641978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6641978 prefixEnd_6641978 := by exact prefixLift 6641978
  have htrace : WordTrace (prefixWord ++ tailWord_6641978) baseStart_6641978 baseEnd_6641978 := by
    simpa [prefixWord, tailWord_6641978, baseEnd_6641978] using wordTrace_append hprefix tailTrace_6641978
  have hstable : (prefixWord ++ tailWord_6641978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6641978).length < 2 ^ (prefixWord ++ tailWord_6641978).sum := by decide
  have hdescent : baseEnd_6641978 < baseStart_6641978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6641978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642002 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_6642002 : Nat := 118140960795 + 6642002 * 2 ^ 59
def prefixEnd_6642002 : Nat := 4983230072969 + 3 ^ 40 * 6642002 * 2
def baseEnd_6642002 : Nat := 3410539534124427370328995

theorem tailTrace_6642002 : CollatzResearch.WordTrace tailWord_6642002 prefixEnd_6642002 3410539534124427370328995 := by
  unfold tailWord_6642002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60563428720792148118852065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161502476588779061650272173 60563428720792148118852065)
  ·
    refine ⟨45422571540594111089139049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60563428720792148118852065 45422571540594111089139049)
    ·
      refine ⟨34066928655445583316854287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45422571540594111089139049 34066928655445583316854287)
      ·
        refine ⟨51100392983168374975281431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34066928655445583316854287 51100392983168374975281431)
        ·
          refine ⟨76650589474752562462922147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51100392983168374975281431 76650589474752562462922147)
          ·
            refine ⟨114975884212128843694383221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76650589474752562462922147 114975884212128843694383221)
            ·
              refine ⟨10778989144887079096348427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114975884212128843694383221 10778989144887079096348427)
              ·
                refine ⟨16168483717330618644522641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778989144887079096348427 16168483717330618644522641)
                ·
                  refine ⟨12126362787997963983391981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16168483717330618644522641 12126362787997963983391981)
                  ·
                    refine ⟨4547386045499236493771993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12126362787997963983391981 4547386045499236493771993)
                    ·
                      refine ⟨3410539534124427370328995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547386045499236493771993 3410539534124427370328995)
                      ·
                        rfl

theorem cell23_6642002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_6642002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642002 prefixEnd_6642002 := by exact prefixLift 6642002
  have htrace : WordTrace (prefixWord ++ tailWord_6642002) baseStart_6642002 baseEnd_6642002 := by
    simpa [prefixWord, tailWord_6642002, baseEnd_6642002] using wordTrace_append hprefix tailTrace_6642002
  have hstable : (prefixWord ++ tailWord_6642002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642002).length < 2 ^ (prefixWord ++ tailWord_6642002).sum := by decide
  have hdescent : baseEnd_6642002 < baseStart_6642002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642032 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2]
def baseStart_6642032 : Nat := 118140960795 + 6642032 * 2 ^ 59
def prefixEnd_6642032 : Nat := 4983230072969 + 3 ^ 40 * 6642032 * 2
def baseEnd_6642032 : Nat := 3410554938544062252953857

theorem tailTrace_6642032 : CollatzResearch.WordTrace tailWord_6642032 prefixEnd_6642032 3410554938544062252953857 := by
  unfold tailWord_6642032
  simp only [CollatzResearch.WordTrace]
  refine ⟨121127404536529953799500175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161503206048706605066000233 121127404536529953799500175)
  ·
    refine ⟨181691106804794930699250263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121127404536529953799500175 181691106804794930699250263)
    ·
      refine ⟨272536660207192396048875395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181691106804794930699250263 272536660207192396048875395)
      ·
        refine ⟨408804990310788594073313093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272536660207192396048875395 408804990310788594073313093)
        ·
          refine ⟨76650935683272861388746205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408804990310788594073313093 76650935683272861388746205)
          ·
            refine ⟨28744100881227323020779827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76650935683272861388746205 28744100881227323020779827)
            ·
              refine ⟨43116151321840984531169741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28744100881227323020779827 43116151321840984531169741)
              ·
                refine ⟨16168556745690369199188653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43116151321840984531169741 16168556745690369199188653)
                ·
                  refine ⟨6063208779633888449695745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16168556745690369199188653 6063208779633888449695745)
                  ·
                    refine ⟨4547406584725416337271809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063208779633888449695745 4547406584725416337271809)
                    ·
                      refine ⟨3410554938544062252953857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547406584725416337271809 3410554938544062252953857)
                      ·
                        rfl

theorem cell23_6642032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2].length) (baseStart_6642032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642032 prefixEnd_6642032 := by exact prefixLift 6642032
  have htrace : WordTrace (prefixWord ++ tailWord_6642032) baseStart_6642032 baseEnd_6642032 := by
    simpa [prefixWord, tailWord_6642032, baseEnd_6642032] using wordTrace_append hprefix tailTrace_6642032
  have hstable : (prefixWord ++ tailWord_6642032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642032).length < 2 ^ (prefixWord ++ tailWord_6642032).sum := by decide
  have hdescent : baseEnd_6642032 < baseStart_6642032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642045 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_6642045 : Nat := 118140960795 + 6642045 * 2 ^ 59
def prefixEnd_6642045 : Nat := 4983230072969 + 3 ^ 40 * 6642045 * 2
def baseEnd_6642045 : Nat := 3410561613792570702091297

theorem tailTrace_6642045 : CollatzResearch.WordTrace tailWord_6642045 prefixEnd_6642045 3410561613792570702091297 := by
  unfold tailWord_6642045
  simp only [CollatzResearch.WordTrace]
  refine ⟨242255283222012810819223589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161503522148008540546149059 242255283222012810819223589)
  ·
    refine ⟨45422865604127402028604423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242255283222012810819223589 45422865604127402028604423)
    ·
      refine ⟨68134298406191103042906635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45422865604127402028604423 68134298406191103042906635)
      ·
        refine ⟨102201447609286654564359953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68134298406191103042906635 102201447609286654564359953)
        ·
          refine ⟨76651085706964990923269965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102201447609286654564359953 76651085706964990923269965)
          ·
            refine ⟨28744157140111871596226237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76651085706964990923269965 28744157140111871596226237)
            ·
              refine ⟨10779058927541951848584839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28744157140111871596226237 10779058927541951848584839)
              ·
                refine ⟨16168588391312927772877259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779058927541951848584839 16168588391312927772877259)
                ·
                  refine ⟨24252882586969391659315889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16168588391312927772877259 24252882586969391659315889)
                  ·
                    refine ⟨18189661940227043744486917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24252882586969391659315889 18189661940227043744486917)
                    ·
                      refine ⟨3410561613792570702091297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18189661940227043744486917 3410561613792570702091297)
                      ·
                        rfl

theorem cell23_6642045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_6642045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642045 prefixEnd_6642045 := by exact prefixLift 6642045
  have htrace : WordTrace (prefixWord ++ tailWord_6642045) baseStart_6642045 baseEnd_6642045 := by
    simpa [prefixWord, tailWord_6642045, baseEnd_6642045] using wordTrace_append hprefix tailTrace_6642045
  have hstable : (prefixWord ++ tailWord_6642045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642045).length < 2 ^ (prefixWord ++ tailWord_6642045).sum := by decide
  have hdescent : baseEnd_6642045 < baseStart_6642045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642049 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_6642049 : Nat := 118140960795 + 6642049 * 2 ^ 59
def prefixEnd_6642049 : Nat := 4983230072969 + 3 ^ 40 * 6642049 * 2
def baseEnd_6642049 : Nat := 3410563667715188686441279

theorem tailTrace_6642049 : CollatzResearch.WordTrace tailWord_6642049 prefixEnd_6642049 3410563667715188686441279 := by
  unfold tailWord_6642049
  simp only [CollatzResearch.WordTrace]
  refine ⟨242255429113998319502369201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161503619409332213001579467 242255429113998319502369201)
  ·
    refine ⟨181691571835498739626776901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242255429113998319502369201 181691571835498739626776901)
    ·
      refine ⟨34067169719156013680020669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181691571835498739626776901 34067169719156013680020669)
      ·
        refine ⟨12775188644683505130007751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34067169719156013680020669 12775188644683505130007751)
        ·
          refine ⟨19162782967025257695011627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12775188644683505130007751 19162782967025257695011627)
          ·
            refine ⟨28744174450537886542517441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19162782967025257695011627 28744174450537886542517441)
            ·
              refine ⟨21558130837903414906888081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28744174450537886542517441 21558130837903414906888081)
              ·
                refine ⟨16168598128427561180166061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21558130837903414906888081 16168598128427561180166061)
                ·
                  refine ⟨6063224298160335442562273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16168598128427561180166061 6063224298160335442562273)
                  ·
                    refine ⟨4547418223620251581921705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063224298160335442562273 4547418223620251581921705)
                    ·
                      refine ⟨3410563667715188686441279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547418223620251581921705 3410563667715188686441279)
                      ·
                        rfl

theorem cell23_6642049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_6642049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642049 prefixEnd_6642049 := by exact prefixLift 6642049
  have htrace : WordTrace (prefixWord ++ tailWord_6642049) baseStart_6642049 baseEnd_6642049 := by
    simpa [prefixWord, tailWord_6642049, baseEnd_6642049] using wordTrace_append hprefix tailTrace_6642049
  have hstable : (prefixWord ++ tailWord_6642049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642049).length < 2 ^ (prefixWord ++ tailWord_6642049).sum := by decide
  have hdescent : baseEnd_6642049 < baseStart_6642049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642052 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_6642052 : Nat := 118140960795 + 6642052 * 2 ^ 59
def prefixEnd_6642052 : Nat := 4983230072969 + 3 ^ 40 * 6642052 * 2
def baseEnd_6642052 : Nat := 3410565208157152174703765

theorem tailTrace_6642052 : CollatzResearch.WordTrace tailWord_6642052 prefixEnd_6642052 3410565208157152174703765 := by
  unfold tailWord_6642052
  simp only [CollatzResearch.WordTrace]
  refine ⟨121127769266493725507364205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161503692355324967343152273 121127769266493725507364205)
  ·
    refine ⟨45422913474935147065261577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121127769266493725507364205 45422913474935147065261577)
    ·
      refine ⟨34067185106201360298946183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45422913474935147065261577 34067185106201360298946183)
      ·
        refine ⟨51100777659302040448419275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34067185106201360298946183 51100777659302040448419275)
        ·
          refine ⟨76651166488953060672628913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51100777659302040448419275 76651166488953060672628913)
          ·
            refine ⟨57488374866714795504471685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76651166488953060672628913 57488374866714795504471685)
            ·
              refine ⟨10779070287509024157088441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57488374866714795504471685 10779070287509024157088441)
              ·
                refine ⟨8084302715631768117816331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10779070287509024157088441 8084302715631768117816331)
                ·
                  refine ⟨12126454073447652176724497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8084302715631768117816331 12126454073447652176724497)
                  ·
                    refine ⟨9094840555085739132543373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12126454073447652176724497 9094840555085739132543373)
                    ·
                      refine ⟨3410565208157152174703765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094840555085739132543373 3410565208157152174703765)
                      ·
                        rfl

theorem cell23_6642052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_6642052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642052 prefixEnd_6642052 := by exact prefixLift 6642052
  have htrace : WordTrace (prefixWord ++ tailWord_6642052) baseStart_6642052 baseEnd_6642052 := by
    simpa [prefixWord, tailWord_6642052, baseEnd_6642052] using wordTrace_append hprefix tailTrace_6642052
  have hstable : (prefixWord ++ tailWord_6642052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642052).length < 2 ^ (prefixWord ++ tailWord_6642052).sum := by decide
  have hdescent : baseEnd_6642052 < baseStart_6642052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642082 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6642082 : Nat := 118140960795 + 6642082 * 2 ^ 59
def prefixEnd_6642082 : Nat := 4983230072969 + 3 ^ 40 * 6642082 * 2
def baseEnd_6642082 : Nat := 3410580612576787057328627

theorem tailTrace_6642082 : CollatzResearch.WordTrace tailWord_6642082 prefixEnd_6642082 3410580612576787057328627 := by
  unfold tailWord_6642082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60564158180719691534580125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161504421815252510758880333 60564158180719691534580125)
  ·
    refine ⟨22711559317769884325467547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60564158180719691534580125 22711559317769884325467547)
    ·
      refine ⟨34067338976654826488201321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22711559317769884325467547 34067338976654826488201321)
      ·
        refine ⟨25550504232491119866150991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34067338976654826488201321 25550504232491119866150991)
        ·
          refine ⟨38325756348736679799226487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25550504232491119866150991 38325756348736679799226487)
          ·
            refine ⟨57488634523105019698839731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38325756348736679799226487 57488634523105019698839731)
            ·
              refine ⟨86232951784657529548259597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57488634523105019698839731 86232951784657529548259597)
              ·
                refine ⟨32337356919246573580597349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86232951784657529548259597 32337356919246573580597349)
                ·
                  refine ⟨6063254422358732546362003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32337356919246573580597349 6063254422358732546362003)
                  ·
                    refine ⟨9094881633538098819543005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6063254422358732546362003 9094881633538098819543005)
                    ·
                      refine ⟨3410580612576787057328627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094881633538098819543005 3410580612576787057328627)
                      ·
                        rfl

theorem cell23_6642082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6642082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642082 prefixEnd_6642082 := by exact prefixLift 6642082
  have htrace : WordTrace (prefixWord ++ tailWord_6642082) baseStart_6642082 baseEnd_6642082 := by
    simpa [prefixWord, tailWord_6642082, baseEnd_6642082] using wordTrace_append hprefix tailTrace_6642082
  have hstable : (prefixWord ++ tailWord_6642082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642082).length < 2 ^ (prefixWord ++ tailWord_6642082).sum := by decide
  have hdescent : baseEnd_6642082 < baseStart_6642082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642093 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6642093 : Nat := 118140960795 + 6642093 * 2 ^ 59
def prefixEnd_6642093 : Nat := 4983230072969 + 3 ^ 40 * 6642093 * 2
def baseEnd_6642093 : Nat := 1136862086954662171430359

theorem tailTrace_6642093 : CollatzResearch.WordTrace tailWord_6642093 prefixEnd_6642093 1136862086954662171430359 := by
  unfold tailWord_6642093
  simp only [CollatzResearch.WordTrace]
  refine ⟨242257033925838915016970933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161504689283892610011313955 242257033925838915016970933)
  ·
    refine ⟨22711596930547398282841025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242257033925838915016970933 22711596930547398282841025)
    ·
      refine ⟨17033697697910548712130769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22711596930547398282841025 17033697697910548712130769)
      ·
        refine ⟨12775273273432911534098077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17033697697910548712130769 12775273273432911534098077)
        ·
          refine ⟨4790727477537341825286779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12775273273432911534098077 4790727477537341825286779)
          ·
            refine ⟨7186091216306012737930169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790727477537341825286779 7186091216306012737930169)
            ·
              refine ⟨5389568412229509553447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7186091216306012737930169 5389568412229509553447627)
              ·
                refine ⟨8084352618344264330171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389568412229509553447627 8084352618344264330171441)
                ·
                  refine ⟨6063264463758198247628581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8084352618344264330171441 6063264463758198247628581)
                  ·
                    refine ⟨1136862086954662171430359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6063264463758198247628581 1136862086954662171430359)
                    ·
                      rfl

theorem cell23_6642093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6642093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642093 prefixEnd_6642093 := by exact prefixLift 6642093
  have htrace : WordTrace (prefixWord ++ tailWord_6642093) baseStart_6642093 baseEnd_6642093 := by
    simpa [prefixWord, tailWord_6642093, baseEnd_6642093] using wordTrace_append hprefix tailTrace_6642093
  have hstable : (prefixWord ++ tailWord_6642093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642093).length < 2 ^ (prefixWord ++ tailWord_6642093).sum := by decide
  have hdescent : baseEnd_6642093 < baseStart_6642093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642098 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_6642098 : Nat := 118140960795 + 6642098 * 2 ^ 59
def prefixEnd_6642098 : Nat := 4983230072969 + 3 ^ 40 * 6642098 * 2
def baseEnd_6642098 : Nat := 1136862942755752998242851

theorem tailTrace_6642098 : CollatzResearch.WordTrace tailWord_6642098 prefixEnd_6642098 1136862942755752998242851 := by
  unfold tailWord_6642098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60564304072705200217725737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161504810860547200580601965 60564304072705200217725737)
  ·
    refine ⟨45423228054528900163294303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60564304072705200217725737 45423228054528900163294303)
    ·
      refine ⟨68134842081793350244941455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423228054528900163294303 68134842081793350244941455)
      ·
        refine ⟨102202263122690025367412183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68134842081793350244941455 102202263122690025367412183)
        ·
          refine ⟨153303394684035038051118275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102202263122690025367412183 153303394684035038051118275)
          ·
            refine ⟨229955092026052557076677413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153303394684035038051118275 229955092026052557076677413)
            ·
              refine ⟨43116579754884854451877015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229955092026052557076677413 43116579754884854451877015)
              ·
                refine ⟨64674869632327281677815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43116579754884854451877015 64674869632327281677815523)
                ·
                  refine ⟨97012304448490922516723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64674869632327281677815523 97012304448490922516723285)
                  ·
                    refine ⟨1136862942755752998242851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97012304448490922516723285 1136862942755752998242851)
                    ·
                      rfl

theorem cell23_6642098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_6642098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642098 prefixEnd_6642098 := by exact prefixLift 6642098
  have htrace : WordTrace (prefixWord ++ tailWord_6642098) baseStart_6642098 baseEnd_6642098 := by
    simpa [prefixWord, tailWord_6642098, baseEnd_6642098] using wordTrace_append hprefix tailTrace_6642098
  have hstable : (prefixWord ++ tailWord_6642098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642098).length < 2 ^ (prefixWord ++ tailWord_6642098).sum := by decide
  have hdescent : baseEnd_6642098 < baseStart_6642098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642109 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6642109 : Nat := 118140960795 + 6642109 * 2 ^ 59
def prefixEnd_6642109 : Nat := 4983230072969 + 3 ^ 40 * 6642109 * 2
def baseEnd_6642109 : Nat := 3410594476554458451691003

theorem tailTrace_6642109 : CollatzResearch.WordTrace tailWord_6642109 prefixEnd_6642109 3410594476554458451691003 := by
  unfold tailWord_6642109
  simp only [CollatzResearch.WordTrace]
  refine ⟨242257617493780949749553381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161505078329187299833035587 242257617493780949749553381)
  ·
    refine ⟨45423303280083928078041259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242257617493780949749553381 45423303280083928078041259)
    ·
      refine ⟨68134954920125892117061889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423303280083928078041259 68134954920125892117061889)
      ·
        refine ⟨51101216190094419087796417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68134954920125892117061889 51101216190094419087796417)
        ·
          refine ⟨38325912142570814315847313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51101216190094419087796417 38325912142570814315847313)
          ·
            refine ⟨28744434106928110736885485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38325912142570814315847313 28744434106928110736885485)
            ·
              refine ⟨10779162790098041526332057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28744434106928110736885485 10779162790098041526332057)
              ·
                refine ⟨8084372092573531144749043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10779162790098041526332057 8084372092573531144749043)
                ·
                  refine ⟨12126558138860296717123565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8084372092573531144749043 12126558138860296717123565)
                  ·
                    refine ⟨4547459302072611268921337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12126558138860296717123565 4547459302072611268921337)
                    ·
                      refine ⟨3410594476554458451691003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547459302072611268921337 3410594476554458451691003)
                      ·
                        rfl

theorem cell23_6642109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6642109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642109 prefixEnd_6642109 := by exact prefixLift 6642109
  have htrace : WordTrace (prefixWord ++ tailWord_6642109) baseStart_6642109 baseEnd_6642109 := by
    simpa [prefixWord, tailWord_6642109, baseEnd_6642109] using wordTrace_append hprefix tailTrace_6642109
  have hstable : (prefixWord ++ tailWord_6642109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642109).length < 2 ^ (prefixWord ++ tailWord_6642109).sum := by decide
  have hdescent : baseEnd_6642109 < baseStart_6642109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642122 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_6642122 : Nat := 118140960795 + 6642122 * 2 ^ 59
def prefixEnd_6642122 : Nat := 4983230072969 + 3 ^ 40 * 6642122 * 2
def baseEnd_6642122 : Nat := 3410601151802966900828443

theorem tailTrace_6642122 : CollatzResearch.WordTrace tailWord_6642122 prefixEnd_6642122 3410601151802966900828443 := by
  unfold tailWord_6642122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60564522910683463242444155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161505394428489235313184413 60564522910683463242444155)
  ·
    refine ⟨90846784366025194863666233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60564522910683463242444155 90846784366025194863666233)
    ·
      refine ⟨68135088274518896147749675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90846784366025194863666233 68135088274518896147749675)
      ·
        refine ⟨102202632411778344221624513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68135088274518896147749675 102202632411778344221624513)
        ·
          refine ⟨76651974308833758166218385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102202632411778344221624513 76651974308833758166218385)
          ·
            refine ⟨57488980731625318624663789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76651974308833758166218385 57488980731625318624663789)
            ·
              refine ⟨21558367774359494484248921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57488980731625318624663789 21558367774359494484248921)
              ·
                refine ⟨16168775830769620863186691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21558367774359494484248921 16168775830769620863186691)
                ·
                  refine ⟨24253163746154431294780037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16168775830769620863186691 24253163746154431294780037)
                  ·
                    refine ⟨4547468202403955867771257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24253163746154431294780037 4547468202403955867771257)
                    ·
                      refine ⟨3410601151802966900828443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547468202403955867771257 3410601151802966900828443)
                      ·
                        rfl

theorem cell23_6642122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_6642122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642122 prefixEnd_6642122 := by exact prefixLift 6642122
  have htrace : WordTrace (prefixWord ++ tailWord_6642122) baseStart_6642122 baseEnd_6642122 := by
    simpa [prefixWord, tailWord_6642122, baseEnd_6642122] using wordTrace_append hprefix tailTrace_6642122
  have hstable : (prefixWord ++ tailWord_6642122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642122).length < 2 ^ (prefixWord ++ tailWord_6642122).sum := by decide
  have hdescent : baseEnd_6642122 < baseStart_6642122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642148 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_6642148 : Nat := 118140960795 + 6642148 * 2 ^ 59
def prefixEnd_6642148 : Nat := 4983230072969 + 3 ^ 40 * 6642148 * 2
def baseEnd_6642148 : Nat := 3410614502299983799103323

theorem tailTrace_6642148 : CollatzResearch.WordTrace tailWord_6642148 prefixEnd_6642148 3410614502299983799103323 := by
  unfold tailWord_6642148
  simp only [CollatzResearch.WordTrace]
  refine ⟨121129519970319829705111549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161506026627093106273482065 121129519970319829705111549)
  ·
    refine ⟨45423569988869936139416831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121129519970319829705111549 45423569988869936139416831)
    ·
      refine ⟨68135354983304904209125247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423569988869936139416831 68135354983304904209125247)
      ·
        refine ⟨102203032474957356313687871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68135354983304904209125247 102203032474957356313687871)
        ·
          refine ⟨153304548712436034470531807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102203032474957356313687871 153304548712436034470531807)
          ·
            refine ⟨229956823068654051705797711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153304548712436034470531807 229956823068654051705797711)
            ·
              refine ⟨344935234602981077558696567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229956823068654051705797711 344935234602981077558696567)
              ·
                refine ⟨517402851904471616338044851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344935234602981077558696567 517402851904471616338044851)
                ·
                  refine ⟨776104277856707424507067277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517402851904471616338044851 776104277856707424507067277)
                  ·
                    refine ⟨291039104196265284190150229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776104277856707424507067277 291039104196265284190150229)
                    ·
                      refine ⟨3410614502299983799103323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291039104196265284190150229 3410614502299983799103323)
                      ·
                        rfl

theorem cell23_6642148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_6642148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642148 prefixEnd_6642148 := by exact prefixLift 6642148
  have htrace : WordTrace (prefixWord ++ tailWord_6642148) baseStart_6642148 baseEnd_6642148 := by
    simpa [prefixWord, tailWord_6642148, baseEnd_6642148] using wordTrace_append hprefix tailTrace_6642148
  have hstable : (prefixWord ++ tailWord_6642148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642148).length < 2 ^ (prefixWord ++ tailWord_6642148).sum := by decide
  have hdescent : baseEnd_6642148 < baseStart_6642148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642155 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3]
def baseStart_6642155 : Nat := 118140960795 + 6642155 * 2 ^ 59
def prefixEnd_6642155 : Nat := 4983230072969 + 3 ^ 40 * 6642155 * 2
def baseEnd_6642155 : Nat := 3410618096664565271715791

theorem tailTrace_6642155 : CollatzResearch.WordTrace tailWord_6642155 prefixEnd_6642155 3410618096664565271715791 := by
  unfold tailWord_6642155
  simp only [CollatzResearch.WordTrace]
  refine ⟨242259295251614299605727919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161506196834409533070485279 242259295251614299605727919)
  ·
    refine ⟨363388942877421449408591879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242259295251614299605727919 363388942877421449408591879)
    ·
      refine ⟨545083414316132174112887819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363388942877421449408591879 545083414316132174112887819)
      ·
        refine ⟨817625121474198261169331729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545083414316132174112887819 817625121474198261169331729)
        ·
          refine ⟨613218841105648695876998797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817625121474198261169331729 613218841105648695876998797)
          ·
            refine ⟨229957065414618260953874549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613218841105648695876998797 229957065414618260953874549)
            ·
              refine ⟨21558474882620461964425739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229957065414618260953874549 21558474882620461964425739)
              ·
                refine ⟨32337712323930692946638609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21558474882620461964425739 32337712323930692946638609)
                ·
                  refine ⟨24253284242948019709978957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32337712323930692946638609 24253284242948019709978957)
                  ·
                    refine ⟨9094981591105507391242109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24253284242948019709978957 9094981591105507391242109)
                    ·
                      refine ⟨3410618096664565271715791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9094981591105507391242109 3410618096664565271715791)
                      ·
                        rfl

theorem cell23_6642155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 3].length) (baseStart_6642155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642155 prefixEnd_6642155 := by exact prefixLift 6642155
  have htrace : WordTrace (prefixWord ++ tailWord_6642155) baseStart_6642155 baseEnd_6642155 := by
    simpa [prefixWord, tailWord_6642155, baseEnd_6642155] using wordTrace_append hprefix tailTrace_6642155
  have hstable : (prefixWord ++ tailWord_6642155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642155).length < 2 ^ (prefixWord ++ tailWord_6642155).sum := by decide
  have hdescent : baseEnd_6642155 < baseStart_6642155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642162 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_6642162 : Nat := 118140960795 + 6642162 * 2 ^ 59
def prefixEnd_6642162 : Nat := 4983230072969 + 3 ^ 40 * 6642162 * 2
def baseEnd_6642162 : Nat := 378957965669905193814251

theorem tailTrace_6642162 : CollatzResearch.WordTrace tailWord_6642162 prefixEnd_6642162 378957965669905193814251 := by
  unfold tailWord_6642162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60564887640647234950308185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161506367041725959867488493 60564887640647234950308185)
  ·
    refine ⟨45423665730485426212731139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60564887640647234950308185 45423665730485426212731139)
    ·
      refine ⟨68135498595728139319096709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423665730485426212731139 68135498595728139319096709)
      ·
        refine ⟨12775405986699026122330633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68135498595728139319096709 12775405986699026122330633)
        ·
          refine ⟨9581554490024269591747975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12775405986699026122330633 9581554490024269591747975)
          ·
            refine ⟨14372331735036404387621963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9581554490024269591747975 14372331735036404387621963)
            ·
              refine ⟨21558497602554606581432945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14372331735036404387621963 21558497602554606581432945)
              ·
                refine ⟨16168873201915954936074709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21558497602554606581432945 16168873201915954936074709)
                ·
                  refine ⟨378957965669905193814251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16168873201915954936074709 378957965669905193814251)
                  ·
                    rfl

theorem cell23_6642162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_6642162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642162 prefixEnd_6642162 := by exact prefixLift 6642162
  have htrace : WordTrace (prefixWord ++ tailWord_6642162) baseStart_6642162 baseEnd_6642162 := by
    simpa [prefixWord, tailWord_6642162, baseEnd_6642162] using wordTrace_append hprefix tailTrace_6642162
  have hstable : (prefixWord ++ tailWord_6642162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642162).length < 2 ^ (prefixWord ++ tailWord_6642162).sum := by decide
  have hdescent : baseEnd_6642162 < baseStart_6642162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642195 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4]
def baseStart_6642195 : Nat := 118140960795 + 6642195 * 2 ^ 59
def prefixEnd_6642195 : Nat := 4983230072969 + 3 ^ 40 * 6642195 * 2
def baseEnd_6642195 : Nat := 3410638635890745115215607

theorem tailTrace_6642195 : CollatzResearch.WordTrace tailWord_6642195 prefixEnd_6642195 3410638635890745115215607 := by
  unfold tailWord_6642195
  simp only [CollatzResearch.WordTrace]
  refine ⟨242260754171469386437184039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161507169447646257624789359 242260754171469386437184039)
  ·
    refine ⟨363391131257204079655776059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242260754171469386437184039 363391131257204079655776059)
    ·
      refine ⟨545086696885806119483664089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363391131257204079655776059 545086696885806119483664089)
      ·
        refine ⟨408815022664354589612748067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545086696885806119483664089 408815022664354589612748067)
        ·
          refine ⟨613222533996531884419122101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408815022664354589612748067 613222533996531884419122101)
          ·
            refine ⟨57489612562174864164292697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613222533996531884419122101 57489612562174864164292697)
            ·
              refine ⟨43117209421631148123219523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57489612562174864164292697 43117209421631148123219523)
              ·
                refine ⟨64675814132446722184829285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43117209421631148123219523 64675814132446722184829285)
                ·
                  refine ⟨12126715149833760409655491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64675814132446722184829285 12126715149833760409655491)
                  ·
                    refine ⟨18190072724750640614483237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12126715149833760409655491 18190072724750640614483237)
                    ·
                      refine ⟨3410638635890745115215607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18190072724750640614483237 3410638635890745115215607)
                      ·
                        rfl

theorem cell23_6642195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_6642195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642195 prefixEnd_6642195 := by exact prefixLift 6642195
  have htrace : WordTrace (prefixWord ++ tailWord_6642195) baseStart_6642195 baseEnd_6642195 := by
    simpa [prefixWord, tailWord_6642195, baseEnd_6642195] using wordTrace_append hprefix tailTrace_6642195
  have hstable : (prefixWord ++ tailWord_6642195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642195).length < 2 ^ (prefixWord ++ tailWord_6642195).sum := by decide
  have hdescent : baseEnd_6642195 < baseStart_6642195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642232 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_6642232 : Nat := 118140960795 + 6642232 * 2 ^ 59
def prefixEnd_6642232 : Nat := 4983230072969 + 3 ^ 40 * 6642232 * 2
def baseEnd_6642232 : Nat := 3410657634674961470452937

theorem tailTrace_6642232 : CollatzResearch.WordTrace tailWord_6642232 prefixEnd_6642232 3410657634674961470452937 := by
  unfold tailWord_6642232
  simp only [CollatzResearch.WordTrace]
  refine ⟨121131051836167670878140475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161508069114890227837520633 121131051836167670878140475)
  ·
    refine ⟨181696577754251506317210713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121131051836167670878140475 181696577754251506317210713)
    ·
      refine ⟨136272433315688629737908035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181696577754251506317210713 136272433315688629737908035)
      ·
        refine ⟨204408649973532944606862053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136272433315688629737908035 204408649973532944606862053)
        ·
          refine ⟨38326621870037427113786635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204408649973532944606862053 38326621870037427113786635)
          ·
            refine ⟨57489932805056140670679953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38326621870037427113786635 57489932805056140670679953)
            ·
              refine ⟨43117449603792105503009965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57489932805056140670679953 43117449603792105503009965)
              ·
                refine ⟨16169043601422039563628737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43117449603792105503009965 16169043601422039563628737)
                ·
                  refine ⟨12126782701066529672721553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16169043601422039563628737 12126782701066529672721553)
                  ·
                    refine ⟨9095087025799897254541165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12126782701066529672721553 9095087025799897254541165)
                    ·
                      refine ⟨3410657634674961470452937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9095087025799897254541165 3410657634674961470452937)
                      ·
                        rfl

theorem cell23_6642232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_6642232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642232 prefixEnd_6642232 := by exact prefixLift 6642232
  have htrace : WordTrace (prefixWord ++ tailWord_6642232) baseStart_6642232 baseEnd_6642232 := by
    simpa [prefixWord, tailWord_6642232, baseEnd_6642232] using wordTrace_append hprefix tailTrace_6642232
  have hstable : (prefixWord ++ tailWord_6642232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642232).length < 2 ^ (prefixWord ++ tailWord_6642232).sum := by decide
  have hdescent : baseEnd_6642232 < baseStart_6642232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642246 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6642246 : Nat := 118140960795 + 6642246 * 2 ^ 59
def prefixEnd_6642246 : Nat := 4983230072969 + 3 ^ 40 * 6642246 * 2
def baseEnd_6642246 : Nat := 3410664823404124415677873

theorem tailTrace_6642246 : CollatzResearch.WordTrace tailWord_6642246 prefixEnd_6642246 3410664823404124415677873 := by
  unfold tailWord_6642246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570706696696394442102831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161508409529523081431527061 7570706696696394442102831)
  ·
    refine ⟨11356060045044591663154247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7570706696696394442102831 11356060045044591663154247)
    ·
      refine ⟨17034090067566887494731371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11356060045044591663154247 17034090067566887494731371)
      ·
        refine ⟨25551135101350331242097057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17034090067566887494731371 25551135101350331242097057)
        ·
          refine ⟨19163351326012748431572793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25551135101350331242097057 19163351326012748431572793)
          ·
            refine ⟨14372513494509561323679595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19163351326012748431572793 14372513494509561323679595)
            ·
              refine ⟨21558770241764341985519393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14372513494509561323679595 21558770241764341985519393)
              ·
                refine ⟨16169077681323256489139545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21558770241764341985519393 16169077681323256489139545)
                ·
                  refine ⟨12126808260992442366854659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16169077681323256489139545 12126808260992442366854659)
                  ·
                    refine ⟨18190212391488663550281989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12126808260992442366854659 18190212391488663550281989)
                    ·
                      refine ⟨3410664823404124415677873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18190212391488663550281989 3410664823404124415677873)
                      ·
                        rfl

theorem cell23_6642246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6642246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642246 prefixEnd_6642246 := by exact prefixLift 6642246
  have htrace : WordTrace (prefixWord ++ tailWord_6642246) baseStart_6642246 baseEnd_6642246 := by
    simpa [prefixWord, tailWord_6642246, baseEnd_6642246] using wordTrace_append hprefix tailTrace_6642246
  have hstable : (prefixWord ++ tailWord_6642246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642246).length < 2 ^ (prefixWord ++ tailWord_6642246).sum := by decide
  have hdescent : baseEnd_6642246 < baseStart_6642246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642272 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2]
def baseStart_6642272 : Nat := 118140960795 + 6642272 * 2 ^ 59
def prefixEnd_6642272 : Nat := 4983230072969 + 3 ^ 40 * 6642272 * 2
def baseEnd_6642272 : Nat := 3410678173901141313952753

theorem tailTrace_6642272 : CollatzResearch.WordTrace tailWord_6642272 prefixEnd_6642272 3410678173901141313952753 := by
  unfold tailWord_6642272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121131781296095214293868535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161509041728126952391824713 121131781296095214293868535)
  ·
    refine ⟨181697671944142821440802803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121131781296095214293868535 181697671944142821440802803)
    ·
      refine ⟨272546507916214232161204205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181697671944142821440802803 272546507916214232161204205)
      ·
        refine ⟨102204940468580337060451577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272546507916214232161204205 102204940468580337060451577)
        ·
          refine ⟨76653705351435252795338683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102204940468580337060451577 76653705351435252795338683)
          ·
            refine ⟨114980558027152879193008025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76653705351435252795338683 114980558027152879193008025)
            ·
              refine ⟨86235418520364659394756019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114980558027152879193008025 86235418520364659394756019)
              ·
                refine ⟨129353127780546989092134029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86235418520364659394756019 129353127780546989092134029)
                ·
                  refine ⟨48507422917705120909550261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129353127780546989092134029 48507422917705120909550261)
                  ·
                    refine ⟨4547570898534855085270337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48507422917705120909550261 4547570898534855085270337)
                    ·
                      refine ⟨3410678173901141313952753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547570898534855085270337 3410678173901141313952753)
                      ·
                        rfl

theorem cell23_6642272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_6642272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642272 prefixEnd_6642272 := by exact prefixLift 6642272
  have htrace : WordTrace (prefixWord ++ tailWord_6642272) baseStart_6642272 baseEnd_6642272 := by
    simpa [prefixWord, tailWord_6642272, baseEnd_6642272] using wordTrace_append hprefix tailTrace_6642272
  have hstable : (prefixWord ++ tailWord_6642272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642272).length < 2 ^ (prefixWord ++ tailWord_6642272).sum := by decide
  have hdescent : baseEnd_6642272 < baseStart_6642272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642282 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_6642282 : Nat := 118140960795 + 6642282 * 2 ^ 59
def prefixEnd_6642282 : Nat := 4983230072969 + 3 ^ 40 * 6642282 * 2
def baseEnd_6642282 : Nat := 1136894436235895424942569

theorem tailTrace_6642282 : CollatzResearch.WordTrace tailWord_6642282 prefixEnd_6642282 1136894436235895424942569 := by
  unfold tailWord_6642282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60565981830538550073900275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161509284881436133530400733 60565981830538550073900275)
  ·
    refine ⟨90848972745807825110850413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60565981830538550073900275 90848972745807825110850413)
    ·
      refine ⟨34068364779677934416568905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90848972745807825110850413 34068364779677934416568905)
      ·
        refine ⟨25551273584758450812426679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34068364779677934416568905 25551273584758450812426679)
        ·
          refine ⟨38326910377137676218640019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25551273584758450812426679 38326910377137676218640019)
          ·
            refine ⟨57490365565706514327960029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38326910377137676218640019 57490365565706514327960029)
            ·
              refine ⟨21558887087139942872985011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57490365565706514327960029 21558887087139942872985011)
              ·
                refine ⟨32338330630709914309477517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21558887087139942872985011 32338330630709914309477517)
                ·
                  refine ⟨12126873986516217866054069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32338330630709914309477517 12126873986516217866054069)
                  ·
                    refine ⟨1136894436235895424942569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12126873986516217866054069 1136894436235895424942569)
                    ·
                      rfl

theorem cell23_6642282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_6642282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642282 prefixEnd_6642282 := by exact prefixLift 6642282
  have htrace : WordTrace (prefixWord ++ tailWord_6642282) baseStart_6642282 baseEnd_6642282 := by
    simpa [prefixWord, tailWord_6642282, baseEnd_6642282] using wordTrace_append hprefix tailTrace_6642282
  have hstable : (prefixWord ++ tailWord_6642282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642282).length < 2 ^ (prefixWord ++ tailWord_6642282).sum := by decide
  have hdescent : baseEnd_6642282 < baseStart_6642282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642295 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 3, 6]
def baseStart_6642295 : Nat := 118140960795 + 6642295 * 2 ^ 59
def prefixEnd_6642295 : Nat := 4983230072969 + 3 ^ 40 * 6642295 * 2
def baseEnd_6642295 : Nat := 1136896661318731574655049

theorem tailTrace_6642295 : CollatzResearch.WordTrace tailWord_6642295 prefixEnd_6642295 1136896661318731574655049 := by
  unfold tailWord_6642295
  simp only [CollatzResearch.WordTrace]
  refine ⟨242264401471107103515824339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161509600980738069010549559 242264401471107103515824339)
  ·
    refine ⟨363396602206660655273736509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242264401471107103515824339 363396602206660655273736509)
    ·
      refine ⟨136273725827497745727651191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363396602206660655273736509 136273725827497745727651191)
      ·
        refine ⟨204410588741246618591476787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136273725827497745727651191 204410588741246618591476787)
        ·
          refine ⟨306615883111869927887215181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204410588741246618591476787 306615883111869927887215181)
          ·
            refine ⟨114980956166951222957705693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306615883111869927887215181 114980956166951222957705693)
            ·
              refine ⟨43117858562606708609139635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114980956166951222957705693 43117858562606708609139635)
              ·
                refine ⟨64676787843910062913709453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43117858562606708609139635 64676787843910062913709453)
                ·
                  refine ⟨24253795441466273592641045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64676787843910062913709453 24253795441466273592641045)
                  ·
                    refine ⟨1136896661318731574655049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24253795441466273592641045 1136896661318731574655049)
                    ·
                      rfl

theorem cell23_6642295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_6642295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642295 prefixEnd_6642295 := by exact prefixLift 6642295
  have htrace : WordTrace (prefixWord ++ tailWord_6642295) baseStart_6642295 baseEnd_6642295 := by
    simpa [prefixWord, tailWord_6642295, baseEnd_6642295] using wordTrace_append hprefix tailTrace_6642295
  have hstable : (prefixWord ++ tailWord_6642295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642295).length < 2 ^ (prefixWord ++ tailWord_6642295).sum := by decide
  have hdescent : baseEnd_6642295 < baseStart_6642295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642315 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_6642315 : Nat := 118140960795 + 6642315 * 2 ^ 59
def prefixEnd_6642315 : Nat := 4983230072969 + 3 ^ 40 * 6642315 * 2
def baseEnd_6642315 : Nat := 3410700253569284645715055

theorem tailTrace_6642315 : CollatzResearch.WordTrace tailWord_6642315 prefixEnd_6642315 3410700253569284645715055 := by
  unfold tailWord_6642315
  simp only [CollatzResearch.WordTrace]
  refine ⟨242265130931034646931552399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161510087287356431287701599 242265130931034646931552399)
  ·
    refine ⟨363397696396551970397328599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242265130931034646931552399 363397696396551970397328599)
    ·
      refine ⟨545096544594827955595992899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363397696396551970397328599 545096544594827955595992899)
      ·
        refine ⟨817644816892241933393989349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545096544594827955595992899 817644816892241933393989349)
        ·
          refine ⟨153308403167295362511373003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 817644816892241933393989349 153308403167295362511373003)
          ·
            refine ⟨229962604750943043767059505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153308403167295362511373003 229962604750943043767059505)
            ·
              refine ⟨172471953563207282825294629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229962604750943043767059505 172471953563207282825294629)
              ·
                refine ⟨32338491293101365529742743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172471953563207282825294629 32338491293101365529742743)
                ·
                  refine ⟨48507736939652048294614115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32338491293101365529742743 48507736939652048294614115)
                  ·
                    refine ⟨72761605409478072441921173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48507736939652048294614115 72761605409478072441921173)
                    ·
                      refine ⟨3410700253569284645715055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72761605409478072441921173 3410700253569284645715055)
                      ·
                        rfl

theorem cell23_6642315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_6642315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642315 prefixEnd_6642315 := by exact prefixLift 6642315
  have htrace : WordTrace (prefixWord ++ tailWord_6642315) baseStart_6642315 baseEnd_6642315 := by
    simpa [prefixWord, tailWord_6642315, baseEnd_6642315] using wordTrace_append hprefix tailTrace_6642315
  have hstable : (prefixWord ++ tailWord_6642315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642315).length < 2 ^ (prefixWord ++ tailWord_6642315).sum := by decide
  have hdescent : baseEnd_6642315 < baseStart_6642315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642349 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6642349 : Nat := 118140960795 + 6642349 * 2 ^ 59
def prefixEnd_6642349 : Nat := 4983230072969 + 3 ^ 40 * 6642349 * 2
def baseEnd_6642349 : Nat := 3410717711911537512689899

theorem tailTrace_6642349 : CollatzResearch.WordTrace tailWord_6642349 prefixEnd_6642349 3410717711911537512689899 := by
  unfold tailWord_6642349
  simp only [CollatzResearch.WordTrace]
  refine ⟨242266371012911470738290101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161510914008607647158860067 242266371012911470738290101)
  ·
    refine ⟨22712472282460450381714697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242266371012911470738290101 22712472282460450381714697)
    ·
      refine ⟨17034354211845337786286023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22712472282460450381714697 17034354211845337786286023)
      ·
        refine ⟨25551531317768006679429035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17034354211845337786286023 25551531317768006679429035)
        ·
          refine ⟨38327296976652010019143553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25551531317768006679429035 38327296976652010019143553)
          ·
            refine ⟨28745472732489007514357665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38327296976652010019143553 28745472732489007514357665)
            ·
              refine ⟨21559104549366755635768249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28745472732489007514357665 21559104549366755635768249)
              ·
                refine ⟨16169328412025066726826187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21559104549366755635768249 16169328412025066726826187)
                ·
                  refine ⟨24253992618037600090239281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16169328412025066726826187 24253992618037600090239281)
                  ·
                    refine ⟨18190494463528200067679461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24253992618037600090239281 18190494463528200067679461)
                    ·
                      refine ⟨3410717711911537512689899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18190494463528200067679461 3410717711911537512689899)
                      ·
                        rfl

theorem cell23_6642349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6642349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642349 prefixEnd_6642349 := by exact prefixLift 6642349
  have htrace : WordTrace (prefixWord ++ tailWord_6642349) baseStart_6642349 baseEnd_6642349 := by
    simpa [prefixWord, tailWord_6642349, baseEnd_6642349] using wordTrace_append hprefix tailTrace_6642349
  have hstable : (prefixWord ++ tailWord_6642349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642349).length < 2 ^ (prefixWord ++ tailWord_6642349).sum := by decide
  have hdescent : baseEnd_6642349 < baseStart_6642349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_6642395 : Nat := 118140960795 + 6642395 * 2 ^ 59
def prefixEnd_6642395 : Nat := 4983230072969 + 3 ^ 40 * 6642395 * 2
def baseEnd_6642395 : Nat := 3410741332021644332714687

theorem tailTrace_6642395 : CollatzResearch.WordTrace tailWord_6642395 prefixEnd_6642395 3410741332021644332714687 := by
  unfold tailWord_6642395
  simp only [CollatzResearch.WordTrace]
  refine ⟨242268048770744820594464639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161512032513829880396309759 242268048770744820594464639)
  ·
    refine ⟨363402073156117230891696959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242268048770744820594464639 363402073156117230891696959)
    ·
      refine ⟨545103109734175846337545439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363402073156117230891696959 545103109734175846337545439)
      ·
        refine ⟨817654664601263769506318159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545103109734175846337545439 817654664601263769506318159)
        ·
          refine ⟨1226481996901895654259477239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817654664601263769506318159 1226481996901895654259477239)
          ·
            refine ⟨1839722995352843481389215859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226481996901895654259477239 1839722995352843481389215859)
            ·
              refine ⟨2759584493029265222083823789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839722995352843481389215859 2759584493029265222083823789)
              ·
                refine ⟨1034844184885974458281433921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759584493029265222083823789 1034844184885974458281433921)
                ·
                  refine ⟨776133138664480843711075441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1034844184885974458281433921 776133138664480843711075441)
                  ·
                    refine ⟨582099853998360632783306581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 776133138664480843711075441 582099853998360632783306581)
                    ·
                      refine ⟨3410741332021644332714687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 582099853998360632783306581 3410741332021644332714687)
                      ·
                        rfl

theorem cell23_6642395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_6642395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642395 prefixEnd_6642395 := by exact prefixLift 6642395
  have htrace : WordTrace (prefixWord ++ tailWord_6642395) baseStart_6642395 baseEnd_6642395 := by
    simpa [prefixWord, tailWord_6642395, baseEnd_6642395] using wordTrace_append hprefix tailTrace_6642395
  have hstable : (prefixWord ++ tailWord_6642395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642395).length < 2 ^ (prefixWord ++ tailWord_6642395).sum := by decide
  have hdescent : baseEnd_6642395 < baseStart_6642395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642409 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 1, 4, 2]
def baseStart_6642409 : Nat := 118140960795 + 6642409 * 2 ^ 59
def prefixEnd_6642409 : Nat := 4983230072969 + 3 ^ 40 * 6642409 * 2
def baseEnd_6642409 : Nat := 3410748520750807277939623

theorem tailTrace_6642409 : CollatzResearch.WordTrace tailWord_6642409 prefixEnd_6642409 3410748520750807277939623 := by
  unfold tailWord_6642409
  simp only [CollatzResearch.WordTrace]
  refine ⟨242268559392694100985474281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161512372928462733990316187 242268559392694100985474281)
  ·
    refine ⟨181701419544520575739105711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242268559392694100985474281 181701419544520575739105711)
    ·
      refine ⟨272552129316780863608658567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181701419544520575739105711 272552129316780863608658567)
      ·
        refine ⟨408828193975171295412987851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272552129316780863608658567 408828193975171295412987851)
        ·
          refine ⟨613242290962756943119481777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408828193975171295412987851 613242290962756943119481777)
          ·
            refine ⟨459931718222067707339611333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613242290962756943119481777 459931718222067707339611333)
            ·
              refine ⟨86237197166637695126177125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 459931718222067707339611333 86237197166637695126177125)
              ·
                refine ⟨16169474468744567836158211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86237197166637695126177125 16169474468744567836158211)
                ·
                  refine ⟨24254211703116851754237317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16169474468744567836158211 24254211703116851754237317)
                  ·
                    refine ⟨4547664694334409703919497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24254211703116851754237317 4547664694334409703919497)
                    ·
                      refine ⟨3410748520750807277939623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547664694334409703919497 3410748520750807277939623)
                      ·
                        rfl

theorem cell23_6642409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4, 2].length) (baseStart_6642409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642409 prefixEnd_6642409 := by exact prefixLift 6642409
  have htrace : WordTrace (prefixWord ++ tailWord_6642409) baseStart_6642409 baseEnd_6642409 := by
    simpa [prefixWord, tailWord_6642409, baseEnd_6642409] using wordTrace_append hprefix tailTrace_6642409
  have hstable : (prefixWord ++ tailWord_6642409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642409).length < 2 ^ (prefixWord ++ tailWord_6642409).sum := by decide
  have hdescent : baseEnd_6642409 < baseStart_6642409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642412 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_6642412 : Nat := 118140960795 + 6642412 * 2 ^ 59
def prefixEnd_6642412 : Nat := 4983230072969 + 3 ^ 40 * 6642412 * 2
def baseEnd_6642412 : Nat := 3410750061192770766202109

theorem tailTrace_6642412 : CollatzResearch.WordTrace tailWord_6642412 prefixEnd_6642412 3410750061192770766202109 := by
  unfold tailWord_6642412
  simp only [CollatzResearch.WordTrace]
  refine ⟨121134334405841616248916745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161512445874455488331888993 121134334405841616248916745)
  ·
    refine ⟨90850750804381212186687559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121134334405841616248916745 90850750804381212186687559)
    ·
      refine ⟨136276126206571818280031339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90850750804381212186687559 136276126206571818280031339)
      ·
        refine ⟨204414189309857727420047009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136276126206571818280031339 204414189309857727420047009)
        ·
          refine ⟨153310641982393295565035257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204414189309857727420047009 153310641982393295565035257)
          ·
            refine ⟨114982981486794971673776443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153310641982393295565035257 114982981486794971673776443)
            ·
              refine ⟨172474472230192457510664665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114982981486794971673776443 172474472230192457510664665)
              ·
                refine ⟨129355854172644343132998499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172474472230192457510664665 129355854172644343132998499)
                ·
                  refine ⟨194033781258966514699497749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129355854172644343132998499 194033781258966514699497749)
                  ·
                    refine ⟨9095333496514055376538957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194033781258966514699497749 9095333496514055376538957)
                    ·
                      refine ⟨3410750061192770766202109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9095333496514055376538957 3410750061192770766202109)
                      ·
                        rfl

theorem cell23_6642412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_6642412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642412 prefixEnd_6642412 := by exact prefixLift 6642412
  have htrace : WordTrace (prefixWord ++ tailWord_6642412) baseStart_6642412 baseEnd_6642412 := by
    simpa [prefixWord, tailWord_6642412, baseEnd_6642412] using wordTrace_append hprefix tailTrace_6642412
  have hstable : (prefixWord ++ tailWord_6642412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642412).length < 2 ^ (prefixWord ++ tailWord_6642412).sum := by decide
  have hdescent : baseEnd_6642412 < baseStart_6642412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642421 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6642421 : Nat := 118140960795 + 6642421 * 2 ^ 59
def prefixEnd_6642421 : Nat := 4983230072969 + 3 ^ 40 * 6642421 * 2
def baseEnd_6642421 : Nat := 3410754682518661230989569

theorem tailTrace_6642421 : CollatzResearch.WordTrace tailWord_6642421 prefixEnd_6642421 3410754682518661230989569 := by
  unfold tailWord_6642421
  simp only [CollatzResearch.WordTrace]
  refine ⟨242268997068650627034911117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161512664712433751356607411 242268997068650627034911117)
  ·
    refine ⟨90850873900743985138091669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242268997068650627034911117 90850873900743985138091669)
    ·
      refine ⟨4258634714097374303348047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90850873900743985138091669 4258634714097374303348047)
      ·
        refine ⟨6387952071146061455022071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258634714097374303348047 6387952071146061455022071)
        ·
          refine ⟨9581928106719092182533107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387952071146061455022071 9581928106719092182533107)
          ·
            refine ⟨14372892160078638273799661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9581928106719092182533107 14372892160078638273799661)
            ·
              refine ⟨5389834560029489352674873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14372892160078638273799661 5389834560029489352674873)
              ·
                refine ⟨4042375920022117014506155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389834560029489352674873 4042375920022117014506155)
                ·
                  refine ⟨6063563880033175521759233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042375920022117014506155 6063563880033175521759233)
                  ·
                    refine ⟨4547672910024881641319425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063563880033175521759233 4547672910024881641319425)
                    ·
                      refine ⟨3410754682518661230989569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547672910024881641319425 3410754682518661230989569)
                      ·
                        rfl

theorem cell23_6642421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6642421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642421 prefixEnd_6642421 := by exact prefixLift 6642421
  have htrace : WordTrace (prefixWord ++ tailWord_6642421) baseStart_6642421 baseEnd_6642421 := by
    simpa [prefixWord, tailWord_6642421, baseEnd_6642421] using wordTrace_append hprefix tailTrace_6642421
  have hstable : (prefixWord ++ tailWord_6642421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642421).length < 2 ^ (prefixWord ++ tailWord_6642421).sum := by decide
  have hdescent : baseEnd_6642421 < baseStart_6642421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642426 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_6642426 : Nat := 118140960795 + 6642426 * 2 ^ 59
def prefixEnd_6642426 : Nat := 4983230072969 + 3 ^ 40 * 6642426 * 2
def baseEnd_6642426 : Nat := 3410757249921933711427045

theorem tailTrace_6642426 : CollatzResearch.WordTrace tailWord_6642426 prefixEnd_6642426 3410757249921933711427045 := by
  unfold tailWord_6642426
  simp only [CollatzResearch.WordTrace]
  refine ⟨60567294858408128222210783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161512786289088341925895421 60567294858408128222210783)
  ·
    refine ⟨90850942287612192333316175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60567294858408128222210783 90850942287612192333316175)
    ·
      refine ⟨136276413431418288499974263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90850942287612192333316175 136276413431418288499974263)
      ·
        refine ⟨204414620147127432749961395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136276413431418288499974263 204414620147127432749961395)
        ·
          refine ⟨306621930220691149124942093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204414620147127432749961395 306621930220691149124942093)
          ·
            refine ⟨114983223832759180921853285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306621930220691149124942093 114983223832759180921853285)
            ·
              refine ⟨21559354468642346422847491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114983223832759180921853285 21559354468642346422847491)
              ·
                refine ⟨32339031702963519634271237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21559354468642346422847491 32339031702963519634271237)
                ·
                  refine ⟨6063568444305659931425857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32339031702963519634271237 6063568444305659931425857)
                  ·
                    refine ⟨4547676333229244948569393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063568444305659931425857 4547676333229244948569393)
                    ·
                      refine ⟨3410757249921933711427045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547676333229244948569393 3410757249921933711427045)
                      ·
                        rfl

theorem cell23_6642426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_6642426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642426 prefixEnd_6642426 := by exact prefixLift 6642426
  have htrace : WordTrace (prefixWord ++ tailWord_6642426) baseStart_6642426 baseEnd_6642426 := by
    simpa [prefixWord, tailWord_6642426, baseEnd_6642426] using wordTrace_append hprefix tailTrace_6642426
  have hstable : (prefixWord ++ tailWord_6642426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642426).length < 2 ^ (prefixWord ++ tailWord_6642426).sum := by decide
  have hdescent : baseEnd_6642426 < baseStart_6642426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642483 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 5]
def baseStart_6642483 : Nat := 118140960795 + 6642483 * 2 ^ 59
def prefixEnd_6642483 : Nat := 4983230072969 + 3 ^ 40 * 6642483 * 2
def baseEnd_6642483 : Nat := 378976279813248887601587

theorem tailTrace_6642483 : CollatzResearch.WordTrace tailWord_6642483 prefixEnd_6642483 378976279813248887601587 := by
  unfold tailWord_6642483
  simp only [CollatzResearch.WordTrace]
  refine ⟨242271258394426011623668103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161514172262950674415778735 242271258394426011623668103)
  ·
    refine ⟨363406887591639017435502155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242271258394426011623668103 363406887591639017435502155)
    ·
      refine ⟨545110331387458526153253233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363406887591639017435502155 545110331387458526153253233)
      ·
        refine ⟨408832748540593894614939925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545110331387458526153253233 408832748540593894614939925)
        ·
          refine ⟨19164035087840338810075309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 408832748540593894614939925 19164035087840338810075309)
          ·
            refine ⟨7186513157940127053778241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19164035087840338810075309 7186513157940127053778241)
            ·
              refine ⟨5389884868455095290333681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7186513157940127053778241 5389884868455095290333681)
              ·
                refine ⟨4042413651341321467750261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389884868455095290333681 4042413651341321467750261)
                ·
                  refine ⟨378976279813248887601587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042413651341321467750261 378976279813248887601587)
                  ·
                    rfl

theorem cell23_6642483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 5].length) (baseStart_6642483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642483 prefixEnd_6642483 := by exact prefixLift 6642483
  have htrace : WordTrace (prefixWord ++ tailWord_6642483) baseStart_6642483 baseEnd_6642483 := by
    simpa [prefixWord, tailWord_6642483, baseEnd_6642483] using wordTrace_append hprefix tailTrace_6642483
  have hstable : (prefixWord ++ tailWord_6642483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642483).length < 2 ^ (prefixWord ++ tailWord_6642483).sum := by decide
  have hdescent : baseEnd_6642483 < baseStart_6642483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642492 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_6642492 : Nat := 118140960795 + 6642492 * 2 ^ 59
def prefixEnd_6642492 : Nat := 4983230072969 + 3 ^ 40 * 6642492 * 2
def baseEnd_6642492 : Nat := 1136930379881710151067247

theorem tailTrace_6642492 : CollatzResearch.WordTrace tailWord_6642492 prefixEnd_6642492 1136930379881710151067247 := by
  unfold tailWord_6642492
  simp only [CollatzResearch.WordTrace]
  refine ⟨121135793325696703080372865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161514391100928937440497153 121135793325696703080372865)
  ·
    refine ⟨90851844994272527310279649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121135793325696703080372865 90851844994272527310279649)
    ·
      refine ⟨68138883745704395482709737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90851844994272527310279649 68138883745704395482709737)
      ·
        refine ⟨51104162809278296612032303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68138883745704395482709737 51104162809278296612032303)
        ·
          refine ⟨76656244213917444918048455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51104162809278296612032303 76656244213917444918048455)
          ·
            refine ⟨114984366320876167377072683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76656244213917444918048455 114984366320876167377072683)
            ·
              refine ⟨172476549481314251065609025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114984366320876167377072683 172476549481314251065609025)
              ·
                refine ⟨129357412110985688299206769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172476549481314251065609025 129357412110985688299206769)
                ·
                  refine ⟨97018059083239266224405077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129357412110985688299206769 97018059083239266224405077)
                  ·
                    refine ⟨1136930379881710151067247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97018059083239266224405077 1136930379881710151067247)
                    ·
                      rfl

theorem cell23_6642492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_6642492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642492 prefixEnd_6642492 := by exact prefixLift 6642492
  have htrace : WordTrace (prefixWord ++ tailWord_6642492) baseStart_6642492 baseEnd_6642492 := by
    simpa [prefixWord, tailWord_6642492, baseEnd_6642492] using wordTrace_append hprefix tailTrace_6642492
  have hstable : (prefixWord ++ tailWord_6642492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642492).length < 2 ^ (prefixWord ++ tailWord_6642492).sum := by decide
  have hdescent : baseEnd_6642492 < baseStart_6642492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642513 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 2, 5]
def baseStart_6642513 : Nat := 118140960795 + 6642513 * 2 ^ 59
def prefixEnd_6642513 : Nat := 4983230072969 + 3 ^ 40 * 6642513 * 2
def baseEnd_6642513 : Nat := 1136933974246291623679715

theorem tailTrace_6642513 : CollatzResearch.WordTrace tailWord_6642513 prefixEnd_6642513 1136933974246291623679715 := by
  unfold tailWord_6642513
  simp only [CollatzResearch.WordTrace]
  refine ⟨242272352584317326747260193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161514901722878217831506795 242272352584317326747260193)
  ·
    refine ⟨181704264438237995060445145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242272352584317326747260193 181704264438237995060445145)
    ·
      refine ⟨136278198328678496295333859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181704264438237995060445145 136278198328678496295333859)
      ·
        refine ⟨204417297493017744443000789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136278198328678496295333859 204417297493017744443000789)
        ·
          refine ⟨4791030409992603385382831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 204417297493017744443000789 4791030409992603385382831)
          ·
            refine ⟨7186545614988905078074247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791030409992603385382831 7186545614988905078074247)
            ·
              refine ⟨10779818422483357617111371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7186545614988905078074247 10779818422483357617111371)
              ·
                refine ⟨16169727633725036425667057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779818422483357617111371 16169727633725036425667057)
                ·
                  refine ⟨12127295725293777319250293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16169727633725036425667057 12127295725293777319250293)
                  ·
                    refine ⟨1136933974246291623679715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12127295725293777319250293 1136933974246291623679715)
                    ·
                      rfl

theorem cell23_6642513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_6642513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642513 prefixEnd_6642513 := by exact prefixLift 6642513
  have htrace : WordTrace (prefixWord ++ tailWord_6642513) baseStart_6642513 baseEnd_6642513 := by
    simpa [prefixWord, tailWord_6642513, baseEnd_6642513] using wordTrace_append hprefix tailTrace_6642513
  have hstable : (prefixWord ++ tailWord_6642513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642513).length < 2 ^ (prefixWord ++ tailWord_6642513).sum := by decide
  have hdescent : baseEnd_6642513 < baseStart_6642513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642516 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_6642516 : Nat := 118140960795 + 6642516 * 2 ^ 59
def prefixEnd_6642516 : Nat := 4983230072969 + 3 ^ 40 * 6642516 * 2
def baseEnd_6642516 : Nat := 3410803463180838359301631

theorem tailTrace_6642516 : CollatzResearch.WordTrace tailWord_6642516 prefixEnd_6642516 3410803463180838359301631 := by
  unfold tailWord_6642516
  simp only [CollatzResearch.WordTrace]
  refine ⟨121136231001653229129809701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161514974668870972173079601 121136231001653229129809701)
  ·
    refine ⟨22713043312809980461839319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121136231001653229129809701 22713043312809980461839319)
    ·
      refine ⟨34069564969214970692758979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22713043312809980461839319 34069564969214970692758979)
      ·
        refine ⟨51104347453822456039138469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34069564969214970692758979 51104347453822456039138469)
        ·
          refine ⟨9582065147591710507338463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51104347453822456039138469 9582065147591710507338463)
          ·
            refine ⟨14373097721387565761007695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582065147591710507338463 14373097721387565761007695)
            ·
              refine ⟨21559646582081348641511543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14373097721387565761007695 21559646582081348641511543)
              ·
                refine ⟨32339469873122022962267315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21559646582081348641511543 32339469873122022962267315)
                ·
                  refine ⟨48509204809683034443400973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32339469873122022962267315 48509204809683034443400973)
                  ·
                    refine ⟨18190951803631137916275365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48509204809683034443400973 18190951803631137916275365)
                    ·
                      refine ⟨3410803463180838359301631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18190951803631137916275365 3410803463180838359301631)
                      ·
                        rfl

theorem cell23_6642516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_6642516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642516 prefixEnd_6642516 := by exact prefixLift 6642516
  have htrace : WordTrace (prefixWord ++ tailWord_6642516) baseStart_6642516 baseEnd_6642516 := by
    simpa [prefixWord, tailWord_6642516, baseEnd_6642516] using wordTrace_append hprefix tailTrace_6642516
  have hstable : (prefixWord ++ tailWord_6642516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642516).length < 2 ^ (prefixWord ++ tailWord_6642516).sum := by decide
  have hdescent : baseEnd_6642516 < baseStart_6642516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642539 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 6]
def baseStart_6642539 : Nat := 118140960795 + 6642539 * 2 ^ 59
def prefixEnd_6642539 : Nat := 4983230072969 + 3 ^ 40 * 6642539 * 2
def baseEnd_6642539 : Nat := 378979474803987974368225

theorem tailTrace_6642539 : CollatzResearch.WordTrace tailWord_6642539 prefixEnd_6642539 378979474803987974368225 := by
  unfold tailWord_6642539
  simp only [CollatzResearch.WordTrace]
  refine ⟨242273300882223133187706671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161515533921482088791804447 242273300882223133187706671)
  ·
    refine ⟨363409951323334699781560007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242273300882223133187706671 363409951323334699781560007)
    ·
      refine ⟨545114926985002049672340011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363409951323334699781560007 545114926985002049672340011)
      ·
        refine ⟨817672390477503074508510017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545114926985002049672340011 817672390477503074508510017)
        ·
          refine ⟨613254292858127305881382513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817672390477503074508510017 613254292858127305881382513)
          ·
            refine ⟨459940719643595479411036885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613254292858127305881382513 459940719643595479411036885)
            ·
              refine ⟨10779860616646769048696177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 459940719643595479411036885 10779860616646769048696177)
              ·
                refine ⟨8084895462485076786522133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10779860616646769048696177 8084895462485076786522133)
                ·
                  refine ⟨378979474803987974368225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8084895462485076786522133 378979474803987974368225)
                  ·
                    rfl

theorem cell23_6642539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 6].length) (baseStart_6642539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642539 prefixEnd_6642539 := by exact prefixLift 6642539
  have htrace : WordTrace (prefixWord ++ tailWord_6642539) baseStart_6642539 baseEnd_6642539 := by
    simpa [prefixWord, tailWord_6642539, baseEnd_6642539] using wordTrace_append hprefix tailTrace_6642539
  have hstable : (prefixWord ++ tailWord_6642539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642539).length < 2 ^ (prefixWord ++ tailWord_6642539).sum := by decide
  have hdescent : baseEnd_6642539 < baseStart_6642539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642552 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_6642552 : Nat := 118140960795 + 6642552 * 2 ^ 59
def prefixEnd_6642552 : Nat := 4983230072969 + 3 ^ 40 * 6642552 * 2
def baseEnd_6642552 : Nat := 1136940649494800072817155

theorem tailTrace_6642552 : CollatzResearch.WordTrace tailWord_6642552 prefixEnd_6642552 1136940649494800072817155 := by
  unfold tailWord_6642552
  simp only [CollatzResearch.WordTrace]
  refine ⟨121136887515588018203964955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161515850020784024271953273 121136887515588018203964955)
  ·
    refine ⟨181705331273382027305947433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121136887515588018203964955 181705331273382027305947433)
    ·
      refine ⟨136278998455036520479460575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181705331273382027305947433 136278998455036520479460575)
      ·
        refine ⟨204418497682554780719190863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136278998455036520479460575 204418497682554780719190863)
        ·
          refine ⟨306627746523832171078786295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204418497682554780719190863 306627746523832171078786295)
          ·
            refine ⟨459941619785748256618179443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306627746523832171078786295 459941619785748256618179443)
            ·
              refine ⟨689912429678622384927269165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459941619785748256618179443 689912429678622384927269165)
              ·
                refine ⟨258717161129483394347725937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 689912429678622384927269165 258717161129483394347725937)
                ·
                  refine ⟨194037870847112545760794453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258717161129483394347725937 194037870847112545760794453)
                  ·
                    refine ⟨1136940649494800072817155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194037870847112545760794453 1136940649494800072817155)
                    ·
                      rfl

theorem cell23_6642552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_6642552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642552 prefixEnd_6642552 := by exact prefixLift 6642552
  have htrace : WordTrace (prefixWord ++ tailWord_6642552) baseStart_6642552 baseEnd_6642552 := by
    simpa [prefixWord, tailWord_6642552, baseEnd_6642552] using wordTrace_append hprefix tailTrace_6642552
  have hstable : (prefixWord ++ tailWord_6642552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642552).length < 2 ^ (prefixWord ++ tailWord_6642552).sum := by decide
  have hdescent : baseEnd_6642552 < baseStart_6642552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642593 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6642593 : Nat := 118140960795 + 6642593 * 2 ^ 59
def prefixEnd_6642593 : Nat := 4983230072969 + 3 ^ 40 * 6642593 * 2
def baseEnd_6642593 : Nat := 3410843001191234558038777

theorem tailTrace_6642593 : CollatzResearch.WordTrace tailWord_6642593 prefixEnd_6642593 3410843001191234558038777 := by
  unfold tailWord_6642593
  simp only [CollatzResearch.WordTrace]
  refine ⟨242275270424027500410172433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161516846949351666940114955 242275270424027500410172433)
  ·
    refine ⟨181706452818020625307629325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242275270424027500410172433 181706452818020625307629325)
    ·
      refine ⟨68139919806757734490360997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181706452818020625307629325 68139919806757734490360997)
      ·
        refine ⟨12776234963767075216942687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68139919806757734490360997 12776234963767075216942687)
        ·
          refine ⟨19164352445650612825414031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776234963767075216942687 19164352445650612825414031)
          ·
            refine ⟨28746528668475919238121047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19164352445650612825414031 28746528668475919238121047)
            ·
              refine ⟨43119793002713878857181571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28746528668475919238121047 43119793002713878857181571)
              ·
                refine ⟨64679689504070818285772357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43119793002713878857181571 64679689504070818285772357)
                ·
                  refine ⟨12127441782013278428582317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64679689504070818285772357 12127441782013278428582317)
                  ·
                    refine ⟨4547790668254979410718369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12127441782013278428582317 4547790668254979410718369)
                    ·
                      refine ⟨3410843001191234558038777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547790668254979410718369 3410843001191234558038777)
                      ·
                        rfl

theorem cell23_6642593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6642593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642593 prefixEnd_6642593 := by exact prefixLift 6642593
  have htrace : WordTrace (prefixWord ++ tailWord_6642593) baseStart_6642593 baseEnd_6642593 := by
    simpa [prefixWord, tailWord_6642593, baseEnd_6642593] using wordTrace_append hprefix tailTrace_6642593
  have hstable : (prefixWord ++ tailWord_6642593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642593).length < 2 ^ (prefixWord ++ tailWord_6642593).sum := by decide
  have hdescent : baseEnd_6642593 < baseStart_6642593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642636 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6642636 : Nat := 118140960795 + 6642636 * 2 ^ 59
def prefixEnd_6642636 : Nat := 4983230072969 + 3 ^ 40 * 6642636 * 2
def baseEnd_6642636 : Nat := 3410865080859377889801079

theorem tailTrace_6642636 : CollatzResearch.WordTrace tailWord_6642636 prefixEnd_6642636 3410865080859377889801079 := by
  unfold tailWord_6642636
  simp only [CollatzResearch.WordTrace]
  refine ⟨121138419381435859376993881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161517892508581145835991841 121138419381435859376993881)
  ·
    refine ⟨90853814536076894532745411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121138419381435859376993881 90853814536076894532745411)
    ·
      refine ⟨136280721804115341799118117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90853814536076894532745411 136280721804115341799118117)
      ·
        refine ⟨25552635338271626587334647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136280721804115341799118117 25552635338271626587334647)
        ·
          refine ⟨38328953007407439881001971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25552635338271626587334647 38328953007407439881001971)
          ·
            refine ⟨57493429511111159821502957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38328953007407439881001971 57493429511111159821502957)
            ·
              refine ⟨21560036066666684933063609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57493429511111159821502957 21560036066666684933063609)
              ·
                refine ⟨16170027050000013699797707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21560036066666684933063609 16170027050000013699797707)
                ·
                  refine ⟨24255040575000020549696561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16170027050000013699797707 24255040575000020549696561)
                  ·
                    refine ⟨18191280431250015412272421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24255040575000020549696561 18191280431250015412272421)
                    ·
                      refine ⟨3410865080859377889801079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18191280431250015412272421 3410865080859377889801079)
                      ·
                        rfl

theorem cell23_6642636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6642636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642636 prefixEnd_6642636 := by exact prefixLift 6642636
  have htrace : WordTrace (prefixWord ++ tailWord_6642636) baseStart_6642636 baseEnd_6642636 := by
    simpa [prefixWord, tailWord_6642636, baseEnd_6642636] using wordTrace_append hprefix tailTrace_6642636
  have hstable : (prefixWord ++ tailWord_6642636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642636).length < 2 ^ (prefixWord ++ tailWord_6642636).sum := by decide
  have hdescent : baseEnd_6642636 < baseStart_6642636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642640 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 1, 2, 2]
def baseStart_6642640 : Nat := 118140960795 + 6642640 * 2 ^ 59
def prefixEnd_6642640 : Nat := 4983230072969 + 3 ^ 40 * 6642640 * 2
def baseEnd_6642640 : Nat := 3410867134781995874151061

theorem tailTrace_6642640 : CollatzResearch.WordTrace tailWord_6642640 prefixEnd_6642640 3410867134781995874151061 := by
  unfold tailWord_6642640
  simp only [CollatzResearch.WordTrace]
  refine ⟨121138492327428613718566687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161517989769904818291422249 121138492327428613718566687)
  ·
    refine ⟨181707738491142920577850031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121138492327428613718566687 181707738491142920577850031)
    ·
      refine ⟨272561607736714380866775047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181707738491142920577850031 272561607736714380866775047)
      ·
        refine ⟨408842411605071571300162571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272561607736714380866775047 408842411605071571300162571)
        ·
          refine ⟨613263617407607356950243857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408842411605071571300162571 613263617407607356950243857)
          ·
            refine ⟨459947713055705517712682893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613263617407607356950243857 459947713055705517712682893)
            ·
              refine ⟨172480392395889569142256085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459947713055705517712682893 172480392395889569142256085)
              ·
                refine ⟨4042509196778661776771627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172480392395889569142256085 4042509196778661776771627)
                ·
                  refine ⟨6063763795167992665157441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042509196778661776771627 6063763795167992665157441)
                  ·
                    refine ⟨4547822846375994498868081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6063763795167992665157441 4547822846375994498868081)
                    ·
                      refine ⟨3410867134781995874151061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547822846375994498868081 3410867134781995874151061)
                      ·
                        rfl

theorem cell23_6642640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 2, 2].length) (baseStart_6642640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642640 prefixEnd_6642640 := by exact prefixLift 6642640
  have htrace : WordTrace (prefixWord ++ tailWord_6642640) baseStart_6642640 baseEnd_6642640 := by
    simpa [prefixWord, tailWord_6642640, baseEnd_6642640] using wordTrace_append hprefix tailTrace_6642640
  have hstable : (prefixWord ++ tailWord_6642640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642640).length < 2 ^ (prefixWord ++ tailWord_6642640).sum := by decide
  have hdescent : baseEnd_6642640 < baseStart_6642640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642646 : List Nat := [5, 2, 1, 1, 2, 12]
def baseStart_6642646 : Nat := 118140960795 + 6642646 * 2 ^ 59
def prefixEnd_6642646 : Nat := 4983230072969 + 3 ^ 40 * 6642646 * 2
def baseEnd_6642646 : Nat := 14036502945127254529531

theorem tailTrace_6642646 : CollatzResearch.WordTrace tailWord_6642646 prefixEnd_6642646 14036502945127254529531 := by
  unfold tailWord_6642646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15142325218302218153865737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161518135661890326974567861 15142325218302218153865737)
  ·
    refine ⟨11356743913726663615399303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15142325218302218153865737 11356743913726663615399303)
    ·
      refine ⟨17035115870589995423098955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11356743913726663615399303 17035115870589995423098955)
      ·
        refine ⟨25552673805884993134648433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17035115870589995423098955 25552673805884993134648433)
        ·
          refine ⟨19164505354413744850986325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25552673805884993134648433 19164505354413744850986325)
          ·
            refine ⟨14036502945127254529531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19164505354413744850986325 14036502945127254529531)
            ·
              rfl

theorem cell23_6642646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 12].length) (baseStart_6642646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642646 prefixEnd_6642646 := by exact prefixLift 6642646
  have htrace : WordTrace (prefixWord ++ tailWord_6642646) baseStart_6642646 baseEnd_6642646 := by
    simpa [prefixWord, tailWord_6642646, baseEnd_6642646] using wordTrace_append hprefix tailTrace_6642646
  have hstable : (prefixWord ++ tailWord_6642646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642646).length < 2 ^ (prefixWord ++ tailWord_6642646).sum := by decide
  have hdescent : baseEnd_6642646 < baseStart_6642646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642659 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 9]
def baseStart_6642659 : Nat := 118140960795 + 6642659 * 2 ^ 59
def prefixEnd_6642659 : Nat := 4983230072969 + 3 ^ 40 * 6642659 * 2
def baseEnd_6642659 : Nat := 1136958963638143766604491

theorem tailTrace_6642659 : CollatzResearch.WordTrace tailWord_6642659 prefixEnd_6642659 1136958963638143766604491 := by
  unfold tailWord_6642659
  simp only [CollatzResearch.WordTrace]
  refine ⟨242277677641788393682075031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161518451761192262454716687 242277677641788393682075031)
  ·
    refine ⟨363416516462682590523112547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242277677641788393682075031 363416516462682590523112547)
    ·
      refine ⟨545124774694023885784668821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363416516462682590523112547 545124774694023885784668821)
      ·
        refine ⟨25552723813782369646156351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 545124774694023885784668821 25552723813782369646156351)
        ·
          refine ⟨38329085720673554469234527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25552723813782369646156351 38329085720673554469234527)
          ·
            refine ⟨57493628581010331703851791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38329085720673554469234527 57493628581010331703851791)
            ·
              refine ⟨86240442871515497555777687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57493628581010331703851791 86240442871515497555777687)
              ·
                refine ⟨129360664307273246333666531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86240442871515497555777687 129360664307273246333666531)
                ·
                  refine ⟨194040996460909869500499797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129360664307273246333666531 194040996460909869500499797)
                  ·
                    refine ⟨1136958963638143766604491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194040996460909869500499797 1136958963638143766604491)
                    ·
                      rfl

theorem cell23_6642659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_6642659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642659 prefixEnd_6642659 := by exact prefixLift 6642659
  have htrace : WordTrace (prefixWord ++ tailWord_6642659) baseStart_6642659 baseEnd_6642659 := by
    simpa [prefixWord, tailWord_6642659, baseEnd_6642659] using wordTrace_append hprefix tailTrace_6642659
  have hstable : (prefixWord ++ tailWord_6642659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642659).length < 2 ^ (prefixWord ++ tailWord_6642659).sum := by decide
  have hdescent : baseEnd_6642659 < baseStart_6642659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642673 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_6642673 : Nat := 118140960795 + 6642673 * 2 ^ 59
def prefixEnd_6642673 : Nat := 4983230072969 + 3 ^ 40 * 6642673 * 2
def baseEnd_6642673 : Nat := 3410884079643594245038409

theorem tailTrace_6642673 : CollatzResearch.WordTrace tailWord_6642673 prefixEnd_6642673 3410884079643594245038409 := by
  unfold tailWord_6642673
  simp only [CollatzResearch.WordTrace]
  refine ⟨242278188263737674073084673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161518792175825116048723115 242278188263737674073084673)
  ·
    refine ⟨181708641197803255554813505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242278188263737674073084673 181708641197803255554813505)
    ·
      refine ⟨136281480898352441666110129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181708641197803255554813505 136281480898352441666110129)
      ·
        refine ⟨102211110673764331249582597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136281480898352441666110129 102211110673764331249582597)
        ·
          refine ⟨19164583251330812109296737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102211110673764331249582597 19164583251330812109296737)
          ·
            refine ⟨14373437438498109081972553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19164583251330812109296737 14373437438498109081972553)
            ·
              refine ⟨10780078078873581811479415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14373437438498109081972553 10780078078873581811479415)
              ·
                refine ⟨16170117118310372717219123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10780078078873581811479415 16170117118310372717219123)
                ·
                  refine ⟨24255175677465559075828685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16170117118310372717219123 24255175677465559075828685)
                  ·
                    refine ⟨9095690879049584653435757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24255175677465559075828685 9095690879049584653435757)
                    ·
                      refine ⟨3410884079643594245038409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9095690879049584653435757 3410884079643594245038409)
                      ·
                        rfl

theorem cell23_6642673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_6642673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642673 prefixEnd_6642673 := by exact prefixLift 6642673
  have htrace : WordTrace (prefixWord ++ tailWord_6642673) baseStart_6642673 baseEnd_6642673 := by
    simpa [prefixWord, tailWord_6642673, baseEnd_6642673] using wordTrace_append hprefix tailTrace_6642673
  have hstable : (prefixWord ++ tailWord_6642673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642673).length < 2 ^ (prefixWord ++ tailWord_6642673).sum := by decide
  have hdescent : baseEnd_6642673 < baseStart_6642673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642683 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 1, 3, 2]
def baseStart_6642683 : Nat := 118140960795 + 6642683 * 2 ^ 59
def prefixEnd_6642683 : Nat := 4983230072969 + 3 ^ 40 * 6642683 * 2
def baseEnd_6642683 : Nat := 3410889214450139205913363

theorem tailTrace_6642683 : CollatzResearch.WordTrace tailWord_6642683 prefixEnd_6642683 3410889214450139205913363 := by
  unfold tailWord_6642683
  simp only [CollatzResearch.WordTrace]
  refine ⟨242278552993701445780948703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161519035329134297187299135 242278552993701445780948703)
  ·
    refine ⟨363417829490552168671423055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242278552993701445780948703 363417829490552168671423055)
    ·
      refine ⟨545126744235828253007134583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363417829490552168671423055 545126744235828253007134583)
      ·
        refine ⟨817690116353742379510701875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545126744235828253007134583 817690116353742379510701875)
        ·
          refine ⟨1226535174530613569266052813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817690116353742379510701875 1226535174530613569266052813)
          ·
            refine ⟨459950690448980088474769805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1226535174530613569266052813 459950690448980088474769805)
            ·
              refine ⟨172481508918367533178038677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459950690448980088474769805 172481508918367533178038677)
              ·
                refine ⟨8085070730548478117720563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172481508918367533178038677 8085070730548478117720563)
                ·
                  refine ⟨12127606095822717176580845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8085070730548478117720563 12127606095822717176580845)
                  ·
                    refine ⟨4547852285933518941217817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12127606095822717176580845 4547852285933518941217817)
                    ·
                      refine ⟨3410889214450139205913363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547852285933518941217817 3410889214450139205913363)
                      ·
                        rfl

theorem cell23_6642683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3, 2].length) (baseStart_6642683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642683 prefixEnd_6642683 := by exact prefixLift 6642683
  have htrace : WordTrace (prefixWord ++ tailWord_6642683) baseStart_6642683 baseEnd_6642683 := by
    simpa [prefixWord, tailWord_6642683, baseEnd_6642683] using wordTrace_append hprefix tailTrace_6642683
  have hstable : (prefixWord ++ tailWord_6642683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642683).length < 2 ^ (prefixWord ++ tailWord_6642683).sum := by decide
  have hdescent : baseEnd_6642683 < baseStart_6642683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642700 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_6642700 : Nat := 118140960795 + 6642700 * 2 ^ 59
def prefixEnd_6642700 : Nat := 4983230072969 + 3 ^ 40 * 6642700 * 2
def baseEnd_6642700 : Nat := 3410897943621265639400785

theorem tailTrace_6642700 : CollatzResearch.WordTrace tailWord_6642700 prefixEnd_6642700 3410897943621265639400785 := by
  unfold tailWord_6642700
  simp only [CollatzResearch.WordTrace]
  refine ⟨121139586517319928842158777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161519448689759905122878369 121139586517319928842158777)
  ·
    refine ⟨90854689887989946631619083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121139586517319928842158777 90854689887989946631619083)
    ·
      refine ⟨136282034831984919947428625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90854689887989946631619083 136282034831984919947428625)
      ·
        refine ⟨102211526123988689960571469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136282034831984919947428625 102211526123988689960571469)
        ·
          refine ⟨38329322296495758735214301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102211526123988689960571469 38329322296495758735214301)
          ·
            refine ⟨14373495861185909525705363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38329322296495758735214301 14373495861185909525705363)
            ·
              refine ⟨21560243791778864288558045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14373495861185909525705363 21560243791778864288558045)
              ·
                refine ⟨8085091421917074108209267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21560243791778864288558045 8085091421917074108209267)
                ·
                  refine ⟨12127637132875611162313901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8085091421917074108209267 12127637132875611162313901)
                  ·
                    refine ⟨4547863924828354185867713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12127637132875611162313901 4547863924828354185867713)
                    ·
                      refine ⟨3410897943621265639400785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547863924828354185867713 3410897943621265639400785)
                      ·
                        rfl

theorem cell23_6642700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_6642700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642700 prefixEnd_6642700 := by exact prefixLift 6642700
  have htrace : WordTrace (prefixWord ++ tailWord_6642700) baseStart_6642700 baseEnd_6642700 := by
    simpa [prefixWord, tailWord_6642700, baseEnd_6642700] using wordTrace_append hprefix tailTrace_6642700
  have hstable : (prefixWord ++ tailWord_6642700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642700).length < 2 ^ (prefixWord ++ tailWord_6642700).sum := by decide
  have hdescent : baseEnd_6642700 < baseStart_6642700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642746 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_6642746 : Nat := 118140960795 + 6642746 * 2 ^ 59
def prefixEnd_6642746 : Nat := 4983230072969 + 3 ^ 40 * 6642746 * 2
def baseEnd_6642746 : Nat := 3410921563731372459425573

theorem tailTrace_6642746 : CollatzResearch.WordTrace tailWord_6642746 prefixEnd_6642746 3410921563731372459425573 := by
  unfold tailWord_6642746
  simp only [CollatzResearch.WordTrace]
  refine ⟨60570212698118301885123023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161520567194982138360328061 60570212698118301885123023)
  ·
    refine ⟨90855319047177452827684535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60570212698118301885123023 90855319047177452827684535)
    ·
      refine ⟨136282978570766179241526803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90855319047177452827684535 136282978570766179241526803)
      ·
        refine ⟨204424467856149268862290205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136282978570766179241526803 204424467856149268862290205)
        ·
          refine ⟨76659175446055975823358827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204424467856149268862290205 76659175446055975823358827)
          ·
            refine ⟨114988763169083963735038241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76659175446055975823358827 114988763169083963735038241)
            ·
              refine ⟨86241572376812972801278681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114988763169083963735038241 86241572376812972801278681)
              ·
                refine ⟨64681179282609729600959011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86241572376812972801278681 64681179282609729600959011)
                ·
                  refine ⟨97021768923914594401438517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64681179282609729600959011 97021768923914594401438517)
                  ·
                    refine ⟨9095790836616993225134861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97021768923914594401438517 9095790836616993225134861)
                    ·
                      refine ⟨3410921563731372459425573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9095790836616993225134861 3410921563731372459425573)
                      ·
                        rfl

theorem cell23_6642746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_6642746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642746 prefixEnd_6642746 := by exact prefixLift 6642746
  have htrace : WordTrace (prefixWord ++ tailWord_6642746) baseStart_6642746 baseEnd_6642746 := by
    simpa [prefixWord, tailWord_6642746, baseEnd_6642746] using wordTrace_append hprefix tailTrace_6642746
  have hstable : (prefixWord ++ tailWord_6642746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642746).length < 2 ^ (prefixWord ++ tailWord_6642746).sum := by decide
  have hdescent : baseEnd_6642746 < baseStart_6642746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642773 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_6642773 : Nat := 118140960795 + 6642773 * 2 ^ 59
def prefixEnd_6642773 : Nat := 4983230072969 + 3 ^ 40 * 6642773 * 2
def baseEnd_6642773 : Nat := 3410935427709043853787949

theorem tailTrace_6642773 : CollatzResearch.WordTrace tailWord_6642773 prefixEnd_6642773 3410935427709043853787949 := by
  unfold tailWord_6642773
  simp only [CollatzResearch.WordTrace]
  refine ⟨242281835563375391151724973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161521223708916927434483315 242281835563375391151724973)
  ·
    refine ⟨90855688336265771681896865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242281835563375391151724973 90855688336265771681896865)
    ·
      refine ⟨68141766252199328761422649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90855688336265771681896865 68141766252199328761422649)
      ·
        refine ⟨51106324689149496571066987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68141766252199328761422649 51106324689149496571066987)
        ·
          refine ⟨76659487033724244856600481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51106324689149496571066987 76659487033724244856600481)
          ·
            refine ⟨57494615275293183642450361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76659487033724244856600481 57494615275293183642450361)
            ·
              refine ⟨43120961456469887731837771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57494615275293183642450361 43120961456469887731837771)
              ·
                refine ⟨64681442184704831597756657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43120961456469887731837771 64681442184704831597756657)
                ·
                  refine ⟨48511081638528623698317493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64681442184704831597756657 48511081638528623698317493)
                  ·
                    refine ⟨4547913903612058471717265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48511081638528623698317493 4547913903612058471717265)
                    ·
                      refine ⟨3410935427709043853787949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4547913903612058471717265 3410935427709043853787949)
                      ·
                        rfl

theorem cell23_6642773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_6642773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642773 prefixEnd_6642773 := by exact prefixLift 6642773
  have htrace : WordTrace (prefixWord ++ tailWord_6642773) baseStart_6642773 baseEnd_6642773 := by
    simpa [prefixWord, tailWord_6642773, baseEnd_6642773] using wordTrace_append hprefix tailTrace_6642773
  have hstable : (prefixWord ++ tailWord_6642773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642773).length < 2 ^ (prefixWord ++ tailWord_6642773).sum := by decide
  have hdescent : baseEnd_6642773 < baseStart_6642773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642776 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6642776 : Nat := 118140960795 + 6642776 * 2 ^ 59
def prefixEnd_6642776 : Nat := 4983230072969 + 3 ^ 40 * 6642776 * 2
def baseEnd_6642776 : Nat := 3410936968151007342050435

theorem tailTrace_6642776 : CollatzResearch.WordTrace tailWord_6642776 prefixEnd_6642776 3410936968151007342050435 := by
  unfold tailWord_6642776
  simp only [CollatzResearch.WordTrace]
  refine ⟨121140972491182261332042091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161521296654909681776056121 121140972491182261332042091)
  ·
    refine ⟨181711458736773391998063137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121140972491182261332042091 181711458736773391998063137)
    ·
      refine ⟨136283594052580043998547353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181711458736773391998063137 136283594052580043998547353)
      ·
        refine ⟨102212695539435032998910515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136283594052580043998547353 102212695539435032998910515)
        ·
          refine ⟨153319043309152549498365773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102212695539435032998910515 153319043309152549498365773)
          ·
            refine ⟨57494641240932206061887165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153319043309152549498365773 57494641240932206061887165)
            ·
              refine ⟨21560490465349577273207687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57494641240932206061887165 21560490465349577273207687)
              ·
                refine ⟨32340735698024365909811531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21560490465349577273207687 32340735698024365909811531)
                ·
                  refine ⟨48511103547036548864717297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32340735698024365909811531 48511103547036548864717297)
                  ·
                    refine ⟨36383327660277411648537973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48511103547036548864717297 36383327660277411648537973)
                    ·
                      refine ⟨3410936968151007342050435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36383327660277411648537973 3410936968151007342050435)
                      ·
                        rfl

theorem cell23_6642776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6642776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642776 prefixEnd_6642776 := by exact prefixLift 6642776
  have htrace : WordTrace (prefixWord ++ tailWord_6642776) baseStart_6642776 baseEnd_6642776 := by
    simpa [prefixWord, tailWord_6642776, baseEnd_6642776] using wordTrace_append hprefix tailTrace_6642776
  have hstable : (prefixWord ++ tailWord_6642776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642776).length < 2 ^ (prefixWord ++ tailWord_6642776).sum := by decide
  have hdescent : baseEnd_6642776 < baseStart_6642776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642903 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 1, 6]
def baseStart_6642903 : Nat := 118140960795 + 6642903 * 2 ^ 59
def prefixEnd_6642903 : Nat := 4983230072969 + 3 ^ 40 * 6642903 * 2
def baseEnd_6642903 : Nat := 1137000726731376115054117

theorem tailTrace_6642903 : CollatzResearch.WordTrace tailWord_6642903 prefixEnd_6642903 1137000726731376115054117 := by
  unfold tailWord_6642903
  simp only [CollatzResearch.WordTrace]
  refine ⟨242286577052904423353957363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161524384701936282235971575 242286577052904423353957363)
  ·
    refine ⟨363429865579356635030936045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242286577052904423353957363 363429865579356635030936045)
    ·
      refine ⟨136286199592258738136601017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363429865579356635030936045 136286199592258738136601017)
      ·
        refine ⟨102214649694194053602450763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136286199592258738136601017 102214649694194053602450763)
        ·
          refine ⟨153321974541291080403676145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102214649694194053602450763 153321974541291080403676145)
          ·
            refine ⟨114991480905968310302757109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153321974541291080403676145 114991480905968310302757109)
            ·
              refine ⟨10780451334934529090883479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114991480905968310302757109 10780451334934529090883479)
              ·
                refine ⟨16170677002401793636325219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10780451334934529090883479 16170677002401793636325219)
                ·
                  refine ⟨24256015503602690454487829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16170677002401793636325219 24256015503602690454487829)
                  ·
                    refine ⟨1137000726731376115054117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24256015503602690454487829 1137000726731376115054117)
                    ·
                      rfl

theorem cell23_6642903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_6642903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642903 prefixEnd_6642903 := by exact prefixLift 6642903
  have htrace : WordTrace (prefixWord ++ tailWord_6642903) baseStart_6642903 baseEnd_6642903 := by
    simpa [prefixWord, tailWord_6642903, baseEnd_6642903] using wordTrace_append hprefix tailTrace_6642903
  have hstable : (prefixWord ++ tailWord_6642903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642903).length < 2 ^ (prefixWord ++ tailWord_6642903).sum := by decide
  have hdescent : baseEnd_6642903 < baseStart_6642903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642974 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6642974 : Nat := 118140960795 + 6642974 * 2 ^ 59
def prefixEnd_6642974 : Nat := 4983230072969 + 3 ^ 40 * 6642974 * 2
def baseEnd_6642974 : Nat := 3411038637320597567374525

theorem tailTrace_6642974 : CollatzResearch.WordTrace tailWord_6642974 prefixEnd_6642974 3411038637320597567374525 := by
  unfold tailWord_6642974
  simp only [CollatzResearch.WordTrace]
  refine ⟨30286145829455900309973997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161526111090431468319861317 30286145829455900309973997)
  ·
    refine ⟨11357304686045962616240249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30286145829455900309973997 11357304686045962616240249)
    ·
      refine ⟨8517978514534471962180187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11357304686045962616240249 8517978514534471962180187)
      ·
        refine ⟨12776967771801707943270281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8517978514534471962180187 12776967771801707943270281)
        ·
          refine ⟨9582725828851280957452711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12776967771801707943270281 9582725828851280957452711)
          ·
            refine ⟨14374088743276921436179067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582725828851280957452711 14374088743276921436179067)
            ·
              refine ⟨21561133114915382154268601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14374088743276921436179067 21561133114915382154268601)
              ·
                refine ⟨16170849836186536615701451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21561133114915382154268601 16170849836186536615701451)
                ·
                  refine ⟨24256274754279804923552177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16170849836186536615701451 24256274754279804923552177)
                  ·
                    refine ⟨18192206065709853692664133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24256274754279804923552177 18192206065709853692664133)
                    ·
                      refine ⟨3411038637320597567374525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18192206065709853692664133 3411038637320597567374525)
                      ·
                        rfl

theorem cell23_6642974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6642974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642974 prefixEnd_6642974 := by exact prefixLift 6642974
  have htrace : WordTrace (prefixWord ++ tailWord_6642974) baseStart_6642974 baseEnd_6642974 := by
    simpa [prefixWord, tailWord_6642974, baseEnd_6642974] using wordTrace_append hprefix tailTrace_6642974
  have hstable : (prefixWord ++ tailWord_6642974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642974).length < 2 ^ (prefixWord ++ tailWord_6642974).sum := by decide
  have hdescent : baseEnd_6642974 < baseStart_6642974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6642994 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_6642994 : Nat := 118140960795 + 6642994 * 2 ^ 59
def prefixEnd_6642994 : Nat := 4983230072969 + 3 ^ 40 * 6642994 * 2
def baseEnd_6642994 : Nat := 3411048906933687489124433

theorem tailTrace_6642994 : CollatzResearch.WordTrace tailWord_6642994 prefixEnd_6642994 3411048906933687489124433 := by
  unfold tailWord_6642994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60572474023893686473880009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161526597397049830597013357 60572474023893686473880009)
  ·
    refine ⟨45429355517920264855410007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60572474023893686473880009 45429355517920264855410007)
    ·
      refine ⟨68144033276880397283115011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45429355517920264855410007 68144033276880397283115011)
      ·
        refine ⟨102216049915320595924672517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68144033276880397283115011 102216049915320595924672517)
        ·
          refine ⟨19165509359122611735876097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102216049915320595924672517 19165509359122611735876097)
          ·
            refine ⟨14374132019341958801907073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19165509359122611735876097 14374132019341958801907073)
            ·
              refine ⟨10780599014506469101430305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14374132019341958801907073 10780599014506469101430305)
              ·
                refine ⟨8085449260879851826072729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10780599014506469101430305 8085449260879851826072729)
                ·
                  refine ⟨6064086945659888869554547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8085449260879851826072729 6064086945659888869554547)
                  ·
                    refine ⟨9096130418489833304331821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064086945659888869554547 9096130418489833304331821)
                    ·
                      refine ⟨3411048906933687489124433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9096130418489833304331821 3411048906933687489124433)
                      ·
                        rfl

theorem cell23_6642994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_6642994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6642994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6642994 prefixEnd_6642994 := by exact prefixLift 6642994
  have htrace : WordTrace (prefixWord ++ tailWord_6642994) baseStart_6642994 baseEnd_6642994 := by
    simpa [prefixWord, tailWord_6642994, baseEnd_6642994] using wordTrace_append hprefix tailTrace_6642994
  have hstable : (prefixWord ++ tailWord_6642994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6642994).length < 2 ^ (prefixWord ++ tailWord_6642994).sum := by decide
  have hdescent : baseEnd_6642994 < baseStart_6642994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6642994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643000 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_6643000 : Nat := 118140960795 + 6643000 * 2 ^ 59
def prefixEnd_6643000 : Nat := 4983230072969 + 3 ^ 40 * 6643000 * 2
def baseEnd_6643000 : Nat := 3411051987817614465649405

theorem tailTrace_6643000 : CollatzResearch.WordTrace tailWord_6643000 prefixEnd_6643000 3411051987817614465649405 := by
  unfold tailWord_6643000
  simp only [CollatzResearch.WordTrace]
  refine ⟨121145057466776504460119227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161526743289035339280158969 121145057466776504460119227)
  ·
    refine ⟨181717586200164756690178841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121145057466776504460119227 181717586200164756690178841)
    ·
      refine ⟨136288189650123567517634131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181717586200164756690178841 136288189650123567517634131)
      ·
        refine ⟨204432284475185351276451197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136288189650123567517634131 204432284475185351276451197)
        ·
          refine ⟨76662106678194506728669199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204432284475185351276451197 76662106678194506728669199)
          ·
            refine ⟨114993160017291760093003799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76662106678194506728669199 114993160017291760093003799)
            ·
              refine ⟨172489740025937640139505699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114993160017291760093003799 172489740025937640139505699)
              ·
                refine ⟨258734610038906460209258549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172489740025937640139505699 258734610038906460209258549)
                ·
                  refine ⟨24256369691147480644617989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258734610038906460209258549 24256369691147480644617989)
                  ·
                    refine ⟨4548069317090152620865873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24256369691147480644617989 4548069317090152620865873)
                    ·
                      refine ⟨3411051987817614465649405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548069317090152620865873 3411051987817614465649405)
                      ·
                        rfl

theorem cell23_6643000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_6643000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643000 prefixEnd_6643000 := by exact prefixLift 6643000
  have htrace : WordTrace (prefixWord ++ tailWord_6643000) baseStart_6643000 baseEnd_6643000 := by
    simpa [prefixWord, tailWord_6643000, baseEnd_6643000] using wordTrace_append hprefix tailTrace_6643000
  have hstable : (prefixWord ++ tailWord_6643000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643000).length < 2 ^ (prefixWord ++ tailWord_6643000).sum := by decide
  have hdescent : baseEnd_6643000 < baseStart_6643000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643063 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_6643063 : Nat := 118140960795 + 6643063 * 2 ^ 59
def prefixEnd_6643063 : Nat := 4983230072969 + 3 ^ 40 * 6643063 * 2
def baseEnd_6643063 : Nat := 3411084337098847719161615

theorem tailTrace_6643063 : CollatzResearch.WordTrace tailWord_6643063 prefixEnd_6643063 3411084337098847719161615 := by
  unfold tailWord_6643063
  simp only [CollatzResearch.WordTrace]
  refine ⟨242292412732324770679781843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161528275154883180453187895 242292412732324770679781843)
  ·
    refine ⟨363438619098487156019672765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242292412732324770679781843 363438619098487156019672765)
    ·
      refine ⟨136289482161932683507377287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363438619098487156019672765 136289482161932683507377287)
      ·
        refine ⟨204434223242899025261065931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136289482161932683507377287 204434223242899025261065931)
        ·
          refine ⟨306651334864348537891598897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204434223242899025261065931 306651334864348537891598897)
          ·
            refine ⟨229988501148261403418699173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306651334864348537891598897 229988501148261403418699173)
            ·
              refine ⟨43122843965299013141006095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229988501148261403418699173 43122843965299013141006095)
              ·
                refine ⟨64684265947948519711509143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43122843965299013141006095 64684265947948519711509143)
                ·
                  refine ⟨97026398921922779567263715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64684265947948519711509143 97026398921922779567263715)
                  ·
                    refine ⟨145539598382884169350895573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97026398921922779567263715 145539598382884169350895573)
                    ·
                      refine ⟨3411084337098847719161615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145539598382884169350895573 3411084337098847719161615)
                      ·
                        rfl

theorem cell23_6643063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_6643063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643063 prefixEnd_6643063 := by exact prefixLift 6643063
  have htrace : WordTrace (prefixWord ++ tailWord_6643063) baseStart_6643063 baseEnd_6643063 := by
    simpa [prefixWord, tailWord_6643063, baseEnd_6643063] using wordTrace_append hprefix tailTrace_6643063
  have hstable : (prefixWord ++ tailWord_6643063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643063).length < 2 ^ (prefixWord ++ tailWord_6643063).sum := by decide
  have hdescent : baseEnd_6643063 < baseStart_6643063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643083 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 8]
def baseStart_6643083 : Nat := 118140960795 + 6643083 * 2 ^ 59
def prefixEnd_6643083 : Nat := 4983230072969 + 3 ^ 40 * 6643083 * 2
def baseEnd_6643083 : Nat := 1137031535570645880303841

theorem tailTrace_6643083 : CollatzResearch.WordTrace tailWord_6643083 prefixEnd_6643083 1137031535570645880303841 := by
  unfold tailWord_6643083
  simp only [CollatzResearch.WordTrace]
  refine ⟨242293142192252314095509903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161528761461501542730339935 242293142192252314095509903)
  ·
    refine ⟨363439713288378471143264855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242293142192252314095509903 363439713288378471143264855)
    ·
      refine ⟨545159569932567706714897283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363439713288378471143264855 545159569932567706714897283)
      ·
        refine ⟨817739354898851560072345925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545159569932567706714897283 817739354898851560072345925)
        ·
          refine ⟨153326129043534667513564861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 817739354898851560072345925 153326129043534667513564861)
          ·
            refine ⟨57497298391325500317586823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153326129043534667513564861 57497298391325500317586823)
            ·
              refine ⟨86245947586988250476380235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57497298391325500317586823 86245947586988250476380235)
              ·
                refine ⟨129368921380482375714570353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86245947586988250476380235 129368921380482375714570353)
                ·
                  refine ⟨97026691035361781785927765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129368921380482375714570353 97026691035361781785927765)
                  ·
                    refine ⟨1137031535570645880303841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97026691035361781785927765 1137031535570645880303841)
                    ·
                      rfl

theorem cell23_6643083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_6643083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643083 prefixEnd_6643083 := by exact prefixLift 6643083
  have htrace : WordTrace (prefixWord ++ tailWord_6643083) baseStart_6643083 baseEnd_6643083 := by
    simpa [prefixWord, tailWord_6643083, baseEnd_6643083] using wordTrace_append hprefix tailTrace_6643083
  have hstable : (prefixWord ++ tailWord_6643083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643083).length < 2 ^ (prefixWord ++ tailWord_6643083).sum := by decide
  have hdescent : baseEnd_6643083 < baseStart_6643083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643197 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_6643197 : Nat := 118140960795 + 6643197 * 2 ^ 59
def prefixEnd_6643197 : Nat := 4983230072969 + 3 ^ 40 * 6643197 * 2
def baseEnd_6643197 : Nat := 3411153143506550194885999

theorem tailTrace_6643197 : CollatzResearch.WordTrace tailWord_6643197 prefixEnd_6643197 3411153143506550194885999 := by
  unfold tailWord_6643197
  simp only [CollatzResearch.WordTrace]
  refine ⟨242297300113839311565159845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161531533409226207710106563 242297300113839311565159845)
  ·
    refine ⟨45430743771344870918467471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242297300113839311565159845 45430743771344870918467471)
    ·
      refine ⟨68146115657017306377701207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45430743771344870918467471 68146115657017306377701207)
      ·
        refine ⟨102219173485525959566551811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68146115657017306377701207 102219173485525959566551811)
        ·
          refine ⟨153328760228288939349827717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102219173485525959566551811 153328760228288939349827717)
          ·
            refine ⟨28749142542804176128092697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153328760228288939349827717 28749142542804176128092697)
            ·
              refine ⟨21561856907103132096069523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28749142542804176128092697 21561856907103132096069523)
              ·
                refine ⟨32342785360654698144104285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21561856907103132096069523 32342785360654698144104285)
                ·
                  refine ⟨12128544510245511804039107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32342785360654698144104285 12128544510245511804039107)
                  ·
                    refine ⟨18192816765368267706058661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12128544510245511804039107 18192816765368267706058661)
                    ·
                      refine ⟨3411153143506550194885999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18192816765368267706058661 3411153143506550194885999)
                      ·
                        rfl

theorem cell23_6643197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_6643197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643197 prefixEnd_6643197 := by exact prefixLift 6643197
  have htrace : WordTrace (prefixWord ++ tailWord_6643197) baseStart_6643197 baseEnd_6643197 := by
    simpa [prefixWord, tailWord_6643197, baseEnd_6643197] using wordTrace_append hprefix tailTrace_6643197
  have hstable : (prefixWord ++ tailWord_6643197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643197).length < 2 ^ (prefixWord ++ tailWord_6643197).sum := by decide
  have hdescent : baseEnd_6643197 < baseStart_6643197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643207 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 1, 6]
def baseStart_6643207 : Nat := 118140960795 + 6643207 * 2 ^ 59
def prefixEnd_6643207 : Nat := 4983230072969 + 3 ^ 40 * 6643207 * 2
def baseEnd_6643207 : Nat := 1137052759437698385253651

theorem tailTrace_6643207 : CollatzResearch.WordTrace tailWord_6643207 prefixEnd_6643207 1137052759437698385253651 := by
  unfold tailWord_6643207
  simp only [CollatzResearch.WordTrace]
  refine ⟨242297664843803083273023875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161531776562535388848682583 242297664843803083273023875)
  ·
    refine ⟨363446497265704624909535813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242297664843803083273023875 363446497265704624909535813)
    ·
      refine ⟨68146218237319617170537965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363446497265704624909535813 68146218237319617170537965)
      ·
        refine ⟨25554831838994856438951737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68146218237319617170537965 25554831838994856438951737)
        ·
          refine ⟨19166123879246142329213803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25554831838994856438951737 19166123879246142329213803)
          ·
            refine ⟨28749185818869213493820705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19166123879246142329213803 28749185818869213493820705)
            ·
              refine ⟨21561889364151910120365529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28749185818869213493820705 21561889364151910120365529)
              ·
                refine ⟨16171417023113932590274147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21561889364151910120365529 16171417023113932590274147)
                ·
                  refine ⟨24257125534670898885411221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16171417023113932590274147 24257125534670898885411221)
                  ·
                    refine ⟨1137052759437698385253651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24257125534670898885411221 1137052759437698385253651)
                    ·
                      rfl

theorem cell23_6643207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_6643207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643207 prefixEnd_6643207 := by exact prefixLift 6643207
  have htrace : WordTrace (prefixWord ++ tailWord_6643207) baseStart_6643207 baseEnd_6643207 := by
    simpa [prefixWord, tailWord_6643207, baseEnd_6643207] using wordTrace_append hprefix tailTrace_6643207
  have hstable : (prefixWord ++ tailWord_6643207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643207).length < 2 ^ (prefixWord ++ tailWord_6643207).sum := by decide
  have hdescent : baseEnd_6643207 < baseStart_6643207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643211 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 1, 5]
def baseStart_6643211 : Nat := 118140960795 + 6643211 * 2 ^ 59
def prefixEnd_6643211 : Nat := 4983230072969 + 3 ^ 40 * 6643211 * 2
def baseEnd_6643211 : Nat := 1137053444078571046703645

theorem tailTrace_6643211 : CollatzResearch.WordTrace tailWord_6643211 prefixEnd_6643211 1137053444078571046703645 := by
  unfold tailWord_6643211
  simp only [CollatzResearch.WordTrace]
  refine ⟨242297810735788591956169487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161531873823859061304112991 242297810735788591956169487)
  ·
    refine ⟨363446716103682887934254231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242297810735788591956169487 363446716103682887934254231)
    ·
      refine ⟨545170074155524331901381347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363446716103682887934254231 545170074155524331901381347)
      ·
        refine ⟨817755111233286497852072021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545170074155524331901381347 817755111233286497852072021)
        ·
          refine ⟨9583067709765076146703969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 817755111233286497852072021 9583067709765076146703969)
          ·
            refine ⟨7187300782323807110027977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9583067709765076146703969 7187300782323807110027977)
            ·
              refine ⟨5390475586742855332520983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7187300782323807110027977 5390475586742855332520983)
              ·
                refine ⟨8085713380114282998781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390475586742855332520983 8085713380114282998781475)
                ·
                  refine ⟨12128570070171424498172213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8085713380114282998781475 12128570070171424498172213)
                  ·
                    refine ⟨1137053444078571046703645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12128570070171424498172213 1137053444078571046703645)
                    ·
                      rfl

theorem cell23_6643211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 5].length) (baseStart_6643211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643211 prefixEnd_6643211 := by exact prefixLift 6643211
  have htrace : WordTrace (prefixWord ++ tailWord_6643211) baseStart_6643211 baseEnd_6643211 := by
    simpa [prefixWord, tailWord_6643211, baseEnd_6643211] using wordTrace_append hprefix tailTrace_6643211
  have hstable : (prefixWord ++ tailWord_6643211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643211).length < 2 ^ (prefixWord ++ tailWord_6643211).sum := by decide
  have hdescent : baseEnd_6643211 < baseStart_6643211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643224 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_6643224 : Nat := 118140960795 + 6643224 * 2 ^ 59
def prefixEnd_6643224 : Nat := 4983230072969 + 3 ^ 40 * 6643224 * 2
def baseEnd_6643224 : Nat := 1137055669161407196416125

theorem tailTrace_6643224 : CollatzResearch.WordTrace tailWord_6643224 prefixEnd_6643224 1137055669161407196416125 := by
  unfold tailWord_6643224
  simp only [CollatzResearch.WordTrace]
  refine ⟨121149142442370747588196363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161532189923160996784261817 121149142442370747588196363)
  ·
    refine ⟨181723713663556121382294545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121149142442370747588196363 181723713663556121382294545)
    ·
      refine ⟨136292785247667091036720909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181723713663556121382294545 136292785247667091036720909)
      ·
        refine ⟨51109794467875159138770341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136292785247667091036720909 51109794467875159138770341)
        ·
          refine ⟨9583086462726592338519439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51109794467875159138770341 9583086462726592338519439)
          ·
            refine ⟨14374629694089888507779159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9583086462726592338519439 14374629694089888507779159)
            ·
              refine ⟨21561944541134832761668739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14374629694089888507779159 21561944541134832761668739)
              ·
                refine ⟨32342916811702249142503109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21561944541134832761668739 32342916811702249142503109)
                ·
                  refine ⟨6064296902194171714219333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32342916811702249142503109 6064296902194171714219333)
                  ·
                    refine ⟨1137055669161407196416125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064296902194171714219333 1137055669161407196416125)
                    ·
                      rfl

theorem cell23_6643224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_6643224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643224 prefixEnd_6643224 := by exact prefixLift 6643224
  have htrace : WordTrace (prefixWord ++ tailWord_6643224) baseStart_6643224 baseEnd_6643224 := by
    simpa [prefixWord, tailWord_6643224, baseEnd_6643224] using wordTrace_append hprefix tailTrace_6643224
  have hstable : (prefixWord ++ tailWord_6643224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643224).length < 2 ^ (prefixWord ++ tailWord_6643224).sum := by decide
  have hdescent : baseEnd_6643224 < baseStart_6643224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643254 : List Nat := [5, 1, 2, 1, 3, 1, 1, 9]
def baseStart_6643254 : Nat := 118140960795 + 6643254 * 2 ^ 59
def prefixEnd_6643254 : Nat := 4983230072969 + 3 ^ 40 * 6643254 * 2
def baseEnd_6643254 : Nat := 126340089329772461921231

theorem tailTrace_6643254 : CollatzResearch.WordTrace tailWord_6643254 prefixEnd_6643254 126340089329772461921231 := by
  unfold tailWord_6643254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143711192164550643749051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161532919383088540199989877 15143711192164550643749051)
  ·
    refine ⟨22715566788246825965623577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15143711192164550643749051 22715566788246825965623577)
    ·
      refine ⟨17036675091185119474217683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22715566788246825965623577 17036675091185119474217683)
      ·
        refine ⟨25555012636777679211326525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17036675091185119474217683 25555012636777679211326525)
        ·
          refine ⟨9583129738791629704247447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25555012636777679211326525 9583129738791629704247447)
          ·
            refine ⟨14374694608187444556371171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9583129738791629704247447 14374694608187444556371171)
            ·
              refine ⟨21562041912281166834556757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14374694608187444556371171 21562041912281166834556757)
              ·
                refine ⟨126340089329772461921231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21562041912281166834556757 126340089329772461921231)
                ·
                  rfl

theorem cell23_6643254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_6643254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643254 prefixEnd_6643254 := by exact prefixLift 6643254
  have htrace : WordTrace (prefixWord ++ tailWord_6643254) baseStart_6643254 baseEnd_6643254 := by
    simpa [prefixWord, tailWord_6643254, baseEnd_6643254] using wordTrace_append hprefix tailTrace_6643254
  have hstable : (prefixWord ++ tailWord_6643254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643254).length < 2 ^ (prefixWord ++ tailWord_6643254).sum := by decide
  have hdescent : baseEnd_6643254 < baseStart_6643254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643338 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_6643338 : Nat := 118140960795 + 6643338 * 2 ^ 59
def prefixEnd_6643338 : Nat := 4983230072969 + 3 ^ 40 * 6643338 * 2
def baseEnd_6643338 : Nat := 3411225544278834143222851

theorem tailTrace_6643338 : CollatzResearch.WordTrace tailWord_6643338 prefixEnd_6643338 3411225544278834143222851 := by
  unfold tailWord_6643338
  simp only [CollatzResearch.WordTrace]
  refine ⟨60575610701582123161510667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161534961870885661764028445 60575610701582123161510667)
  ·
    refine ⟨90863416052373184742266001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60575610701582123161510667 90863416052373184742266001)
    ·
      refine ⟨68147562039279888556699501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90863416052373184742266001 68147562039279888556699501)
      ·
        refine ⟨25555335764729958208762313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68147562039279888556699501 25555335764729958208762313)
        ·
          refine ⟨19166501823547468656571735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25555335764729958208762313 19166501823547468656571735)
          ·
            refine ⟨28749752735321202984857603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19166501823547468656571735 28749752735321202984857603)
            ·
              refine ⟨43124629102981804477286405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28749752735321202984857603 43124629102981804477286405)
              ·
                refine ⟨8085867956809088339491201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43124629102981804477286405 8085867956809088339491201)
                ·
                  refine ⟨6064400967606816254618401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8085867956809088339491201 6064400967606816254618401)
                  ·
                    refine ⟨4548300725705112190963801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6064400967606816254618401 4548300725705112190963801)
                    ·
                      refine ⟨3411225544278834143222851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548300725705112190963801 3411225544278834143222851)
                      ·
                        rfl

theorem cell23_6643338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_6643338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643338 prefixEnd_6643338 := by exact prefixLift 6643338
  have htrace : WordTrace (prefixWord ++ tailWord_6643338) baseStart_6643338 baseEnd_6643338 := by
    simpa [prefixWord, tailWord_6643338, baseEnd_6643338] using wordTrace_append hprefix tailTrace_6643338
  have hstable : (prefixWord ++ tailWord_6643338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643338).length < 2 ^ (prefixWord ++ tailWord_6643338).sum := by decide
  have hdescent : baseEnd_6643338 < baseStart_6643338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643357 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_6643357 : Nat := 118140960795 + 6643357 * 2 ^ 59
def prefixEnd_6643357 : Nat := 4983230072969 + 3 ^ 40 * 6643357 * 2
def baseEnd_6643357 : Nat := 1137078433470423189628421

theorem tailTrace_6643357 : CollatzResearch.WordTrace tailWord_6643357 prefixEnd_6643357 1137078433470423189628421 := by
  unfold tailWord_6643357
  simp only [CollatzResearch.WordTrace]
  refine ⟨242303135793259658890984325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161535423862173105927322883 242303135793259658890984325)
  ·
    refine ⟨45431837961236186042059561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242303135793259658890984325 45431837961236186042059561)
    ·
      refine ⟨34073878470927139531544671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45431837961236186042059561 34073878470927139531544671)
      ·
        refine ⟨51110817706390709297317007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34073878470927139531544671 51110817706390709297317007)
        ·
          refine ⟨76666226559586063945975511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51110817706390709297317007 76666226559586063945975511)
          ·
            refine ⟨114999339839379095918963267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76666226559586063945975511 114999339839379095918963267)
            ·
              refine ⟨172499009759068643878444901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114999339839379095918963267 172499009759068643878444901)
              ·
                refine ⟨32343564329825370727208419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172499009759068643878444901 32343564329825370727208419)
                ·
                  refine ⟨48515346494738056090812629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32343564329825370727208419 48515346494738056090812629)
                  ·
                    refine ⟨1137078433470423189628421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48515346494738056090812629 1137078433470423189628421)
                    ·
                      rfl

theorem cell23_6643357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_6643357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643357 prefixEnd_6643357 := by exact prefixLift 6643357
  have htrace : WordTrace (prefixWord ++ tailWord_6643357) baseStart_6643357 baseEnd_6643357 := by
    simpa [prefixWord, tailWord_6643357, baseEnd_6643357] using wordTrace_append hprefix tailTrace_6643357
  have hstable : (prefixWord ++ tailWord_6643357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643357).length < 2 ^ (prefixWord ++ tailWord_6643357).sum := by decide
  have hdescent : baseEnd_6643357 < baseStart_6643357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643464 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_6643464 : Nat := 118140960795 + 6643464 * 2 ^ 59
def prefixEnd_6643464 : Nat := 4983230072969 + 3 ^ 40 * 6643464 * 2
def baseEnd_6643464 : Nat := 1137096747613766883415757

theorem tailTrace_6643464 : CollatzResearch.WordTrace tailWord_6643464 prefixEnd_6643464 1137096747613766883415757 := by
  unfold tailWord_6643464
  simp only [CollatzResearch.WordTrace]
  refine ⟨121153519201936008082564723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161538025602581344110086297 121153519201936008082564723)
  ·
    refine ⟨181730278802904012123847085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121153519201936008082564723 181730278802904012123847085)
    ·
      refine ⟨68148854551089004546442657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181730278802904012123847085 68148854551089004546442657)
      ·
        refine ⟨51111640913316753409831993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68148854551089004546442657 51111640913316753409831993)
        ·
          refine ⟨38333730684987565057373995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51111640913316753409831993 38333730684987565057373995)
          ·
            refine ⟨57500596027481347586060993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38333730684987565057373995 57500596027481347586060993)
            ·
              refine ⟨43125447020611010689545745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57500596027481347586060993 43125447020611010689545745)
              ·
                refine ⟨32344085265458258017159309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43125447020611010689545745 32344085265458258017159309)
                ·
                  refine ⟨12129031974546846756434741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32344085265458258017159309 12129031974546846756434741)
                  ·
                    refine ⟨1137096747613766883415757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12129031974546846756434741 1137096747613766883415757)
                    ·
                      rfl

theorem cell23_6643464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_6643464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643464 prefixEnd_6643464 := by exact prefixLift 6643464
  have htrace : WordTrace (prefixWord ++ tailWord_6643464) baseStart_6643464 baseEnd_6643464 := by
    simpa [prefixWord, tailWord_6643464, baseEnd_6643464] using wordTrace_append hprefix tailTrace_6643464
  have hstable : (prefixWord ++ tailWord_6643464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643464).length < 2 ^ (prefixWord ++ tailWord_6643464).sum := by decide
  have hdescent : baseEnd_6643464 < baseStart_6643464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643488 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6643488 : Nat := 118140960795 + 6643488 * 2 ^ 59
def prefixEnd_6643488 : Nat := 4983230072969 + 3 ^ 40 * 6643488 * 2
def baseEnd_6643488 : Nat := 3411302566377008556347161

theorem tailTrace_6643488 : CollatzResearch.WordTrace tailWord_6643488 prefixEnd_6643488 3411302566377008556347161 := by
  unfold tailWord_6643488
  simp only [CollatzResearch.WordTrace]
  refine ⟨121153956877892534132001559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161538609170523378842668745 121153956877892534132001559)
  ·
    refine ⟨181730935316838801198002339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121153956877892534132001559 181730935316838801198002339)
    ·
      refine ⟨272596402975258201797003509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181730935316838801198002339 272596402975258201797003509)
      ·
        refine ⟨25555912778930456418469079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272596402975258201797003509 25555912778930456418469079)
        ·
          refine ⟨38333869168395684627703619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25555912778930456418469079 38333869168395684627703619)
          ·
            refine ⟨57500803752593526941555429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38333869168395684627703619 57500803752593526941555429)
            ·
              refine ⟨10781400703611286301541643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57500803752593526941555429 10781400703611286301541643)
              ·
                refine ⟨16172101055416929452312465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10781400703611286301541643 16172101055416929452312465)
                ·
                  refine ⟨12129075791562697089234349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16172101055416929452312465 12129075791562697089234349)
                  ·
                    refine ⟨4548403421836011408462881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12129075791562697089234349 4548403421836011408462881)
                    ·
                      refine ⟨3411302566377008556347161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548403421836011408462881 3411302566377008556347161)
                      ·
                        rfl

theorem cell23_6643488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6643488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643488 prefixEnd_6643488 := by exact prefixLift 6643488
  have htrace : WordTrace (prefixWord ++ tailWord_6643488) baseStart_6643488 baseEnd_6643488 := by
    simpa [prefixWord, tailWord_6643488, baseEnd_6643488] using wordTrace_append hprefix tailTrace_6643488
  have hstable : (prefixWord ++ tailWord_6643488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643488).length < 2 ^ (prefixWord ++ tailWord_6643488).sum := by decide
  have hdescent : baseEnd_6643488 < baseStart_6643488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643507 : List Nat := [1, 1, 1, 2, 18]
def baseStart_6643507 : Nat := 118140960795 + 6643507 * 2 ^ 59
def prefixEnd_6643507 : Nat := 4983230072969 + 3 ^ 40 * 6643507 * 2
def baseEnd_6643507 : Nat := 4679440771617892979437

theorem tailTrace_6643507 : CollatzResearch.WordTrace tailWord_6643507 prefixEnd_6643507 4679440771617892979437 := by
  unfold tailWord_6643507
  simp only [CollatzResearch.WordTrace]
  refine ⟨242308606742716234508944775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161539071161810823005963183 242308606742716234508944775)
  ·
    refine ⟨363462910114074351763417163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242308606742716234508944775 363462910114074351763417163)
    ·
      refine ⟨545194365171111527645125745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363462910114074351763417163 545194365171111527645125745)
      ·
        refine ⟨408895773878333645733844309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545194365171111527645125745 408895773878333645733844309)
        ·
          refine ⟨4679440771617892979437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 18 408895773878333645733844309 4679440771617892979437)
          ·
            rfl

theorem cell23_6643507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 18].length) (baseStart_6643507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643507 prefixEnd_6643507 := by exact prefixLift 6643507
  have htrace : WordTrace (prefixWord ++ tailWord_6643507) baseStart_6643507 baseEnd_6643507 := by
    simpa [prefixWord, tailWord_6643507, baseEnd_6643507] using wordTrace_append hprefix tailTrace_6643507
  have hstable : (prefixWord ++ tailWord_6643507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643507).length < 2 ^ (prefixWord ++ tailWord_6643507).sum := by decide
  have hdescent : baseEnd_6643507 < baseStart_6643507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643512 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 1, 1, 3]
def baseStart_6643512 : Nat := 118140960795 + 6643512 * 2 ^ 59
def prefixEnd_6643512 : Nat := 4983230072969 + 3 ^ 40 * 6643512 * 2
def baseEnd_6643512 : Nat := 3411314889912716462447051

theorem tailTrace_6643512 : CollatzResearch.WordTrace tailWord_6643512 prefixEnd_6643512 3411314889912716462447051 := by
  unfold tailWord_6643512
  simp only [CollatzResearch.WordTrace]
  refine ⟨121154394553849060181438395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161539192738465413575251193 121154394553849060181438395)
  ·
    refine ⟨181731591830773590272157593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121154394553849060181438395 181731591830773590272157593)
    ·
      refine ⟨136298693873080192704118195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181731591830773590272157593 136298693873080192704118195)
      ·
        refine ⟨204448040809620289056177293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136298693873080192704118195 204448040809620289056177293)
        ·
          refine ⟨76668015303607608396066485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204448040809620289056177293 76668015303607608396066485)
          ·
            refine ⟨7187626434713213287131233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76668015303607608396066485 7187626434713213287131233)
            ·
              refine ⟨5390719826034909965348425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7187626434713213287131233 5390719826034909965348425)
              ·
                refine ⟨4043039869526182474011319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390719826034909965348425 4043039869526182474011319)
                ·
                  refine ⟨6064559804289273711016979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043039869526182474011319 6064559804289273711016979)
                  ·
                    refine ⟨9096839706433910566525469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064559804289273711016979 9096839706433910566525469)
                    ·
                      refine ⟨3411314889912716462447051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9096839706433910566525469 3411314889912716462447051)
                      ·
                        rfl

theorem cell23_6643512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_6643512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643512 prefixEnd_6643512 := by exact prefixLift 6643512
  have htrace : WordTrace (prefixWord ++ tailWord_6643512) baseStart_6643512 baseEnd_6643512 := by
    simpa [prefixWord, tailWord_6643512, baseEnd_6643512] using wordTrace_append hprefix tailTrace_6643512
  have hstable : (prefixWord ++ tailWord_6643512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643512).length < 2 ^ (prefixWord ++ tailWord_6643512).sum := by decide
  have hdescent : baseEnd_6643512 < baseStart_6643512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643541 : List Nat := [1, 3, 2, 2, 2, 3, 3, 7]
def baseStart_6643541 : Nat := 118140960795 + 6643541 * 2 ^ 59
def prefixEnd_6643541 : Nat := 4983230072969 + 3 ^ 40 * 6643541 * 2
def baseEnd_6643541 : Nat := 126345547438951735147571

theorem tailTrace_6643541 : CollatzResearch.WordTrace tailWord_6643541 prefixEnd_6643541 126345547438951735147571 := by
  unfold tailWord_6643541
  simp only [CollatzResearch.WordTrace]
  refine ⟨242309846824593058315682477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161539897883062038877121651 242309846824593058315682477)
  ·
    refine ⟨90866192559222396868380929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242309846824593058315682477 90866192559222396868380929)
    ·
      refine ⟨68149644419416797651285697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90866192559222396868380929 68149644419416797651285697)
      ·
        refine ⟨51112233314562598238464273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68149644419416797651285697 51112233314562598238464273)
        ·
          refine ⟨38334174985921948678848205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51112233314562598238464273 38334174985921948678848205)
          ·
            refine ⟨14375315619720730754568077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38334174985921948678848205 14375315619720730754568077)
            ·
              refine ⟨5390743357395274032963029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14375315619720730754568077 5390743357395274032963029)
              ·
                refine ⟨126345547438951735147571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5390743357395274032963029 126345547438951735147571)
                ·
                  rfl

theorem cell23_6643541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 7].length) (baseStart_6643541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643541 prefixEnd_6643541 := by exact prefixLift 6643541
  have htrace : WordTrace (prefixWord ++ tailWord_6643541) baseStart_6643541 baseEnd_6643541 := by
    simpa [prefixWord, tailWord_6643541, baseEnd_6643541] using wordTrace_append hprefix tailTrace_6643541
  have hstable : (prefixWord ++ tailWord_6643541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643541).length < 2 ^ (prefixWord ++ tailWord_6643541).sum := by decide
  have hdescent : baseEnd_6643541 < baseStart_6643541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643551 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_6643551 : Nat := 118140960795 + 6643551 * 2 ^ 59
def prefixEnd_6643551 : Nat := 4983230072969 + 3 ^ 40 * 6643551 * 2
def baseEnd_6643551 : Nat := 3411334915658241809859371

theorem tailTrace_6643551 : CollatzResearch.WordTrace tailWord_6643551 prefixEnd_6643551 3411334915658241809859371 := by
  unfold tailWord_6643551
  simp only [CollatzResearch.WordTrace]
  refine ⟨242310211554556830023546507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161540141036371220015697671 242310211554556830023546507)
  ·
    refine ⟨363465317331835245035319761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242310211554556830023546507 363465317331835245035319761)
    ·
      refine ⟨272598987998876433776489821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363465317331835245035319761 272598987998876433776489821)
      ·
        refine ⟨102224620499578662666183683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272598987998876433776489821 102224620499578662666183683)
        ·
          refine ⟨153336930749367993999275525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102224620499578662666183683 153336930749367993999275525)
          ·
            refine ⟨28750674515506498874864161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153336930749367993999275525 28750674515506498874864161)
            ·
              refine ⟨21563005886629874156148121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28750674515506498874864161 21563005886629874156148121)
              ·
                refine ⟨16172254414972405617111091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21563005886629874156148121 16172254414972405617111091)
                ·
                  refine ⟨24258381622458608425666637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16172254414972405617111091 24258381622458608425666637)
                  ·
                    refine ⟨9096893108421978159624989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24258381622458608425666637 9096893108421978159624989)
                    ·
                      refine ⟨3411334915658241809859371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9096893108421978159624989 3411334915658241809859371)
                      ·
                        rfl

theorem cell23_6643551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_6643551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643551 prefixEnd_6643551 := by exact prefixLift 6643551
  have htrace : WordTrace (prefixWord ++ tailWord_6643551) baseStart_6643551 baseEnd_6643551 := by
    simpa [prefixWord, tailWord_6643551, baseEnd_6643551] using wordTrace_append hprefix tailTrace_6643551
  have hstable : (prefixWord ++ tailWord_6643551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643551).length < 2 ^ (prefixWord ++ tailWord_6643551).sum := by decide
  have hdescent : baseEnd_6643551 < baseStart_6643551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643552 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 1, 2, 2]
def baseStart_6643552 : Nat := 118140960795 + 6643552 * 2 ^ 59
def prefixEnd_6643552 : Nat := 4983230072969 + 3 ^ 40 * 6643552 * 2
def baseEnd_6643552 : Nat := 3411335429138896305946867

theorem tailTrace_6643552 : CollatzResearch.WordTrace tailWord_6643552 prefixEnd_6643552 3411335429138896305946867 := by
  unfold tailWord_6643552
  simp only [CollatzResearch.WordTrace]
  refine ⟨121155124013776603597166455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161540165351702138129555273 121155124013776603597166455)
  ·
    refine ⟨181732686020664905395749683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121155124013776603597166455 181732686020664905395749683)
    ·
      refine ⟨272599029030997358093624525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181732686020664905395749683 272599029030997358093624525)
      ·
        refine ⟨102224635886624009285109197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272599029030997358093624525 102224635886624009285109197)
        ·
          refine ⟨38334238457484003481915949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102224635886624009285109197 38334238457484003481915949)
          ·
            refine ⟨14375339421556501305718481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38334238457484003481915949 14375339421556501305718481)
            ·
              refine ⟨10781504566167375979288861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14375339421556501305718481 10781504566167375979288861)
              ·
                refine ⟨4043064212312765992233323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10781504566167375979288861 4043064212312765992233323)
                ·
                  refine ⟨6064596318469148988349985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043064212312765992233323 6064596318469148988349985)
                  ·
                    refine ⟨4548447238851861741262489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6064596318469148988349985 4548447238851861741262489)
                    ·
                      refine ⟨3411335429138896305946867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548447238851861741262489 3411335429138896305946867)
                      ·
                        rfl

theorem cell23_6643552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_6643552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643552 prefixEnd_6643552 := by exact prefixLift 6643552
  have htrace : WordTrace (prefixWord ++ tailWord_6643552) baseStart_6643552 baseEnd_6643552 := by
    simpa [prefixWord, tailWord_6643552, baseEnd_6643552] using wordTrace_append hprefix tailTrace_6643552
  have hstable : (prefixWord ++ tailWord_6643552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643552).length < 2 ^ (prefixWord ++ tailWord_6643552).sum := by decide
  have hdescent : baseEnd_6643552 < baseStart_6643552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643562 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_6643562 : Nat := 118140960795 + 6643562 * 2 ^ 59
def prefixEnd_6643562 : Nat := 4983230072969 + 3 ^ 40 * 6643562 * 2
def baseEnd_6643562 : Nat := 1137113521315147088940607

theorem tailTrace_6643562 : CollatzResearch.WordTrace tailWord_6643562 prefixEnd_6643562 1137113521315147088940607 := by
  unfold tailWord_6643562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60577653189379244725549235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161540408505011319268131293 60577653189379244725549235)
  ·
    refine ⟨90866479784068867088323853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60577653189379244725549235 90866479784068867088323853)
    ·
      refine ⟨34074929919025825158121445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90866479784068867088323853 34074929919025825158121445)
      ·
        refine ⟨6389049359817342217147771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34074929919025825158121445 6389049359817342217147771)
        ·
          refine ⟨9583574039726013325721657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389049359817342217147771 9583574039726013325721657)
          ·
            refine ⟨7187680529794509994291243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9583574039726013325721657 7187680529794509994291243)
            ·
              refine ⟨10781520794691764991436865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187680529794509994291243 10781520794691764991436865)
              ·
                refine ⟨8086140596018823743577649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10781520794691764991436865 8086140596018823743577649)
                ·
                  refine ⟨6064605447014117807683237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086140596018823743577649 6064605447014117807683237)
                  ·
                    refine ⟨1137113521315147088940607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064605447014117807683237 1137113521315147088940607)
                    ·
                      rfl

theorem cell23_6643562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_6643562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643562 prefixEnd_6643562 := by exact prefixLift 6643562
  have htrace : WordTrace (prefixWord ++ tailWord_6643562) baseStart_6643562 baseEnd_6643562 := by
    simpa [prefixWord, tailWord_6643562, baseEnd_6643562] using wordTrace_append hprefix tailTrace_6643562
  have hstable : (prefixWord ++ tailWord_6643562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643562).length < 2 ^ (prefixWord ++ tailWord_6643562).sum := by decide
  have hdescent : baseEnd_6643562 < baseStart_6643562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643584 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_6643584 : Nat := 118140960795 + 6643584 * 2 ^ 59
def prefixEnd_6643584 : Nat := 4983230072969 + 3 ^ 40 * 6643584 * 2
def baseEnd_6643584 : Nat := 1137117286839946726915573

theorem tailTrace_6643584 : CollatzResearch.WordTrace tailWord_6643584 prefixEnd_6643584 1137117286839946726915573 := by
  unfold tailWord_6643584
  simp only [CollatzResearch.WordTrace]
  refine ⟨121155707581718638329748903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161540943442291517772998537 121155707581718638329748903)
  ·
    refine ⟨181733561372577957494623355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121155707581718638329748903 181733561372577957494623355)
    ·
      refine ⟨272600342058866936241935033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181733561372577957494623355 272600342058866936241935033)
      ·
        refine ⟨204450256544150202181451275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272600342058866936241935033 204450256544150202181451275)
        ·
          refine ⟨306675384816225303272176913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204450256544150202181451275 306675384816225303272176913)
          ·
            refine ⟨230006538612168977454132685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306675384816225303272176913 230006538612168977454132685)
            ·
              refine ⟨86252451979563366545299757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230006538612168977454132685 86252451979563366545299757)
              ·
                refine ⟨32344669492336262454487409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86252451979563366545299757 32344669492336262454487409)
                ·
                  refine ⟨24258502119252196840865557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32344669492336262454487409 24258502119252196840865557)
                  ·
                    refine ⟨1137117286839946726915573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24258502119252196840865557 1137117286839946726915573)
                    ·
                      rfl

theorem cell23_6643584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_6643584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643584 prefixEnd_6643584 := by exact prefixLift 6643584
  have htrace : WordTrace (prefixWord ++ tailWord_6643584) baseStart_6643584 baseEnd_6643584 := by
    simpa [prefixWord, tailWord_6643584, baseEnd_6643584] using wordTrace_append hprefix tailTrace_6643584
  have hstable : (prefixWord ++ tailWord_6643584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643584).length < 2 ^ (prefixWord ++ tailWord_6643584).sum := by decide
  have hdescent : baseEnd_6643584 < baseStart_6643584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643636 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6643636 : Nat := 118140960795 + 6643636 * 2 ^ 59
def prefixEnd_6643636 : Nat := 4983230072969 + 3 ^ 40 * 6643636 * 2
def baseEnd_6643636 : Nat := 3411378561513873977296481

theorem tailTrace_6643636 : CollatzResearch.WordTrace tailWord_6643636 prefixEnd_6643636 3411378561513873977296481 := by
  unfold tailWord_6643636
  simp only [CollatzResearch.WordTrace]
  refine ⟨121156655879624444770195381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161542207839499259693593841 121156655879624444770195381)
  ·
    refine ⟨11358436488714791697205817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121156655879624444770195381 11358436488714791697205817)
    ·
      refine ⟨8518827366536093772904363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11358436488714791697205817 8518827366536093772904363)
      ·
        refine ⟨12778241049804140659356545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518827366536093772904363 12778241049804140659356545)
        ·
          refine ⟨9583680787353105494517409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12778241049804140659356545 9583680787353105494517409)
          ·
            refine ⟨7187760590514829120888057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9583680787353105494517409 7187760590514829120888057)
            ·
              refine ⟨5390820442886121840666043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7187760590514829120888057 5390820442886121840666043)
              ·
                refine ⟨8086230664329182760999065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390820442886121840666043 8086230664329182760999065)
                ·
                  refine ⟨6064672998246887070749299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086230664329182760999065 6064672998246887070749299)
                  ·
                    refine ⟨9097009497370330606123949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064672998246887070749299 9097009497370330606123949)
                    ·
                      refine ⟨3411378561513873977296481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097009497370330606123949 3411378561513873977296481)
                      ·
                        rfl

theorem cell23_6643636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6643636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643636 prefixEnd_6643636 := by exact prefixLift 6643636
  have htrace : WordTrace (prefixWord ++ tailWord_6643636) baseStart_6643636 baseEnd_6643636 := by
    simpa [prefixWord, tailWord_6643636, baseEnd_6643636] using wordTrace_append hprefix tailTrace_6643636
  have hstable : (prefixWord ++ tailWord_6643636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643636).length < 2 ^ (prefixWord ++ tailWord_6643636).sum := by decide
  have hdescent : baseEnd_6643636 < baseStart_6643636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643641 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6643641 : Nat := 118140960795 + 6643641 * 2 ^ 59
def prefixEnd_6643641 : Nat := 4983230072969 + 3 ^ 40 * 6643641 * 2
def baseEnd_6643641 : Nat := 3411381128917146457733957

theorem tailTrace_6643641 : CollatzResearch.WordTrace tailWord_6643641 prefixEnd_6643641 3411381128917146457733957 := by
  unfold tailWord_6643641
  simp only [CollatzResearch.WordTrace]
  refine ⟨242313494124230775394322777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161542329416153850262881851 242313494124230775394322777)
  ·
    refine ⟨181735120593173081545742083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242313494124230775394322777 181735120593173081545742083)
    ·
      refine ⟨272602680889759622318613125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181735120593173081545742083 272602680889759622318613125)
      ·
        refine ⟨51113002666829929184739961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272602680889759622318613125 51113002666829929184739961)
        ·
          refine ⟨38334752000122446888554971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51113002666829929184739961 38334752000122446888554971)
          ·
            refine ⟨57502128000183670332832457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38334752000122446888554971 57502128000183670332832457)
            ·
              refine ⟨43126596000137752749624343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57502128000183670332832457 43126596000137752749624343)
              ·
                refine ⟨64689894000206629124436515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43126596000137752749624343 64689894000206629124436515)
                ·
                  refine ⟨97034841000309943686654773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64689894000206629124436515 97034841000309943686654773)
                  ·
                    refine ⟨9097016343779057220623885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97034841000309943686654773 9097016343779057220623885)
                    ·
                      refine ⟨3411381128917146457733957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097016343779057220623885 3411381128917146457733957)
                      ·
                        rfl

theorem cell23_6643641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6643641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643641 prefixEnd_6643641 := by exact prefixLift 6643641
  have htrace : WordTrace (prefixWord ++ tailWord_6643641) baseStart_6643641 baseEnd_6643641 := by
    simpa [prefixWord, tailWord_6643641, baseEnd_6643641] using wordTrace_append hprefix tailTrace_6643641
  have hstable : (prefixWord ++ tailWord_6643641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643641).length < 2 ^ (prefixWord ++ tailWord_6643641).sum := by decide
  have hdescent : baseEnd_6643641 < baseStart_6643641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643682 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_6643682 : Nat := 118140960795 + 6643682 * 2 ^ 59
def prefixEnd_6643682 : Nat := 4983230072969 + 3 ^ 40 * 6643682 * 2
def baseEnd_6643682 : Nat := 379044686847108977480141

theorem tailTrace_6643682 : CollatzResearch.WordTrace tailWord_6643682 prefixEnd_6643682 379044686847108977480141 := by
  unfold tailWord_6643682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60578747379270559849141325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161543326344721492931043533 60578747379270559849141325)
  ·
    refine ⟨22717030267226459943427997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60578747379270559849141325 22717030267226459943427997)
    ·
      refine ⟨8518886350209922478785499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22717030267226459943427997 8518886350209922478785499)
      ·
        refine ⟨12778329525314883718178249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518886350209922478785499 12778329525314883718178249)
        ·
          refine ⟨9583747143986162788633687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12778329525314883718178249 9583747143986162788633687)
          ·
            refine ⟨14375620715979244182950531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9583747143986162788633687 14375620715979244182950531)
            ·
              refine ⟨21563431073968866274425797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14375620715979244182950531 21563431073968866274425797)
              ·
                refine ⟨4043143326369162426454837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21563431073968866274425797 4043143326369162426454837)
                ·
                  refine ⟨379044686847108977480141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4043143326369162426454837 379044686847108977480141)
                  ·
                    rfl

theorem cell23_6643682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_6643682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643682 prefixEnd_6643682 := by exact prefixLift 6643682
  have htrace : WordTrace (prefixWord ++ tailWord_6643682) baseStart_6643682 baseEnd_6643682 := by
    simpa [prefixWord, tailWord_6643682, baseEnd_6643682] using wordTrace_append hprefix tailTrace_6643682
  have hstable : (prefixWord ++ tailWord_6643682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643682).length < 2 ^ (prefixWord ++ tailWord_6643682).sum := by decide
  have hdescent : baseEnd_6643682 < baseStart_6643682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643691 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 7, 4]
def baseStart_6643691 : Nat := 118140960795 + 6643691 * 2 ^ 59
def prefixEnd_6643691 : Nat := 4983230072969 + 3 ^ 40 * 6643691 * 2
def baseEnd_6643691 : Nat := 1137135600983290420702909

theorem tailTrace_6643691 : CollatzResearch.WordTrace tailWord_6643691 prefixEnd_6643691 1137135600983290420702909 := by
  unfold tailWord_6643691
  simp only [CollatzResearch.WordTrace]
  refine ⟨242315317774049633933642927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161543545182699755955761951 242315317774049633933642927)
  ·
    refine ⟨363472976661074450900464391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242315317774049633933642927 363472976661074450900464391)
    ·
      refine ⟨545209464991611676350696587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363472976661074450900464391 545209464991611676350696587)
      ·
        refine ⟨817814197487417514526044881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545209464991611676350696587 817814197487417514526044881)
        ·
          refine ⟨613360648115563135894533661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817814197487417514526044881 613360648115563135894533661)
          ·
            refine ⟨230010243043336175960450123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613360648115563135894533661 230010243043336175960450123)
            ·
              refine ⟨345015364565004263940675185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230010243043336175960450123 345015364565004263940675185)
              ·
                refine ⟨258761523423753197955506389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345015364565004263940675185 258761523423753197955506389)
                ·
                  refine ⟨6064723205244215577082181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 258761523423753197955506389 6064723205244215577082181)
                  ·
                    refine ⟨1137135600983290420702909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064723205244215577082181 1137135600983290420702909)
                    ·
                      rfl

theorem cell23_6643691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 4].length) (baseStart_6643691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643691 prefixEnd_6643691 := by exact prefixLift 6643691
  have htrace : WordTrace (prefixWord ++ tailWord_6643691) baseStart_6643691 baseEnd_6643691 := by
    simpa [prefixWord, tailWord_6643691, baseEnd_6643691] using wordTrace_append hprefix tailTrace_6643691
  have hstable : (prefixWord ++ tailWord_6643691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643691).length < 2 ^ (prefixWord ++ tailWord_6643691).sum := by decide
  have hdescent : baseEnd_6643691 < baseStart_6643691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643708 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_6643708 : Nat := 118140960795 + 6643708 * 2 ^ 59
def prefixEnd_6643708 : Nat := 4983230072969 + 3 ^ 40 * 6643708 * 2
def baseEnd_6643708 : Nat := 1137138510706999231865383

theorem tailTrace_6643708 : CollatzResearch.WordTrace tailWord_6643708 prefixEnd_6643708 1137138510706999231865383 := by
  unfold tailWord_6643708
  simp only [CollatzResearch.WordTrace]
  refine ⟨121157968907494022918505889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161543958543325363891341185 121157968907494022918505889)
  ·
    refine ⟨90868476680620517188879417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121157968907494022918505889 90868476680620517188879417)
    ·
      refine ⟨68151357510465387891659563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90868476680620517188879417 68151357510465387891659563)
      ·
        refine ⟨102227036265698081837489345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68151357510465387891659563 102227036265698081837489345)
        ·
          refine ⟨76670277199273561378117009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102227036265698081837489345 76670277199273561378117009)
          ·
            refine ⟨57502707899455171033587757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76670277199273561378117009 57502707899455171033587757)
            ·
              refine ⟨21563515462295689137595409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57502707899455171033587757 21563515462295689137595409)
              ·
                refine ⟨16172636596721766853196557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21563515462295689137595409 16172636596721766853196557)
                ·
                  refine ⟨6064738723770662569948709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16172636596721766853196557 6064738723770662569948709)
                  ·
                    refine ⟨1137138510706999231865383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064738723770662569948709 1137138510706999231865383)
                    ·
                      rfl

theorem cell23_6643708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_6643708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643708 prefixEnd_6643708 := by exact prefixLift 6643708
  have htrace : WordTrace (prefixWord ++ tailWord_6643708) baseStart_6643708 baseEnd_6643708 := by
    simpa [prefixWord, tailWord_6643708, baseEnd_6643708] using wordTrace_append hprefix tailTrace_6643708
  have hstable : (prefixWord ++ tailWord_6643708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643708).length < 2 ^ (prefixWord ++ tailWord_6643708).sum := by decide
  have hdescent : baseEnd_6643708 < baseStart_6643708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643738 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_6643738 : Nat := 118140960795 + 6643738 * 2 ^ 59
def prefixEnd_6643738 : Nat := 4983230072969 + 3 ^ 40 * 6643738 * 2
def baseEnd_6643738 : Nat := 379047881837848064246779

theorem tailTrace_6643738 : CollatzResearch.WordTrace tailWord_6643738 prefixEnd_6643738 379047881837848064246779 := by
  unfold tailWord_6643738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60579258001219840240150967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161544688003252907307069245 60579258001219840240150967)
  ·
    refine ⟨90868887001829760360226451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60579258001219840240150967 90868887001829760360226451)
    ·
      refine ⟨136303330502744640540339677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90868887001829760360226451 136303330502744640540339677)
      ·
        refine ⟨51113748938529240202627379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136303330502744640540339677 51113748938529240202627379)
        ·
          refine ⟨76670623407793860303941069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51113748938529240202627379 76670623407793860303941069)
          ·
            refine ⟨28751483777922697613977901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76670623407793860303941069 28751483777922697613977901)
            ·
              refine ⟨10781806416721011605241713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28751483777922697613977901 10781806416721011605241713)
              ·
                refine ⟨8086354812540758703931285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10781806416721011605241713 8086354812540758703931285)
                ·
                  refine ⟨379047881837848064246779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8086354812540758703931285 379047881837848064246779)
                  ·
                    rfl

theorem cell23_6643738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_6643738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643738 prefixEnd_6643738 := by exact prefixLift 6643738
  have htrace : WordTrace (prefixWord ++ tailWord_6643738) baseStart_6643738 baseEnd_6643738 := by
    simpa [prefixWord, tailWord_6643738, baseEnd_6643738] using wordTrace_append hprefix tailTrace_6643738
  have hstable : (prefixWord ++ tailWord_6643738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643738).length < 2 ^ (prefixWord ++ tailWord_6643738).sum := by decide
  have hdescent : baseEnd_6643738 < baseStart_6643738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643765 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_6643765 : Nat := 118140960795 + 6643765 * 2 ^ 59
def prefixEnd_6643765 : Nat := 4983230072969 + 3 ^ 40 * 6643765 * 2
def baseEnd_6643765 : Nat := 3411444800518303972583387

theorem tailTrace_6643765 : CollatzResearch.WordTrace tailWord_6643765 prefixEnd_6643765 3411444800518303972583387 := by
  unfold tailWord_6643765
  simp only [CollatzResearch.WordTrace]
  refine ⟨242318016775781544571836749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161545344517187696381224499 242318016775781544571836749)
  ·
    refine ⟨90869256290918079214438781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242318016775781544571836749 90869256290918079214438781)
    ·
      refine ⟨34075971109094279705414543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90869256290918079214438781 34075971109094279705414543)
      ·
        refine ⟨51113956663641419558121815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34075971109094279705414543 51113956663641419558121815)
        ·
          refine ⟨76670934995462129337182723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51113956663641419558121815 76670934995462129337182723)
          ·
            refine ⟨115006402493193194005774085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76670934995462129337182723 115006402493193194005774085)
            ·
              refine ⟨21563700467473723876082641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115006402493193194005774085 21563700467473723876082641)
              ·
                refine ⟨16172775350605292907061981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21563700467473723876082641 16172775350605292907061981)
                ·
                  refine ⟨6064790756476984840148243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16172775350605292907061981 6064790756476984840148243)
                  ·
                    refine ⟨9097186134715477260222365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064790756476984840148243 9097186134715477260222365)
                    ·
                      refine ⟨3411444800518303972583387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097186134715477260222365 3411444800518303972583387)
                      ·
                        rfl

theorem cell23_6643765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_6643765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643765 prefixEnd_6643765 := by exact prefixLift 6643765
  have htrace : WordTrace (prefixWord ++ tailWord_6643765) baseStart_6643765 baseEnd_6643765 := by
    simpa [prefixWord, tailWord_6643765, baseEnd_6643765] using wordTrace_append hprefix tailTrace_6643765
  have hstable : (prefixWord ++ tailWord_6643765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643765).length < 2 ^ (prefixWord ++ tailWord_6643765).sum := by decide
  have hdescent : baseEnd_6643765 < baseStart_6643765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643781 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_6643781 : Nat := 118140960795 + 6643781 * 2 ^ 59
def prefixEnd_6643781 : Nat := 4983230072969 + 3 ^ 40 * 6643781 * 2
def baseEnd_6643781 : Nat := 1137151005402925303327771

theorem tailTrace_6643781 : CollatzResearch.WordTrace tailWord_6643781 prefixEnd_6643781 1137151005402925303327771 := by
  unfold tailWord_6643781
  simp only [CollatzResearch.WordTrace]
  refine ⟨242318600343723579304419197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161545733562482386202946131 242318600343723579304419197)
  ·
    refine ⟨90869475128896342239157199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242318600343723579304419197 90869475128896342239157199)
    ·
      refine ⟨136304212693344513358735799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90869475128896342239157199 136304212693344513358735799)
      ·
        refine ⟨204456319040016770038103699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136304212693344513358735799 204456319040016770038103699)
        ·
          refine ⟨306684478560025155057155549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204456319040016770038103699 306684478560025155057155549)
          ·
            refine ⟨115006679460009433146433331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306684478560025155057155549 115006679460009433146433331)
            ·
              refine ⟨172510019190014149719649997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115006679460009433146433331 172510019190014149719649997)
              ·
                refine ⟨64691257196255306144868749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172510019190014149719649997 64691257196255306144868749)
                ·
                  refine ⟨24259221448595739804325781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64691257196255306144868749 24259221448595739804325781)
                  ·
                    refine ⟨1137151005402925303327771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24259221448595739804325781 1137151005402925303327771)
                    ·
                      rfl

theorem cell23_6643781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_6643781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643781 prefixEnd_6643781 := by exact prefixLift 6643781
  have htrace : WordTrace (prefixWord ++ tailWord_6643781) baseStart_6643781 baseEnd_6643781 := by
    simpa [prefixWord, tailWord_6643781, baseEnd_6643781] using wordTrace_append hprefix tailTrace_6643781
  have hstable : (prefixWord ++ tailWord_6643781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643781).length < 2 ^ (prefixWord ++ tailWord_6643781).sum := by decide
  have hdescent : baseEnd_6643781 < baseStart_6643781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643791 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_6643791 : Nat := 118140960795 + 6643791 * 2 ^ 59
def prefixEnd_6643791 : Nat := 4983230072969 + 3 ^ 40 * 6643791 * 2
def baseEnd_6643791 : Nat := 3411458151015320870858267

theorem tailTrace_6643791 : CollatzResearch.WordTrace tailWord_6643791 prefixEnd_6643791 3411458151015320870858267 := by
  unfold tailWord_6643791
  simp only [CollatzResearch.WordTrace]
  refine ⟨242318965073687351012283227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161545976715791567341522151 242318965073687351012283227)
  ·
    refine ⟨363478447610531026518424841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242318965073687351012283227 363478447610531026518424841)
    ·
      refine ⟨272608835707898269888818631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363478447610531026518424841 272608835707898269888818631)
      ·
        refine ⟨408913253561847404833227947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272608835707898269888818631 408913253561847404833227947)
        ·
          refine ⟨613369880342771107249841921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408913253561847404833227947 613369880342771107249841921)
          ·
            refine ⟨460027410257078330437381441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613369880342771107249841921 460027410257078330437381441)
            ·
              refine ⟨345020557692808747828036081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460027410257078330437381441 345020557692808747828036081)
              ·
                refine ⟨258765418269606560871027061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345020557692808747828036081 258765418269606560871027061)
                ·
                  refine ⟨24259257962775615081658787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258765418269606560871027061 24259257962775615081658787)
                  ·
                    refine ⟨36388886944163422622488181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24259257962775615081658787 36388886944163422622488181)
                    ·
                      refine ⟨3411458151015320870858267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36388886944163422622488181 3411458151015320870858267)
                      ·
                        rfl

theorem cell23_6643791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_6643791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643791 prefixEnd_6643791 := by exact prefixLift 6643791
  have htrace : WordTrace (prefixWord ++ tailWord_6643791) baseStart_6643791 baseEnd_6643791 := by
    simpa [prefixWord, tailWord_6643791, baseEnd_6643791] using wordTrace_append hprefix tailTrace_6643791
  have hstable : (prefixWord ++ tailWord_6643791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643791).length < 2 ^ (prefixWord ++ tailWord_6643791).sum := by decide
  have hdescent : baseEnd_6643791 < baseStart_6643791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643801 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_6643801 : Nat := 118140960795 + 6643801 * 2 ^ 59
def prefixEnd_6643801 : Nat := 4983230072969 + 3 ^ 40 * 6643801 * 2
def baseEnd_6643801 : Nat := 3411463285821865831733221

theorem tailTrace_6643801 : CollatzResearch.WordTrace tailWord_6643801 prefixEnd_6643801 3411463285821865831733221 := by
  unfold tailWord_6643801
  simp only [CollatzResearch.WordTrace]
  refine ⟨242319329803651122720147257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161546219869100748480098171 242319329803651122720147257)
  ·
    refine ⟨181739497352738342040110443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242319329803651122720147257 181739497352738342040110443)
    ·
      refine ⟨272609246029107513060165665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181739497352738342040110443 272609246029107513060165665)
      ·
        refine ⟨204456934521830634795124249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272609246029107513060165665 204456934521830634795124249)
        ·
          refine ⟨153342700891372976096343187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204456934521830634795124249 153342700891372976096343187)
          ·
            refine ⟨230014051337059464144514781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153342700891372976096343187 230014051337059464144514781)
            ·
              refine ⟨86255269251397299054193043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230014051337059464144514781 86255269251397299054193043)
              ·
                refine ⟨129382903877095948581289565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86255269251397299054193043 129382903877095948581289565)
                ·
                  refine ⟨48518588953910980717983587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129382903877095948581289565 48518588953910980717983587)
                  ·
                    refine ⟨72777883430866471076975381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48518588953910980717983587 72777883430866471076975381)
                    ·
                      refine ⟨3411463285821865831733221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72777883430866471076975381 3411463285821865831733221)
                      ·
                        rfl

theorem cell23_6643801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_6643801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643801 prefixEnd_6643801 := by exact prefixLift 6643801
  have htrace : WordTrace (prefixWord ++ tailWord_6643801) baseStart_6643801 baseEnd_6643801 := by
    simpa [prefixWord, tailWord_6643801, baseEnd_6643801] using wordTrace_append hprefix tailTrace_6643801
  have hstable : (prefixWord ++ tailWord_6643801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643801).length < 2 ^ (prefixWord ++ tailWord_6643801).sum := by decide
  have hdescent : baseEnd_6643801 < baseStart_6643801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643806 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_6643806 : Nat := 118140960795 + 6643806 * 2 ^ 59
def prefixEnd_6643806 : Nat := 4983230072969 + 3 ^ 40 * 6643806 * 2
def baseEnd_6643806 : Nat := 379051761469459812463411

theorem tailTrace_6643806 : CollatzResearch.WordTrace tailWord_6643806 prefixEnd_6643806 379051761469459812463411 := by
  unfold tailWord_6643806
  simp only [CollatzResearch.WordTrace]
  refine ⟨30289939021079126071759909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161546341445755339049386181 30289939021079126071759909)
  ·
    refine ⟨5679363566452336138454983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30289939021079126071759909 5679363566452336138454983)
    ·
      refine ⟨8519045349678504207682475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679363566452336138454983 8519045349678504207682475)
      ·
        refine ⟨12778568024517756311523713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519045349678504207682475 12778568024517756311523713)
        ·
          refine ⟨9583926018388317233642785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12778568024517756311523713 9583926018388317233642785)
          ·
            refine ⟨7187944513791237925232089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9583926018388317233642785 7187944513791237925232089)
            ·
              refine ⟨5390958385343428443924067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7187944513791237925232089 5390958385343428443924067)
              ·
                refine ⟨8086437578015142665886101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390958385343428443924067 8086437578015142665886101)
                ·
                  refine ⟨379051761469459812463411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8086437578015142665886101 379051761469459812463411)
                  ·
                    rfl

theorem cell23_6643806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_6643806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643806 prefixEnd_6643806 := by exact prefixLift 6643806
  have htrace : WordTrace (prefixWord ++ tailWord_6643806) baseStart_6643806 baseEnd_6643806 := by
    simpa [prefixWord, tailWord_6643806, baseEnd_6643806] using wordTrace_append hprefix tailTrace_6643806
  have hstable : (prefixWord ++ tailWord_6643806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643806).length < 2 ^ (prefixWord ++ tailWord_6643806).sum := by decide
  have hdescent : baseEnd_6643806 < baseStart_6643806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643808 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_6643808 : Nat := 118140960795 + 6643808 * 2 ^ 59
def prefixEnd_6643808 : Nat := 4983230072969 + 3 ^ 40 * 6643808 * 2
def baseEnd_6643808 : Nat := 3411466880186447304345689

theorem tailTrace_6643808 : CollatzResearch.WordTrace tailWord_6643808 prefixEnd_6643808 3411466880186447304345689 := by
  unfold tailWord_6643808
  simp only [CollatzResearch.WordTrace]
  refine ⟨121159792557312881457826039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161546390076417175277101385 121159792557312881457826039)
  ·
    refine ⟨181739688835969322186739059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121159792557312881457826039 181739688835969322186739059)
    ·
      refine ⟨272609533253953983280108589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181739688835969322186739059 272609533253953983280108589)
      ·
        refine ⟨102228574970232743730040721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272609533253953983280108589 102228574970232743730040721)
        ·
          refine ⟨76671431227674557797530541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102228574970232743730040721 76671431227674557797530541)
          ·
            refine ⟨28751786710377959174073953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76671431227674557797530541 28751786710377959174073953)
            ·
              refine ⟨21563840032783469380555465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28751786710377959174073953 21563840032783469380555465)
              ·
                refine ⟨16172880024587602035416599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21563840032783469380555465 16172880024587602035416599)
                ·
                  refine ⟨24259320036881403053124899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16172880024587602035416599 24259320036881403053124899)
                  ·
                    refine ⟨36388980055322104579687349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24259320036881403053124899 36388980055322104579687349)
                    ·
                      refine ⟨3411466880186447304345689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36388980055322104579687349 3411466880186447304345689)
                      ·
                        rfl

theorem cell23_6643808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_6643808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643808 prefixEnd_6643808 := by exact prefixLift 6643808
  have htrace : WordTrace (prefixWord ++ tailWord_6643808) baseStart_6643808 baseEnd_6643808 := by
    simpa [prefixWord, tailWord_6643808, baseEnd_6643808] using wordTrace_append hprefix tailTrace_6643808
  have hstable : (prefixWord ++ tailWord_6643808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643808).length < 2 ^ (prefixWord ++ tailWord_6643808).sum := by decide
  have hdescent : baseEnd_6643808 < baseStart_6643808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643811 : List Nat := [1, 1, 1, 5, 1, 1, 3, 10]
def baseStart_6643811 : Nat := 118140960795 + 6643811 * 2 ^ 59
def prefixEnd_6643811 : Nat := 4983230072969 + 3 ^ 40 * 6643811 * 2
def baseEnd_6643811 : Nat := 126350682245496696022525

theorem tailTrace_6643811 : CollatzResearch.WordTrace tailWord_6643811 prefixEnd_6643811 126350682245496696022525 := by
  unfold tailWord_6643811
  simp only [CollatzResearch.WordTrace]
  refine ⟨242319694533614894428011287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161546463022409929618674191 242319694533614894428011287)
  ·
    refine ⟨363479541800422341642016931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242319694533614894428011287 363479541800422341642016931)
    ·
      refine ⟨545219312700633512463025397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363479541800422341642016931 545219312700633512463025397)
      ·
        refine ⟨51114310565684391793408631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 545219312700633512463025397 51114310565684391793408631)
        ·
          refine ⟨76671465848526587690112947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51114310565684391793408631 76671465848526587690112947)
          ·
            refine ⟨115007198772789881535169421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76671465848526587690112947 115007198772789881535169421)
            ·
              refine ⟨43127699539796205575688533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115007198772789881535169421 43127699539796205575688533)
              ·
                refine ⟨126350682245496696022525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43127699539796205575688533 126350682245496696022525)
                ·
                  rfl

theorem cell23_6643811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 10].length) (baseStart_6643811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643811 prefixEnd_6643811 := by exact prefixLift 6643811
  have htrace : WordTrace (prefixWord ++ tailWord_6643811) baseStart_6643811 baseEnd_6643811 := by
    simpa [prefixWord, tailWord_6643811, baseEnd_6643811] using wordTrace_append hprefix tailTrace_6643811
  have hstable : (prefixWord ++ tailWord_6643811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643811).length < 2 ^ (prefixWord ++ tailWord_6643811).sum := by decide
  have hdescent : baseEnd_6643811 < baseStart_6643811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643815 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 2, 4]
def baseStart_6643815 : Nat := 118140960795 + 6643815 * 2 ^ 59
def prefixEnd_6643815 : Nat := 4983230072969 + 3 ^ 40 * 6643815 * 2
def baseEnd_6643815 : Nat := 1137156824850342925652719

theorem tailTrace_6643815 : CollatzResearch.WordTrace tailWord_6643815 prefixEnd_6643815 1137156824850342925652719 := by
  unfold tailWord_6643815
  simp only [CollatzResearch.WordTrace]
  refine ⟨242319840425600403111156899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161546560283733602074104599 242319840425600403111156899)
  ·
    refine ⟨363479760638400604666735349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242319840425600403111156899 363479760638400604666735349)
    ·
      refine ⟨34076227559850056687506439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363479760638400604666735349 34076227559850056687506439)
      ·
        refine ⟨51114341339775085031259659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34076227559850056687506439 51114341339775085031259659)
        ·
          refine ⟨76671512009662627546889489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51114341339775085031259659 76671512009662627546889489)
          ·
            refine ⟨57503634007246970660167117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76671512009662627546889489 57503634007246970660167117)
            ·
              refine ⟨21563862752717613997562669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57503634007246970660167117 21563862752717613997562669)
              ·
                refine ⟨8086448532269105249086001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21563862752717613997562669 8086448532269105249086001)
                ·
                  refine ⟨6064836399201828936814501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086448532269105249086001 6064836399201828936814501)
                  ·
                    refine ⟨1137156824850342925652719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6064836399201828936814501 1137156824850342925652719)
                    ·
                      rfl

theorem cell23_6643815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_6643815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643815 prefixEnd_6643815 := by exact prefixLift 6643815
  have htrace : WordTrace (prefixWord ++ tailWord_6643815) baseStart_6643815 baseEnd_6643815 := by
    simpa [prefixWord, tailWord_6643815, baseEnd_6643815] using wordTrace_append hprefix tailTrace_6643815
  have hstable : (prefixWord ++ tailWord_6643815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643815).length < 2 ^ (prefixWord ++ tailWord_6643815).sum := by decide
  have hdescent : baseEnd_6643815 < baseStart_6643815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643822 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6643822 : Nat := 118140960795 + 6643822 * 2 ^ 59
def prefixEnd_6643822 : Nat := 4983230072969 + 3 ^ 40 * 6643822 * 2
def baseEnd_6643822 : Nat := 3411474068915610249570625

theorem tailTrace_6643822 : CollatzResearch.WordTrace tailWord_6643822 prefixEnd_6643822 3411474068915610249570625 := by
  unfold tailWord_6643822
  simp only [CollatzResearch.WordTrace]
  refine ⟨30290011967071880413332715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161546730491050028871107813 30290011967071880413332715)
  ·
    refine ⟨45435017950607820619999073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30290011967071880413332715 45435017950607820619999073)
    ·
      refine ⟨34076263462955865464999305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45435017950607820619999073 34076263462955865464999305)
      ·
        refine ⟨25557197597216899098749479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34076263462955865464999305 25557197597216899098749479)
        ·
          refine ⟨38335796395825348648124219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25557197597216899098749479 38335796395825348648124219)
          ·
            refine ⟨57503694593738022972186329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38335796395825348648124219 57503694593738022972186329)
            ·
              refine ⟨43127770945303517229139747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57503694593738022972186329 43127770945303517229139747)
              ·
                refine ⟨64691656417955275843709621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43127770945303517229139747 64691656417955275843709621)
                ·
                  refine ⟨6064842789183307110347777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64691656417955275843709621 6064842789183307110347777)
                  ·
                    refine ⟨4548632091887480332760833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6064842789183307110347777 4548632091887480332760833)
                    ·
                      refine ⟨3411474068915610249570625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548632091887480332760833 3411474068915610249570625)
                      ·
                        rfl

theorem cell23_6643822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6643822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643822 prefixEnd_6643822 := by exact prefixLift 6643822
  have htrace : WordTrace (prefixWord ++ tailWord_6643822) baseStart_6643822 baseEnd_6643822 := by
    simpa [prefixWord, tailWord_6643822, baseEnd_6643822] using wordTrace_append hprefix tailTrace_6643822
  have hstable : (prefixWord ++ tailWord_6643822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643822).length < 2 ^ (prefixWord ++ tailWord_6643822).sum := by decide
  have hdescent : baseEnd_6643822 < baseStart_6643822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643851 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_6643851 : Nat := 118140960795 + 6643851 * 2 ^ 59
def prefixEnd_6643851 : Nat := 4983230072969 + 3 ^ 40 * 6643851 * 2
def baseEnd_6643851 : Nat := 3411488959854590636107991

theorem tailTrace_6643851 : CollatzResearch.WordTrace tailWord_6643851 prefixEnd_6643851 3411488959854590636107991 := by
  unfold tailWord_6643851
  simp only [CollatzResearch.WordTrace]
  refine ⟨242321153453469981259467407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161547435635646654172978271 242321153453469981259467407)
  ·
    refine ⟨363481730180204971889201111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242321153453469981259467407 363481730180204971889201111)
    ·
      refine ⟨545222595270307457833801667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363481730180204971889201111 545222595270307457833801667)
      ·
        refine ⟨817833892905461186750702501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545222595270307457833801667 817833892905461186750702501)
        ·
          refine ⟨153343854919773972515756719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 817833892905461186750702501 153343854919773972515756719)
          ·
            refine ⟨230015782379660958773635079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153343854919773972515756719 230015782379660958773635079)
            ·
              refine ⟨345023673569491438160452619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230015782379660958773635079 345023673569491438160452619)
              ·
                refine ⟨517535510354237157240678929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345023673569491438160452619 517535510354237157240678929)
                ·
                  refine ⟨388151632765677867930509197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517535510354237157240678929 388151632765677867930509197)
                  ·
                    refine ⟨145556862287129200473940949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388151632765677867930509197 145556862287129200473940949)
                    ·
                      refine ⟨3411488959854590636107991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145556862287129200473940949 3411488959854590636107991)
                      ·
                        rfl

theorem cell23_6643851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_6643851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643851 prefixEnd_6643851 := by exact prefixLift 6643851
  have htrace : WordTrace (prefixWord ++ tailWord_6643851) baseStart_6643851 baseEnd_6643851 := by
    simpa [prefixWord, tailWord_6643851, baseEnd_6643851] using wordTrace_append hprefix tailTrace_6643851
  have hstable : (prefixWord ++ tailWord_6643851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643851).length < 2 ^ (prefixWord ++ tailWord_6643851).sum := by decide
  have hdescent : baseEnd_6643851 < baseStart_6643851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643858 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6643858 : Nat := 118140960795 + 6643858 * 2 ^ 59
def prefixEnd_6643858 : Nat := 4983230072969 + 3 ^ 40 * 6643858 * 2
def baseEnd_6643858 : Nat := 1137164184739724036240153

theorem tailTrace_6643858 : CollatzResearch.WordTrace tailWord_6643858 prefixEnd_6643858 1137164184739724036240153 := by
  unfold tailWord_6643858
  simp only [CollatzResearch.WordTrace]
  refine ⟨60580352191111155363743057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161547605842963080969981485 60580352191111155363743057)
  ·
    refine ⟨45435264143333366522807293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60580352191111155363743057 45435264143333366522807293)
    ·
      refine ⟨17038224053750012446052735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45435264143333366522807293 17038224053750012446052735)
      ·
        refine ⟨25557336080625018669079103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17038224053750012446052735 25557336080625018669079103)
        ·
          refine ⟨38336004120937528003618655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25557336080625018669079103 38336004120937528003618655)
          ·
            refine ⟨57504006181406292005427983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38336004120937528003618655 57504006181406292005427983)
            ·
              refine ⟨86256009272109438008141975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57504006181406292005427983 86256009272109438008141975)
              ·
                refine ⟨129384013908164157012212963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86256009272109438008141975 129384013908164157012212963)
                ·
                  refine ⟨194076020862246235518319445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129384013908164157012212963 194076020862246235518319445)
                  ·
                    refine ⟨1137164184739724036240153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194076020862246235518319445 1137164184739724036240153)
                    ·
                      rfl

theorem cell23_6643858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6643858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643858 prefixEnd_6643858 := by exact prefixLift 6643858
  have htrace : WordTrace (prefixWord ++ tailWord_6643858) baseStart_6643858 baseEnd_6643858 := by
    simpa [prefixWord, tailWord_6643858, baseEnd_6643858] using wordTrace_append hprefix tailTrace_6643858
  have hstable : (prefixWord ++ tailWord_6643858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643858).length < 2 ^ (prefixWord ++ tailWord_6643858).sum := by decide
  have hdescent : baseEnd_6643858 < baseStart_6643858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643872 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3]
def baseStart_6643872 : Nat := 118140960795 + 6643872 * 2 ^ 59
def prefixEnd_6643872 : Nat := 4983230072969 + 3 ^ 40 * 6643872 * 2
def baseEnd_6643872 : Nat := 3411499742948335053945395

theorem tailTrace_6643872 : CollatzResearch.WordTrace tailWord_6643872 prefixEnd_6643872 3411499742948335053945395 := by
  unfold tailWord_6643872
  simp only [CollatzResearch.WordTrace]
  refine ⟨121160959693196950922990935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161547946257595934563987913 121160959693196950922990935)
  ·
    refine ⟨181741439539795426384486403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121160959693196950922990935 181741439539795426384486403)
    ·
      refine ⟨272612159309693139576729605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181741439539795426384486403 272612159309693139576729605)
      ·
        refine ⟨51114779870567463670636801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272612159309693139576729605 51114779870567463670636801)
        ·
          refine ⟨38336084902925597752977601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51114779870567463670636801 38336084902925597752977601)
          ·
            refine ⟨28752063677194198314733201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38336084902925597752977601 28752063677194198314733201)
            ·
              refine ⟨21564047757895648736049901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28752063677194198314733201 21564047757895648736049901)
              ·
                refine ⟨8086517909210868276018713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21564047757895648736049901 8086517909210868276018713)
                ·
                  refine ⟨6064888431908151207014035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086517909210868276018713 6064888431908151207014035)
                  ·
                    refine ⟨9097332647862226810521053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064888431908151207014035 9097332647862226810521053)
                    ·
                      refine ⟨3411499742948335053945395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097332647862226810521053 3411499742948335053945395)
                      ·
                        rfl

theorem cell23_6643872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_6643872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643872 prefixEnd_6643872 := by exact prefixLift 6643872
  have htrace : WordTrace (prefixWord ++ tailWord_6643872) baseStart_6643872 baseEnd_6643872 := by
    simpa [prefixWord, tailWord_6643872, baseEnd_6643872] using wordTrace_append hprefix tailTrace_6643872
  have hstable : (prefixWord ++ tailWord_6643872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643872).length < 2 ^ (prefixWord ++ tailWord_6643872).sum := by decide
  have hdescent : baseEnd_6643872 < baseStart_6643872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643893 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6643893 : Nat := 118140960795 + 6643893 * 2 ^ 59
def prefixEnd_6643893 : Nat := 4983230072969 + 3 ^ 40 * 6643893 * 2
def baseEnd_6643893 : Nat := 3411510526042079471782799

theorem tailTrace_6643893 : CollatzResearch.WordTrace tailWord_6643893 prefixEnd_6643893 3411510526042079471782799 := by
  unfold tailWord_6643893
  simp only [CollatzResearch.WordTrace]
  refine ⟨242322685319317822432496333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161548456879545214954997555 242322685319317822432496333)
  ·
    refine ⟨90871006994744183412186125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242322685319317822432496333 90871006994744183412186125)
    ·
      refine ⟨34076627623029068779569797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90871006994744183412186125 34076627623029068779569797)
      ·
        refine ⟨6389367679317950396169337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34076627623029068779569797 6389367679317950396169337)
        ·
          refine ⟨4792025759488462797127003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6389367679317950396169337 4792025759488462797127003)
          ·
            refine ⟨7188038639232694195690505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792025759488462797127003 7188038639232694195690505)
            ·
              refine ⟨5391028979424520646767879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188038639232694195690505 5391028979424520646767879)
              ·
                refine ⟨8086543469136780970151819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391028979424520646767879 8086543469136780970151819)
                ·
                  refine ⟨12129815203705171455227729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086543469136780970151819 12129815203705171455227729)
                  ·
                    refine ⟨9097361402778878591420797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12129815203705171455227729 9097361402778878591420797)
                    ·
                      refine ⟨3411510526042079471782799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097361402778878591420797 3411510526042079471782799)
                      ·
                        rfl

theorem cell23_6643893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6643893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643893 prefixEnd_6643893 := by exact prefixLift 6643893
  have htrace : WordTrace (prefixWord ++ tailWord_6643893) baseStart_6643893 baseEnd_6643893 := by
    simpa [prefixWord, tailWord_6643893, baseEnd_6643893] using wordTrace_append hprefix tailTrace_6643893
  have hstable : (prefixWord ++ tailWord_6643893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643893).length < 2 ^ (prefixWord ++ tailWord_6643893).sum := by decide
  have hdescent : baseEnd_6643893 < baseStart_6643893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643898 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_6643898 : Nat := 118140960795 + 6643898 * 2 ^ 59
def prefixEnd_6643898 : Nat := 4983230072969 + 3 ^ 40 * 6643898 * 2
def baseEnd_6643898 : Nat := 3411513093445351952220275

theorem tailTrace_6643898 : CollatzResearch.WordTrace tailWord_6643898 prefixEnd_6643898 3411513093445351952220275 := by
  unfold tailWord_6643898
  simp only [CollatzResearch.WordTrace]
  refine ⟨60580716921074927071607087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161548578456199805524285565 60580716921074927071607087)
  ·
    refine ⟨90871075381612390607410631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60580716921074927071607087 90871075381612390607410631)
    ·
      refine ⟨136306613072418585911115947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90871075381612390607410631 136306613072418585911115947)
      ·
        refine ⟨204459919608627878866673921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136306613072418585911115947 204459919608627878866673921)
        ·
          refine ⟨153344939706470909150005441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204459919608627878866673921 153344939706470909150005441)
          ·
            refine ⟨115008704779853181862504081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153344939706470909150005441 115008704779853181862504081)
            ·
              refine ⟨86256528584889886396878061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115008704779853181862504081 86256528584889886396878061)
              ·
                refine ⟨32346198219333707398829273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86256528584889886396878061 32346198219333707398829273)
                ·
                  refine ⟨24259648664500280549121955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32346198219333707398829273 24259648664500280549121955)
                  ·
                    refine ⟨36389472996750420823682933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24259648664500280549121955 36389472996750420823682933)
                    ·
                      refine ⟨3411513093445351952220275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36389472996750420823682933 3411513093445351952220275)
                      ·
                        rfl

theorem cell23_6643898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_6643898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643898 prefixEnd_6643898 := by exact prefixLift 6643898
  have htrace : WordTrace (prefixWord ++ tailWord_6643898) baseStart_6643898 baseEnd_6643898 := by
    simpa [prefixWord, tailWord_6643898, baseEnd_6643898] using wordTrace_append hprefix tailTrace_6643898
  have hstable : (prefixWord ++ tailWord_6643898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643898).length < 2 ^ (prefixWord ++ tailWord_6643898).sum := by decide
  have hdescent : baseEnd_6643898 < baseStart_6643898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643906 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6643906 : Nat := 118140960795 + 6643906 * 2 ^ 59
def prefixEnd_6643906 : Nat := 4983230072969 + 3 ^ 40 * 6643906 * 2
def baseEnd_6643906 : Nat := 3411517201290587920920239

theorem tailTrace_6643906 : CollatzResearch.WordTrace tailWord_6643906 prefixEnd_6643906 3411517201290587920920239 := by
  unfold tailWord_6643906
  simp only [CollatzResearch.WordTrace]
  refine ⟨60580789867067681413179893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161548772978847150435146381 60580789867067681413179893)
  ·
    refine ⟨5679449050037595132485615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60580789867067681413179893 5679449050037595132485615)
    ·
      refine ⟨8519173575056392698728423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679449050037595132485615 8519173575056392698728423)
      ·
        refine ⟨12778760362584589048092635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519173575056392698728423 12778760362584589048092635)
        ·
          refine ⟨19168140543876883572138953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12778760362584589048092635 19168140543876883572138953)
          ·
            refine ⟨14376105407907662679104215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19168140543876883572138953 14376105407907662679104215)
            ·
              refine ⟨21564158111861494018656323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14376105407907662679104215 21564158111861494018656323)
              ·
                refine ⟨32346237167792241027984485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21564158111861494018656323 32346237167792241027984485)
                ·
                  refine ⟨6064919468961045192747091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32346237167792241027984485 6064919468961045192747091)
                  ·
                    refine ⟨9097379203441567789120637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064919468961045192747091 9097379203441567789120637)
                    ·
                      refine ⟨3411517201290587920920239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097379203441567789120637 3411517201290587920920239)
                      ·
                        rfl

theorem cell23_6643906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6643906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643906 prefixEnd_6643906 := by exact prefixLift 6643906
  have htrace : WordTrace (prefixWord ++ tailWord_6643906) baseStart_6643906 baseEnd_6643906 := by
    simpa [prefixWord, tailWord_6643906, baseEnd_6643906] using wordTrace_append hprefix tailTrace_6643906
  have hstable : (prefixWord ++ tailWord_6643906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643906).length < 2 ^ (prefixWord ++ tailWord_6643906).sum := by decide
  have hdescent : baseEnd_6643906 < baseStart_6643906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643948 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_6643948 : Nat := 118140960795 + 6643948 * 2 ^ 59
def prefixEnd_6643948 : Nat := 4983230072969 + 3 ^ 40 * 6643948 * 2
def baseEnd_6643948 : Nat := 1137179589159358918865015

theorem tailTrace_6643948 : CollatzResearch.WordTrace tailWord_6643948 prefixEnd_6643948 1137179589159358918865015 := by
  unfold tailWord_6643948
  simp only [CollatzResearch.WordTrace]
  refine ⟨121162345667059283412874249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161549794222745711217165665 121162345667059283412874249)
  ·
    refine ⟨90871759250294462559655687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121162345667059283412874249 90871759250294462559655687)
    ·
      refine ⟨136307638875441693839483531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90871759250294462559655687 136307638875441693839483531)
      ·
        refine ⟨204461458313162540759225297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136307638875441693839483531 204461458313162540759225297)
        ·
          refine ⟨153346093734871905569418973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204461458313162540759225297 153346093734871905569418973)
          ·
            refine ⟨57504785150576964588532115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153346093734871905569418973 57504785150576964588532115)
            ·
              refine ⟨86257177725865446882798173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57504785150576964588532115 86257177725865446882798173)
              ·
                refine ⟨32346441647199542581049315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86257177725865446882798173 32346441647199542581049315)
                ·
                  refine ⟨48519662470799313871573973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32346441647199542581049315 48519662470799313871573973)
                  ·
                    refine ⟨1137179589159358918865015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48519662470799313871573973 1137179589159358918865015)
                    ·
                      rfl

theorem cell23_6643948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_6643948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643948 prefixEnd_6643948 := by exact prefixLift 6643948
  have htrace : WordTrace (prefixWord ++ tailWord_6643948) baseStart_6643948 baseEnd_6643948 := by
    simpa [prefixWord, tailWord_6643948, baseEnd_6643948] using wordTrace_append hprefix tailTrace_6643948
  have hstable : (prefixWord ++ tailWord_6643948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643948).length < 2 ^ (prefixWord ++ tailWord_6643948).sum := by decide
  have hdescent : baseEnd_6643948 < baseStart_6643948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6643995 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 3, 4]
def baseStart_6643995 : Nat := 118140960795 + 6643995 * 2 ^ 59
def prefixEnd_6643995 : Nat := 4983230072969 + 3 ^ 40 * 6643995 * 2
def baseEnd_6643995 : Nat := 1137187633689612690902443

theorem tailTrace_6643995 : CollatzResearch.WordTrace tailWord_6643995 prefixEnd_6643995 1137187633689612690902443 := by
  unfold tailWord_6643995
  simp only [CollatzResearch.WordTrace]
  refine ⟨242326405564948293852709439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161550937043298862568472959 242326405564948293852709439)
  ·
    refine ⟨363489608347422440779064159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242326405564948293852709439 363489608347422440779064159)
    ·
      refine ⟨545234412521133661168596239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363489608347422440779064159 545234412521133661168596239)
      ·
        refine ⟨817851618781700491752894359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545234412521133661168596239 817851618781700491752894359)
        ·
          refine ⟨1226777428172550737629341539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817851618781700491752894359 1226777428172550737629341539)
          ·
            refine ⟨1840166142258826106444012309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226777428172550737629341539 1840166142258826106444012309)
            ·
              refine ⟨86257787918382473739563077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1840166142258826106444012309 86257787918382473739563077)
              ·
                refine ⟨16173335234696713826168077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86257787918382473739563077 16173335234696713826168077)
                ·
                  refine ⟨6065000713011267684813029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16173335234696713826168077 6065000713011267684813029)
                  ·
                    refine ⟨1137187633689612690902443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065000713011267684813029 1137187633689612690902443)
                    ·
                      rfl

theorem cell23_6643995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 4].length) (baseStart_6643995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6643995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6643995 prefixEnd_6643995 := by exact prefixLift 6643995
  have htrace : WordTrace (prefixWord ++ tailWord_6643995) baseStart_6643995 baseEnd_6643995 := by
    simpa [prefixWord, tailWord_6643995, baseEnd_6643995] using wordTrace_append hprefix tailTrace_6643995
  have hstable : (prefixWord ++ tailWord_6643995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6643995).length < 2 ^ (prefixWord ++ tailWord_6643995).sum := by decide
  have hdescent : baseEnd_6643995 < baseStart_6643995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6643995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644002 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6644002 : Nat := 118140960795 + 6644002 * 2 ^ 59
def prefixEnd_6644002 : Nat := 4983230072969 + 3 ^ 40 * 6644002 * 2
def baseEnd_6644002 : Nat := 3411566495433419545319797

theorem tailTrace_6644002 : CollatzResearch.WordTrace tailWord_6644002 prefixEnd_6644002 3411566495433419545319797 := by
  unfold tailWord_6644002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60581665218980733512053565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161551107250615289365476173 60581665218980733512053565)
  ·
    refine ⟨22718124457117775067020087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60581665218980733512053565 22718124457117775067020087)
    ·
      refine ⟨34077186685676662600530131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22718124457117775067020087 34077186685676662600530131)
      ·
        refine ⟨51115780028514993900795197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34077186685676662600530131 51115780028514993900795197)
        ·
          refine ⟨19168417510693122712798199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51115780028514993900795197 19168417510693122712798199)
          ·
            refine ⟨28752626266039684069197299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19168417510693122712798199 28752626266039684069197299)
            ·
              refine ⟨43128939399059526103795949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28752626266039684069197299 43128939399059526103795949)
              ·
                refine ⟨16173352274647322288923481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43128939399059526103795949 16173352274647322288923481)
                ·
                  refine ⟨12130014205985491716692611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16173352274647322288923481 12130014205985491716692611)
                  ·
                    refine ⟨18195021308978237575038917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12130014205985491716692611 18195021308978237575038917)
                    ·
                      refine ⟨3411566495433419545319797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18195021308978237575038917 3411566495433419545319797)
                      ·
                        rfl

theorem cell23_6644002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6644002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644002 prefixEnd_6644002 := by exact prefixLift 6644002
  have htrace : WordTrace (prefixWord ++ tailWord_6644002) baseStart_6644002 baseEnd_6644002 := by
    simpa [prefixWord, tailWord_6644002, baseEnd_6644002] using wordTrace_append hprefix tailTrace_6644002
  have hstable : (prefixWord ++ tailWord_6644002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644002).length < 2 ^ (prefixWord ++ tailWord_6644002).sum := by decide
  have hdescent : baseEnd_6644002 < baseStart_6644002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644036 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6644036 : Nat := 118140960795 + 6644036 * 2 ^ 59
def prefixEnd_6644036 : Nat := 4983230072969 + 3 ^ 40 * 6644036 * 2
def baseEnd_6644036 : Nat := 3411583953775672412294641

theorem tailTrace_6644036 : CollatzResearch.WordTrace tailWord_6644036 prefixEnd_6644036 3411583953775672412294641 := by
  unfold tailWord_6644036
  simp only [CollatzResearch.WordTrace]
  refine ⟨121163950478899878927475981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161551933971866505236634641 121163950478899878927475981)
  ·
    refine ⟨45436481429587454597803493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121163950478899878927475981 45436481429587454597803493)
    ·
      refine ⟨8519340268047647737088155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45436481429587454597803493 8519340268047647737088155)
      ·
        refine ⟨12779010402071471605632233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519340268047647737088155 12779010402071471605632233)
        ·
          refine ⟨9584257801553603704224175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12779010402071471605632233 9584257801553603704224175)
          ·
            refine ⟨14376386702330405556336263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584257801553603704224175 14376386702330405556336263)
            ·
              refine ⟨21564580053495608334504395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14376386702330405556336263 21564580053495608334504395)
              ·
                refine ⟨32346870080243412501756593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21564580053495608334504395 32346870080243412501756593)
                ·
                  refine ⟨24260152560182559376317445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32346870080243412501756593 24260152560182559376317445)
                  ·
                    refine ⟨4548778605034229883059521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24260152560182559376317445 4548778605034229883059521)
                    ·
                      refine ⟨3411583953775672412294641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548778605034229883059521 3411583953775672412294641)
                      ·
                        rfl

theorem cell23_6644036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6644036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644036 prefixEnd_6644036 := by exact prefixLift 6644036
  have htrace : WordTrace (prefixWord ++ tailWord_6644036) baseStart_6644036 baseEnd_6644036 := by
    simpa [prefixWord, tailWord_6644036, baseEnd_6644036] using wordTrace_append hprefix tailTrace_6644036
  have hstable : (prefixWord ++ tailWord_6644036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644036).length < 2 ^ (prefixWord ++ tailWord_6644036).sum := by decide
  have hdescent : baseEnd_6644036 < baseStart_6644036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644055 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 3, 5]
def baseStart_6644055 : Nat := 118140960795 + 6644055 * 2 ^ 59
def prefixEnd_6644055 : Nat := 4983230072969 + 3 ^ 40 * 6644055 * 2
def baseEnd_6644055 : Nat := 1137197903302702612652351

theorem tailTrace_6644055 : CollatzResearch.WordTrace tailWord_6644055 prefixEnd_6644055 1137197903302702612652351 := by
  unfold tailWord_6644055
  simp only [CollatzResearch.WordTrace]
  refine ⟨242328593944730924099893619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161552395963153949399929079 242328593944730924099893619)
  ·
    refine ⟨363492890917096386149840429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242328593944730924099893619 363492890917096386149840429)
    ·
      refine ⟨136309834093911144806190161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363492890917096386149840429 136309834093911144806190161)
      ·
        refine ⟨102232375570433358604642621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136309834093911144806190161 102232375570433358604642621)
        ·
          refine ⟨38337140838912509476740983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102232375570433358604642621 38337140838912509476740983)
          ·
            refine ⟨57505711258368764215111475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38337140838912509476740983 57505711258368764215111475)
            ·
              refine ⟨86258566887553146322667213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57505711258368764215111475 86258566887553146322667213)
              ·
                refine ⟨32346962582832429871000205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86258566887553146322667213 32346962582832429871000205)
                ·
                  refine ⟨12130110968562161201625077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32346962582832429871000205 12130110968562161201625077)
                  ·
                    refine ⟨1137197903302702612652351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12130110968562161201625077 1137197903302702612652351)
                    ·
                      rfl

theorem cell23_6644055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_6644055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644055 prefixEnd_6644055 := by exact prefixLift 6644055
  have htrace : WordTrace (prefixWord ++ tailWord_6644055) baseStart_6644055 baseEnd_6644055 := by
    simpa [prefixWord, tailWord_6644055, baseEnd_6644055] using wordTrace_append hprefix tailTrace_6644055
  have hstable : (prefixWord ++ tailWord_6644055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644055).length < 2 ^ (prefixWord ++ tailWord_6644055).sum := by decide
  have hdescent : baseEnd_6644055 < baseStart_6644055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644095 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_6644095 : Nat := 118140960795 + 6644095 * 2 ^ 59
def prefixEnd_6644095 : Nat := 4983230072969 + 3 ^ 40 * 6644095 * 2
def baseEnd_6644095 : Nat := 3411614249134287681456869

theorem tailTrace_6644095 : CollatzResearch.WordTrace tailWord_6644095 prefixEnd_6644095 3411614249134287681456869 := by
  unfold tailWord_6644095
  simp only [CollatzResearch.WordTrace]
  refine ⟨242330052864586010931349739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161553368576390673954233159 242330052864586010931349739)
  ·
    refine ⟨363495079296879016397024609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242330052864586010931349739 363495079296879016397024609)
    ·
      refine ⟨272621309472659262297768457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363495079296879016397024609 272621309472659262297768457)
      ·
        refine ⟨204465982104494446723326343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272621309472659262297768457 204465982104494446723326343)
        ·
          refine ⟨306698973156741670084989515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204465982104494446723326343 306698973156741670084989515)
          ·
            refine ⟨460048459735112505127484273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306698973156741670084989515 460048459735112505127484273)
            ·
              refine ⟨345036344801334378845613205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460048459735112505127484273 345036344801334378845613205)
              ·
                refine ⟨16173578662562549008388119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345036344801334378845613205 16173578662562549008388119)
                ·
                  refine ⟨24260367993843823512582179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16173578662562549008388119 24260367993843823512582179)
                  ·
                    refine ⟨36390551990765735268873269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24260367993843823512582179 36390551990765735268873269)
                    ·
                      refine ⟨3411614249134287681456869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36390551990765735268873269 3411614249134287681456869)
                      ·
                        rfl

theorem cell23_6644095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_6644095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644095 prefixEnd_6644095 := by exact prefixLift 6644095
  have htrace : WordTrace (prefixWord ++ tailWord_6644095) baseStart_6644095 baseEnd_6644095 := by
    simpa [prefixWord, tailWord_6644095, baseEnd_6644095] using wordTrace_append hprefix tailTrace_6644095
  have hstable : (prefixWord ++ tailWord_6644095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644095).length < 2 ^ (prefixWord ++ tailWord_6644095).sum := by decide
  have hdescent : baseEnd_6644095 < baseStart_6644095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644106 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_6644106 : Nat := 118140960795 + 6644106 * 2 ^ 59
def prefixEnd_6644106 : Nat := 4983230072969 + 3 ^ 40 * 6644106 * 2
def baseEnd_6644106 : Nat := 1137206632473829046139773

theorem tailTrace_6644106 : CollatzResearch.WordTrace tailWord_6644106 prefixEnd_6644106 1137206632473829046139773 := by
  unfold tailWord_6644106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60582613516886539952500043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161553636045030773206666781 60582613516886539952500043)
  ·
    refine ⟨90873920275329809928750065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60582613516886539952500043 90873920275329809928750065)
    ·
      refine ⟨68155440206497357446562549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90873920275329809928750065 68155440206497357446562549)
      ·
        refine ⟨6389572519359127260615239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68155440206497357446562549 6389572519359127260615239)
        ·
          refine ⟨9584358779038690890922859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389572519359127260615239 9584358779038690890922859)
          ·
            refine ⟨14376538168558036336384289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584358779038690890922859 14376538168558036336384289)
            ·
              refine ⟨10782403626418527252288217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14376538168558036336384289 10782403626418527252288217)
              ·
                refine ⟨8086802719813895439216163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10782403626418527252288217 8086802719813895439216163)
                ·
                  refine ⟨12130204079720843158824245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086802719813895439216163 12130204079720843158824245)
                  ·
                    refine ⟨1137206632473829046139773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12130204079720843158824245 1137206632473829046139773)
                    ·
                      rfl

theorem cell23_6644106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_6644106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644106 prefixEnd_6644106 := by exact prefixLift 6644106
  have htrace : WordTrace (prefixWord ++ tailWord_6644106) baseStart_6644106 baseEnd_6644106 := by
    simpa [prefixWord, tailWord_6644106, baseEnd_6644106] using wordTrace_append hprefix tailTrace_6644106
  have hstable : (prefixWord ++ tailWord_6644106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644106).length < 2 ^ (prefixWord ++ tailWord_6644106).sum := by decide
  have hdescent : baseEnd_6644106 < baseStart_6644106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644126 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6644126 : Nat := 118140960795 + 6644126 * 2 ^ 59
def prefixEnd_6644126 : Nat := 4983230072969 + 3 ^ 40 * 6644126 * 2
def baseEnd_6644126 : Nat := 3411630167034577060169227

theorem tailTrace_6644126 : CollatzResearch.WordTrace tailWord_6644126 prefixEnd_6644126 3411630167034577060169227 := by
  unfold tailWord_6644126
  simp only [CollatzResearch.WordTrace]
  refine ⟨30291397940934212903216029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161554122351649135483818821 30291397940934212903216029)
  ·
    refine ⟨11359274227850329838706011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30291397940934212903216029 11359274227850329838706011)
    ·
      refine ⟨17038911341775494758059017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11359274227850329838706011 17038911341775494758059017)
      ·
        refine ⟨12779183506331621068544263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17038911341775494758059017 12779183506331621068544263)
        ·
          refine ⟨19168775259497431602816395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779183506331621068544263 19168775259497431602816395)
          ·
            refine ⟨28753162889246147404224593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19168775259497431602816395 28753162889246147404224593)
            ·
              refine ⟨21564872166934610553168445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28753162889246147404224593 21564872166934610553168445)
              ·
                refine ⟨8086827062600478957438167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21564872166934610553168445 8086827062600478957438167)
                ·
                  refine ⟨12130240593900718436157251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086827062600478957438167 12130240593900718436157251)
                  ·
                    refine ⟨18195360890851077654235877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12130240593900718436157251 18195360890851077654235877)
                    ·
                      refine ⟨3411630167034577060169227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18195360890851077654235877 3411630167034577060169227)
                      ·
                        rfl

theorem cell23_6644126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6644126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644126 prefixEnd_6644126 := by exact prefixLift 6644126
  have htrace : WordTrace (prefixWord ++ tailWord_6644126) baseStart_6644126 baseEnd_6644126 := by
    simpa [prefixWord, tailWord_6644126, baseEnd_6644126] using wordTrace_append hprefix tailTrace_6644126
  have hstable : (prefixWord ++ tailWord_6644126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644126).length < 2 ^ (prefixWord ++ tailWord_6644126).sum := by decide
  have hdescent : baseEnd_6644126 < baseStart_6644126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644152 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_6644152 : Nat := 118140960795 + 6644152 * 2 ^ 59
def prefixEnd_6644152 : Nat := 4983230072969 + 3 ^ 40 * 6644152 * 2
def baseEnd_6644152 : Nat := 3411643517531593958444107

theorem tailTrace_6644152 : CollatzResearch.WordTrace tailWord_6644152 prefixEnd_6644152 3411643517531593958444107 := by
  unfold tailWord_6644152
  simp only [CollatzResearch.WordTrace]
  refine ⟨121166065912689754833087355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161554754550253006444116473 121166065912689754833087355)
  ·
    refine ⟨181749098869034632249631033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121166065912689754833087355 181749098869034632249631033)
    ·
      refine ⟨136311824151775974187223275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181749098869034632249631033 136311824151775974187223275)
      ·
        refine ⟨204467736227663961280834913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136311824151775974187223275 204467736227663961280834913)
        ·
          refine ⟨153350802170747970960626185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204467736227663961280834913 153350802170747970960626185)
          ·
            refine ⟨115013101628060978220469639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153350802170747970960626185 115013101628060978220469639)
            ·
              refine ⟨172519652442091467330704459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115013101628060978220469639 172519652442091467330704459)
              ·
                refine ⟨258779478663137200996056689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172519652442091467330704459 258779478663137200996056689)
                ·
                  refine ⟨194084608997352900747042517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258779478663137200996056689 194084608997352900747042517)
                  ·
                    refine ⟨4548858023375458611258809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 194084608997352900747042517 4548858023375458611258809)
                    ·
                      refine ⟨3411643517531593958444107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548858023375458611258809 3411643517531593958444107)
                      ·
                        rfl

theorem cell23_6644152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_6644152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644152 prefixEnd_6644152 := by exact prefixLift 6644152
  have htrace : WordTrace (prefixWord ++ tailWord_6644152) baseStart_6644152 baseEnd_6644152 := by
    simpa [prefixWord, tailWord_6644152, baseEnd_6644152] using wordTrace_append hprefix tailTrace_6644152
  have hstable : (prefixWord ++ tailWord_6644152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644152).length < 2 ^ (prefixWord ++ tailWord_6644152).sum := by decide
  have hdescent : baseEnd_6644152 < baseStart_6644152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644175 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 4, 6]
def baseStart_6644175 : Nat := 118140960795 + 6644175 * 2 ^ 59
def prefixEnd_6644175 : Nat := 4983230072969 + 3 ^ 40 * 6644175 * 2
def baseEnd_6644175 : Nat := 1137218442528882456152167

theorem tailTrace_6644175 : CollatzResearch.WordTrace tailWord_6644175 prefixEnd_6644175 1137218442528882456152167 := by
  unfold tailWord_6644175
  simp only [CollatzResearch.WordTrace]
  refine ⟨242332970704296184594261979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161555313802864123062841319 242332970704296184594261979)
  ·
    refine ⟨363499456056444276891392969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242332970704296184594261979 363499456056444276891392969)
    ·
      refine ⟨272624592042333207668544727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363499456056444276891392969 272624592042333207668544727)
      ·
        refine ⟨408936888063499811502817091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272624592042333207668544727 408936888063499811502817091)
        ·
          refine ⟨613405332095249717254225637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408936888063499811502817091 613405332095249717254225637)
          ·
            refine ⟨115013499767859321985167307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 613405332095249717254225637 115013499767859321985167307)
            ·
              refine ⟨172520249651788982977750961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115013499767859321985167307 172520249651788982977750961)
              ·
                refine ⟨129390187238841737233313221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172520249651788982977750961 129390187238841737233313221)
                ·
                  refine ⟨24260660107282825731246229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129390187238841737233313221 24260660107282825731246229)
                  ·
                    refine ⟨1137218442528882456152167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24260660107282825731246229 1137218442528882456152167)
                    ·
                      rfl

theorem cell23_6644175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_6644175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644175 prefixEnd_6644175 := by exact prefixLift 6644175
  have htrace : WordTrace (prefixWord ++ tailWord_6644175) baseStart_6644175 baseEnd_6644175 := by
    simpa [prefixWord, tailWord_6644175, baseEnd_6644175] using wordTrace_append hprefix tailTrace_6644175
  have hstable : (prefixWord ++ tailWord_6644175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644175).length < 2 ^ (prefixWord ++ tailWord_6644175).sum := by decide
  have hdescent : baseEnd_6644175 < baseStart_6644175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644199 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6644199 : Nat := 118140960795 + 6644199 * 2 ^ 59
def prefixEnd_6644199 : Nat := 4983230072969 + 3 ^ 40 * 6644199 * 2
def baseEnd_6644199 : Nat := 3411667651122355274556391

theorem tailTrace_6644199 : CollatzResearch.WordTrace tailWord_6644199 prefixEnd_6644199 3411667651122355274556391 := by
  unfold tailWord_6644199
  simp only [CollatzResearch.WordTrace]
  refine ⟨242333846056209236693135651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161555897370806157795423767 242333846056209236693135651)
  ·
    refine ⟨363500769084313855039703477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242333846056209236693135651 363500769084313855039703477)
    ·
      refine ⟨34078197101654423909972201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363500769084313855039703477 34078197101654423909972201)
      ·
        refine ⟨25558647826240817932479151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34078197101654423909972201 25558647826240817932479151)
        ·
          refine ⟨38337971739361226898718727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25558647826240817932479151 38337971739361226898718727)
          ·
            refine ⟨57506957609041840348078091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38337971739361226898718727 57506957609041840348078091)
            ·
              refine ⟨86260436413562760522117137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57506957609041840348078091 86260436413562760522117137)
              ·
                refine ⟨64695327310172070391587853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86260436413562760522117137 64695327310172070391587853)
                ·
                  refine ⟨24260747741314526396845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64695327310172070391587853 24260747741314526396845445)
                  ·
                    refine ⟨4548890201496473699408521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24260747741314526396845445 4548890201496473699408521)
                    ·
                      refine ⟨3411667651122355274556391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548890201496473699408521 3411667651122355274556391)
                      ·
                        rfl

theorem cell23_6644199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6644199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644199 prefixEnd_6644199 := by exact prefixLift 6644199
  have htrace : WordTrace (prefixWord ++ tailWord_6644199) baseStart_6644199 baseEnd_6644199 := by
    simpa [prefixWord, tailWord_6644199, baseEnd_6644199] using wordTrace_append hprefix tailTrace_6644199
  have hstable : (prefixWord ++ tailWord_6644199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644199).length < 2 ^ (prefixWord ++ tailWord_6644199).sum := by decide
  have hdescent : baseEnd_6644199 < baseStart_6644199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644215 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_6644215 : Nat := 118140960795 + 6644215 * 2 ^ 59
def prefixEnd_6644215 : Nat := 4983230072969 + 3 ^ 40 * 6644215 * 2
def baseEnd_6644215 : Nat := 3411675866812827211956317

theorem tailTrace_6644215 : CollatzResearch.WordTrace tailWord_6644215 prefixEnd_6644215 3411675866812827211956317 := by
  unfold tailWord_6644215
  simp only [CollatzResearch.WordTrace]
  refine ⟨242334429624151271425718099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161556286416100847617145399 242334429624151271425718099)
  ·
    refine ⟨363501644436226907138577149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242334429624151271425718099 363501644436226907138577149)
    ·
      refine ⟨136313116663585090176966431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363501644436226907138577149 136313116663585090176966431)
      ·
        refine ⟨204469674995377635265449647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136313116663585090176966431 204469674995377635265449647)
        ·
          refine ⟨306704512493066452898174471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204469674995377635265449647 306704512493066452898174471)
          ·
            refine ⟨460056768739599679347261707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306704512493066452898174471 460056768739599679347261707)
            ·
              refine ⟨690085153109399519020892561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460056768739599679347261707 690085153109399519020892561)
              ·
                refine ⟨517563864832049639265669421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690085153109399519020892561 517563864832049639265669421)
                ·
                  refine ⟨194086449312018614724626033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517563864832049639265669421 194086449312018614724626033)
                  ·
                    refine ⟨145564836984013961043469525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194086449312018614724626033 145564836984013961043469525)
                    ·
                      refine ⟨3411675866812827211956317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145564836984013961043469525 3411675866812827211956317)
                      ·
                        rfl

theorem cell23_6644215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_6644215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644215 prefixEnd_6644215 := by exact prefixLift 6644215
  have htrace : WordTrace (prefixWord ++ tailWord_6644215) baseStart_6644215 baseEnd_6644215 := by
    simpa [prefixWord, tailWord_6644215, baseEnd_6644215] using wordTrace_append hprefix tailTrace_6644215
  have hstable : (prefixWord ++ tailWord_6644215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644215).length < 2 ^ (prefixWord ++ tailWord_6644215).sum := by decide
  have hdescent : baseEnd_6644215 < baseStart_6644215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644216 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_6644216 : Nat := 118140960795 + 6644216 * 2 ^ 59
def prefixEnd_6644216 : Nat := 4983230072969 + 3 ^ 40 * 6644216 * 2
def baseEnd_6644216 : Nat := 3411676380293481708043813

theorem tailTrace_6644216 : CollatzResearch.WordTrace tailWord_6644216 prefixEnd_6644216 3411676380293481708043813 := by
  unfold tailWord_6644216
  simp only [CollatzResearch.WordTrace]
  refine ⟨121167233048573824298252251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161556310731431765731003001 121167233048573824298252251)
  ·
    refine ⟨181750849572860736447378377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121167233048573824298252251 181750849572860736447378377)
    ·
      refine ⟨136313137179645552335533783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181750849572860736447378377 136313137179645552335533783)
      ·
        refine ⟨204469705769468328503300675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136313137179645552335533783 204469705769468328503300675)
        ·
          refine ⟨306704558654202492754951013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204469705769468328503300675 306704558654202492754951013)
          ·
            refine ⟨57507104747662967391553315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306704558654202492754951013 57507104747662967391553315)
            ·
              refine ⟨86260657121494451087329973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57507104747662967391553315 86260657121494451087329973)
              ·
                refine ⟨8086936605140104789437185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86260657121494451087329973 8086936605140104789437185)
                ·
                  refine ⟨6065202453855078592077889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086936605140104789437185 6065202453855078592077889)
                  ·
                    refine ⟨4548901840391308944058417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065202453855078592077889 4548901840391308944058417)
                    ·
                      refine ⟨3411676380293481708043813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548901840391308944058417 3411676380293481708043813)
                      ·
                        rfl

theorem cell23_6644216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_6644216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644216 prefixEnd_6644216 := by exact prefixLift 6644216
  have htrace : WordTrace (prefixWord ++ tailWord_6644216) baseStart_6644216 baseEnd_6644216 := by
    simpa [prefixWord, tailWord_6644216, baseEnd_6644216] using wordTrace_append hprefix tailTrace_6644216
  have hstable : (prefixWord ++ tailWord_6644216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644216).length < 2 ^ (prefixWord ++ tailWord_6644216).sum := by decide
  have hdescent : baseEnd_6644216 < baseStart_6644216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644232 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_6644232 : Nat := 118140960795 + 6644232 * 2 ^ 59
def prefixEnd_6644232 : Nat := 4983230072969 + 3 ^ 40 * 6644232 * 2
def baseEnd_6644232 : Nat := 3411684595983953645443739

theorem tailTrace_6644232 : CollatzResearch.WordTrace tailWord_6644232 prefixEnd_6644232 3411684595983953645443739 := by
  unfold tailWord_6644232
  simp only [CollatzResearch.WordTrace]
  refine ⟨121167524832544841664543475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161556699776726455552724633 121167524832544841664543475)
  ·
    refine ⟨181751287248817262496815213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121167524832544841664543475 181751287248817262496815213)
    ·
      refine ⟨68156732718306473436305705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181751287248817262496815213 68156732718306473436305705)
      ·
        refine ⟨51117549538729855077229279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68156732718306473436305705 51117549538729855077229279)
        ·
          refine ⟨76676324308094782615843919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51117549538729855077229279 76676324308094782615843919)
          ·
            refine ⟨115014486462142173923765879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76676324308094782615843919 115014486462142173923765879)
            ·
              refine ⟨172521729693213260885648819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115014486462142173923765879 172521729693213260885648819)
              ·
                refine ⟨258782594539819891328473229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172521729693213260885648819 258782594539819891328473229)
                ·
                  refine ⟨97043472952432459248177461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258782594539819891328473229 97043472952432459248177461)
                  ·
                    refine ⟨9097825589290543054516637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97043472952432459248177461 9097825589290543054516637)
                    ·
                      refine ⟨3411684595983953645443739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097825589290543054516637 3411684595983953645443739)
                      ·
                        rfl

theorem cell23_6644232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_6644232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644232 prefixEnd_6644232 := by exact prefixLift 6644232
  have htrace : WordTrace (prefixWord ++ tailWord_6644232) baseStart_6644232 baseEnd_6644232 := by
    simpa [prefixWord, tailWord_6644232, baseEnd_6644232] using wordTrace_append hprefix tailTrace_6644232
  have hstable : (prefixWord ++ tailWord_6644232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644232).length < 2 ^ (prefixWord ++ tailWord_6644232).sum := by decide
  have hdescent : baseEnd_6644232 < baseStart_6644232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644237 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6644237 : Nat := 118140960795 + 6644237 * 2 ^ 59
def prefixEnd_6644237 : Nat := 4983230072969 + 3 ^ 40 * 6644237 * 2
def baseEnd_6644237 : Nat := 3411687163387226125881217

theorem tailTrace_6644237 : CollatzResearch.WordTrace tailWord_6644237 prefixEnd_6644237 3411687163387226125881217 := by
  unfold tailWord_6644237
  simp only [CollatzResearch.WordTrace]
  refine ⟨242335232030071569183018965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161556821353381046122012643 242335232030071569183018965)
  ·
    refine ⟨5679732000704802402727007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 242335232030071569183018965 5679732000704802402727007)
    ·
      refine ⟨8519598001057203604090511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679732000704802402727007 8519598001057203604090511)
      ·
        refine ⟨12779397001585805406135767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519598001057203604090511 12779397001585805406135767)
        ·
          refine ⟨19169095502378708109203651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779397001585805406135767 19169095502378708109203651)
          ·
            refine ⟨28753643253568062163805477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19169095502378708109203651 28753643253568062163805477)
            ·
              refine ⟨5391308110044011655713527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28753643253568062163805477 5391308110044011655713527)
              ·
                refine ⟨8086962165066017483570291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391308110044011655713527 8086962165066017483570291)
                ·
                  refine ⟨12130443247599026225355437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086962165066017483570291 12130443247599026225355437)
                  ·
                    refine ⟨4548916217849634834508289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12130443247599026225355437 4548916217849634834508289)
                    ·
                      refine ⟨3411687163387226125881217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548916217849634834508289 3411687163387226125881217)
                      ·
                        rfl

theorem cell23_6644237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6644237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644237 prefixEnd_6644237 := by exact prefixLift 6644237
  have htrace : WordTrace (prefixWord ++ tailWord_6644237) baseStart_6644237 baseEnd_6644237 := by
    simpa [prefixWord, tailWord_6644237, baseEnd_6644237] using wordTrace_append hprefix tailTrace_6644237
  have hstable : (prefixWord ++ tailWord_6644237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644237).length < 2 ^ (prefixWord ++ tailWord_6644237).sum := by decide
  have hdescent : baseEnd_6644237 < baseStart_6644237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644272 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_6644272 : Nat := 118140960795 + 6644272 * 2 ^ 59
def prefixEnd_6644272 : Nat := 4983230072969 + 3 ^ 40 * 6644272 * 2
def baseEnd_6644272 : Nat := 3411705135210133488943555

theorem tailTrace_6644272 : CollatzResearch.WordTrace tailWord_6644272 prefixEnd_6644272 3411705135210133488943555 := by
  unfold tailWord_6644272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121168254292472385080271535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161557672389963180107028713 121168254292472385080271535)
  ·
    refine ⟨181752381438708577620407303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121168254292472385080271535 181752381438708577620407303)
    ·
      refine ⟨272628572158062866430610955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181752381438708577620407303 272628572158062866430610955)
      ·
        refine ⟨408942858237094299645916433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272628572158062866430610955 408942858237094299645916433)
        ·
          refine ⟨306707143677820724734437325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408942858237094299645916433 306707143677820724734437325)
          ·
            refine ⟨115015178879182771775413997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306707143677820724734437325 115015178879182771775413997)
            ·
              refine ⟨43130692079693539415780249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115015178879182771775413997 43130692079693539415780249)
              ·
                refine ⟨32348019059770154561835187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43130692079693539415780249 32348019059770154561835187)
                ·
                  refine ⟨48522028589655231842752781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32348019059770154561835187 48522028589655231842752781)
                  ·
                    refine ⟨18195760721120711941032293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48522028589655231842752781 18195760721120711941032293)
                    ·
                      refine ⟨3411705135210133488943555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18195760721120711941032293 3411705135210133488943555)
                      ·
                        rfl

theorem cell23_6644272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_6644272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644272 prefixEnd_6644272 := by exact prefixLift 6644272
  have htrace : WordTrace (prefixWord ++ tailWord_6644272) baseStart_6644272 baseEnd_6644272 := by
    simpa [prefixWord, tailWord_6644272, baseEnd_6644272] using wordTrace_append hprefix tailTrace_6644272
  have hstable : (prefixWord ++ tailWord_6644272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644272).length < 2 ^ (prefixWord ++ tailWord_6644272).sum := by decide
  have hdescent : baseEnd_6644272 < baseStart_6644272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644289 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6644289 : Nat := 118140960795 + 6644289 * 2 ^ 59
def prefixEnd_6644289 : Nat := 4983230072969 + 3 ^ 40 * 6644289 * 2
def baseEnd_6644289 : Nat := 3411713864381259922430977

theorem tailTrace_6644289 : CollatzResearch.WordTrace tailWord_6644289 prefixEnd_6644289 3411713864381259922430977 := by
  unfold tailWord_6644289
  simp only [CollatzResearch.WordTrace]
  refine ⟨242337128625883182063911921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161558085750588788042607947 242337128625883182063911921)
  ·
    refine ⟨181752846469412386547933941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242337128625883182063911921 181752846469412386547933941)
    ·
      refine ⟨17039329356507411238868807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181752846469412386547933941 17039329356507411238868807)
      ·
        refine ⟨25558994034761116858303211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039329356507411238868807 25558994034761116858303211)
        ·
          refine ⟨38338491052141675287454817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25558994034761116858303211 38338491052141675287454817)
          ·
            refine ⟨28753868289106256465591113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38338491052141675287454817 28753868289106256465591113)
            ·
              refine ⟨21565401216829692349193335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28753868289106256465591113 21565401216829692349193335)
              ·
                refine ⟨32348101825244538523790003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21565401216829692349193335 32348101825244538523790003)
                ·
                  refine ⟨48522152737866807785685005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32348101825244538523790003 48522152737866807785685005)
                  ·
                    refine ⟨18195807276700052919631877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48522152737866807785685005 18195807276700052919631877)
                    ·
                      refine ⟨3411713864381259922430977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18195807276700052919631877 3411713864381259922430977)
                      ·
                        rfl

theorem cell23_6644289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6644289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644289 prefixEnd_6644289 := by exact prefixLift 6644289
  have htrace : WordTrace (prefixWord ++ tailWord_6644289) baseStart_6644289 baseEnd_6644289 := by
    simpa [prefixWord, tailWord_6644289, baseEnd_6644289] using wordTrace_append hprefix tailTrace_6644289
  have hstable : (prefixWord ++ tailWord_6644289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644289).length < 2 ^ (prefixWord ++ tailWord_6644289).sum := by decide
  have hdescent : baseEnd_6644289 < baseStart_6644289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644302 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6644302 : Nat := 118140960795 + 6644302 * 2 ^ 59
def prefixEnd_6644302 : Nat := 4983230072969 + 3 ^ 40 * 6644302 * 2
def baseEnd_6644302 : Nat := 3411720539629768371568417

theorem tailTrace_6644302 : CollatzResearch.WordTrace tailWord_6644302 prefixEnd_6644302 3411720539629768371568417 := by
  unfold tailWord_6644302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292200346854510660516895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161558401849890723522756773 30292200346854510660516895)
  ·
    refine ⟨45438300520281765990775343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30292200346854510660516895 45438300520281765990775343)
    ·
      refine ⟨68157450780422648986163015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45438300520281765990775343 68157450780422648986163015)
      ·
        refine ⟨102236176170633973479244523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68157450780422648986163015 102236176170633973479244523)
        ·
          refine ⟨153354264255950960218866785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102236176170633973479244523 153354264255950960218866785)
          ·
            refine ⟨115015698191963220164150089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153354264255950960218866785 115015698191963220164150089)
            ·
              refine ⟨86261773643972415123112567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115015698191963220164150089 86261773643972415123112567)
              ·
                refine ⟨129392660465958622684668851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86261773643972415123112567 129392660465958622684668851)
                ·
                  refine ⟨194088990698937934027003277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129392660465958622684668851 194088990698937934027003277)
                  ·
                    refine ⟨72783371512101725260126229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194088990698937934027003277 72783371512101725260126229)
                    ·
                      refine ⟨3411720539629768371568417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72783371512101725260126229 3411720539629768371568417)
                      ·
                        rfl

theorem cell23_6644302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6644302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644302 prefixEnd_6644302 := by exact prefixLift 6644302
  have htrace : WordTrace (prefixWord ++ tailWord_6644302) baseStart_6644302 baseEnd_6644302 := by
    simpa [prefixWord, tailWord_6644302, baseEnd_6644302] using wordTrace_append hprefix tailTrace_6644302
  have hstable : (prefixWord ++ tailWord_6644302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644302).length < 2 ^ (prefixWord ++ tailWord_6644302).sum := by decide
  have hdescent : baseEnd_6644302 < baseStart_6644302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644309 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_6644309 : Nat := 118140960795 + 6644309 * 2 ^ 59
def prefixEnd_6644309 : Nat := 4983230072969 + 3 ^ 40 * 6644309 * 2
def baseEnd_6644309 : Nat := 3411724133994349844180885

theorem tailTrace_6644309 : CollatzResearch.WordTrace tailWord_6644309 prefixEnd_6644309 3411724133994349844180885 := by
  unfold tailWord_6644309
  simp only [CollatzResearch.WordTrace]
  refine ⟨242337858085810725479639981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161558572057207150319759987 242337858085810725479639981)
  ·
    refine ⟨90876696782179022054864993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242337858085810725479639981 90876696782179022054864993)
    ·
      refine ⟨68157522586634266541148745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90876696782179022054864993 68157522586634266541148745)
      ·
        refine ⟨51118141939975699905861559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68157522586634266541148745 51118141939975699905861559)
        ·
          refine ⟨76677212909963549858792339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51118141939975699905861559 76677212909963549858792339)
          ·
            refine ⟨115015819364945324788188509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76677212909963549858792339 115015819364945324788188509)
            ·
              refine ⟨43130932261854496795570691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115015819364945324788188509 43130932261854496795570691)
              ·
                refine ⟨64696398392781745193356037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43130932261854496795570691 64696398392781745193356037)
                ·
                  refine ⟨12130574698646577223754257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64696398392781745193356037 12130574698646577223754257)
                  ·
                    refine ⟨9097931023984932917815693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12130574698646577223754257 9097931023984932917815693)
                    ·
                      refine ⟨3411724133994349844180885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9097931023984932917815693 3411724133994349844180885)
                      ·
                        rfl

theorem cell23_6644309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_6644309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644309 prefixEnd_6644309 := by exact prefixLift 6644309
  have htrace : WordTrace (prefixWord ++ tailWord_6644309) baseStart_6644309 baseEnd_6644309 := by
    simpa [prefixWord, tailWord_6644309, baseEnd_6644309] using wordTrace_append hprefix tailTrace_6644309
  have hstable : (prefixWord ++ tailWord_6644309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644309).length < 2 ^ (prefixWord ++ tailWord_6644309).sum := by decide
  have hdescent : baseEnd_6644309 < baseStart_6644309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644312 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 8]
def baseStart_6644312 : Nat := 118140960795 + 6644312 * 2 ^ 59
def prefixEnd_6644312 : Nat := 4983230072969 + 3 ^ 40 * 6644312 * 2
def baseEnd_6644312 : Nat := 379080630492923703604819

theorem tailTrace_6644312 : CollatzResearch.WordTrace tailWord_6644312 prefixEnd_6644312 379080630492923703604819 := by
  unfold tailWord_6644312
  simp only [CollatzResearch.WordTrace]
  refine ⟨121168983752399928495999595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161558645003199904661332793 121168983752399928495999595)
  ·
    refine ⟨181753475628599892743999393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121168983752399928495999595 181753475628599892743999393)
    ·
      refine ⟨136315106721449919557999545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181753475628599892743999393 136315106721449919557999545)
      ·
        refine ⟨102236330041087439668499659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136315106721449919557999545 102236330041087439668499659)
        ·
          refine ⟨153354495061631159502749489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102236330041087439668499659 153354495061631159502749489)
          ·
            refine ⟨115015871296223369627062117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153354495061631159502749489 115015871296223369627062117)
            ·
              refine ⟨21565475868041881805074147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115015871296223369627062117 21565475868041881805074147)
              ·
                refine ⟨32348213802062822707611221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21565475868041881805074147 32348213802062822707611221)
                ·
                  refine ⟨379080630492923703604819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32348213802062822707611221 379080630492923703604819)
                  ·
                    rfl

theorem cell23_6644312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_6644312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644312 prefixEnd_6644312 := by exact prefixLift 6644312
  have htrace : WordTrace (prefixWord ++ tailWord_6644312) baseStart_6644312 baseEnd_6644312 := by
    simpa [prefixWord, tailWord_6644312, baseEnd_6644312] using wordTrace_append hprefix tailTrace_6644312
  have hstable : (prefixWord ++ tailWord_6644312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644312).length < 2 ^ (prefixWord ++ tailWord_6644312).sum := by decide
  have hdescent : baseEnd_6644312 < baseStart_6644312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644318 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6644318 : Nat := 118140960795 + 6644318 * 2 ^ 59
def prefixEnd_6644318 : Nat := 4983230072969 + 3 ^ 40 * 6644318 * 2
def baseEnd_6644318 : Nat := 3411728755320240308968345

theorem tailTrace_6644318 : CollatzResearch.WordTrace tailWord_6644318 prefixEnd_6644318 3411728755320240308968345 := by
  unfold tailWord_6644318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292273292847265002089701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161558790895185413344478405 30292273292847265002089701)
  ·
    refine ⟨5679801242408862187891819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30292273292847265002089701 5679801242408862187891819)
    ·
      refine ⟨8519701863613293281837729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679801242408862187891819 8519701863613293281837729)
      ·
        refine ⟨6389776397709969961378297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8519701863613293281837729 6389776397709969961378297)
        ·
          refine ⟨4792332298282477471033723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6389776397709969961378297 4792332298282477471033723)
          ·
            refine ⟨7188498447423716206550585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792332298282477471033723 7188498447423716206550585)
            ·
              refine ⟨5391373835567787154912939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188498447423716206550585 5391373835567787154912939)
              ·
                refine ⟨8087060753351680732369409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391373835567787154912939 8087060753351680732369409)
                ·
                  refine ⟨6065295565013760549277057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087060753351680732369409 6065295565013760549277057)
                  ·
                    refine ⟨4548971673760320411957793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065295565013760549277057 4548971673760320411957793)
                    ·
                      refine ⟨3411728755320240308968345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4548971673760320411957793 3411728755320240308968345)
                      ·
                        rfl

theorem cell23_6644318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6644318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644318 prefixEnd_6644318 := by exact prefixLift 6644318
  have htrace : WordTrace (prefixWord ++ tailWord_6644318) baseStart_6644318 baseEnd_6644318 := by
    simpa [prefixWord, tailWord_6644318, baseEnd_6644318] using wordTrace_append hprefix tailTrace_6644318
  have hstable : (prefixWord ++ tailWord_6644318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644318).length < 2 ^ (prefixWord ++ tailWord_6644318).sum := by decide
  have hdescent : baseEnd_6644318 < baseStart_6644318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644332 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_6644332 : Nat := 118140960795 + 6644332 * 2 ^ 59
def prefixEnd_6644332 : Nat := 4983230072969 + 3 ^ 40 * 6644332 * 2
def baseEnd_6644332 : Nat := 3411735944049403254193279

theorem tailTrace_6644332 : CollatzResearch.WordTrace tailWord_6644332 prefixEnd_6644332 3411735944049403254193279 := by
  unfold tailWord_6644332
  simp only [CollatzResearch.WordTrace]
  refine ⟨121169348482363700203863625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161559131309818266938484833 121169348482363700203863625)
  ·
    refine ⟨90877011361772775152897719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121169348482363700203863625 90877011361772775152897719)
    ·
      refine ⟨136315517042659162729346579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90877011361772775152897719 136315517042659162729346579)
      ·
        refine ⟨204473275563988744094019869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136315517042659162729346579 204473275563988744094019869)
        ·
          refine ⟨76677478336495779035257451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204473275563988744094019869 76677478336495779035257451)
          ·
            refine ⟨115016217504743668552886177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76677478336495779035257451 115016217504743668552886177)
            ·
              refine ⟨86262163128557751414664633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115016217504743668552886177 86262163128557751414664633)
              ·
                refine ⟨64696622346418313560998475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86262163128557751414664633 64696622346418313560998475)
                ·
                  refine ⟨97044933519627470341497713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64696622346418313560998475 97044933519627470341497713)
                  ·
                    refine ⟨72783700139720602756123285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97044933519627470341497713 72783700139720602756123285)
                    ·
                      refine ⟨3411735944049403254193279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72783700139720602756123285 3411735944049403254193279)
                      ·
                        rfl

theorem cell23_6644332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_6644332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644332 prefixEnd_6644332 := by exact prefixLift 6644332
  have htrace : WordTrace (prefixWord ++ tailWord_6644332) baseStart_6644332 baseEnd_6644332 := by
    simpa [prefixWord, tailWord_6644332, baseEnd_6644332] using wordTrace_append hprefix tailTrace_6644332
  have hstable : (prefixWord ++ tailWord_6644332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644332).length < 2 ^ (prefixWord ++ tailWord_6644332).sum := by decide
  have hdescent : baseEnd_6644332 < baseStart_6644332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644379 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 8, 2]
def baseStart_6644379 : Nat := 118140960795 + 6644379 * 2 ^ 59
def prefixEnd_6644379 : Nat := 4983230072969 + 3 ^ 40 * 6644379 * 2
def baseEnd_6644379 : Nat := 3411760077640164570305563

theorem tailTrace_6644379 : CollatzResearch.WordTrace tailWord_6644379 prefixEnd_6644379 3411760077640164570305563 := by
  unfold tailWord_6644379
  simp only [CollatzResearch.WordTrace]
  refine ⟨242340411195557127434688191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161560274130371418289792127 242340411195557127434688191)
  ·
    refine ⟨363510616793335691152032287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242340411195557127434688191 363510616793335691152032287)
    ·
      refine ⟨545265925190003536728048431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363510616793335691152032287 545265925190003536728048431)
      ·
        refine ⟨817898887785005305092072647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545265925190003536728048431 817898887785005305092072647)
        ·
          refine ⟨1226848331677507957638108971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817898887785005305092072647 1226848331677507957638108971)
          ·
            refine ⟨1840272497516261936457163457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226848331677507957638108971 1840272497516261936457163457)
            ·
              refine ⟨1380204373137196452342872593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840272497516261936457163457 1380204373137196452342872593)
              ·
                refine ⟨1035153279852897339257154445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380204373137196452342872593 1035153279852897339257154445)
                ·
                  refine ⟨388182479944836502221432917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035153279852897339257154445 388182479944836502221432917)
                  ·
                    refine ⟨4549013436853552760407417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 388182479944836502221432917 4549013436853552760407417)
                    ·
                      refine ⟨3411760077640164570305563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549013436853552760407417 3411760077640164570305563)
                      ·
                        rfl

theorem cell23_6644379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8, 2].length) (baseStart_6644379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644379 prefixEnd_6644379 := by exact prefixLift 6644379
  have htrace : WordTrace (prefixWord ++ tailWord_6644379) baseStart_6644379 baseEnd_6644379 := by
    simpa [prefixWord, tailWord_6644379, baseEnd_6644379] using wordTrace_append hprefix tailTrace_6644379
  have hstable : (prefixWord ++ tailWord_6644379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644379).length < 2 ^ (prefixWord ++ tailWord_6644379).sum := by decide
  have hdescent : baseEnd_6644379 < baseStart_6644379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644389 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_6644389 : Nat := 118140960795 + 6644389 * 2 ^ 59
def prefixEnd_6644389 : Nat := 4983230072969 + 3 ^ 40 * 6644389 * 2
def baseEnd_6644389 : Nat := 1137255070815569843726839

theorem tailTrace_6644389 : CollatzResearch.WordTrace tailWord_6644389 prefixEnd_6644389 1137255070815569843726839 := by
  unfold tailWord_6644389
  simp only [CollatzResearch.WordTrace]
  refine ⟨242340775925520899142552221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161560517283680599428368147 242340775925520899142552221)
  ·
    refine ⟨90877790972070337178457083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242340775925520899142552221 90877790972070337178457083)
    ·
      refine ⟨136316686458105505767685625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90877790972070337178457083 136316686458105505767685625)
      ·
        refine ⟨102237514843579129325764219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136316686458105505767685625 102237514843579129325764219)
        ·
          refine ⟨153356272265368693988646329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102237514843579129325764219 153356272265368693988646329)
          ·
            refine ⟨115017204199026520491484747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153356272265368693988646329 115017204199026520491484747)
            ·
              refine ⟨172525806298539780737227121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115017204199026520491484747 172525806298539780737227121)
              ·
                refine ⟨129394354723904835552920341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172525806298539780737227121 129394354723904835552920341)
                ·
                  refine ⟨6065360377683039166543141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129394354723904835552920341 6065360377683039166543141)
                  ·
                    refine ⟨1137255070815569843726839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065360377683039166543141 1137255070815569843726839)
                    ·
                      rfl

theorem cell23_6644389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_6644389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644389 prefixEnd_6644389 := by exact prefixLift 6644389
  have htrace : WordTrace (prefixWord ++ tailWord_6644389) baseStart_6644389 baseEnd_6644389 := by
    simpa [prefixWord, tailWord_6644389, baseEnd_6644389] using wordTrace_append hprefix tailTrace_6644389
  have hstable : (prefixWord ++ tailWord_6644389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644389).length < 2 ^ (prefixWord ++ tailWord_6644389).sum := by decide
  have hdescent : baseEnd_6644389 < baseStart_6644389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644413 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6644413 : Nat := 118140960795 + 6644413 * 2 ^ 59
def prefixEnd_6644413 : Nat := 4983230072969 + 3 ^ 40 * 6644413 * 2
def baseEnd_6644413 : Nat := 3411777535982417437280407

theorem tailTrace_6644413 : CollatzResearch.WordTrace tailWord_6644413 prefixEnd_6644413 3411777535982417437280407 := by
  unfold tailWord_6644413
  simp only [CollatzResearch.WordTrace]
  refine ⟨242341651277433951241425893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161561100851622634160950595 242341651277433951241425893)
  ·
    refine ⟨45439059614518865857767355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242341651277433951241425893 45439059614518865857767355)
    ·
      refine ⟨68158589421778298786651033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45439059614518865857767355 68158589421778298786651033)
      ·
        refine ⟨51118942066333724089988275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68158589421778298786651033 51118942066333724089988275)
        ·
          refine ⟨76678413099500586134982413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51118942066333724089988275 76678413099500586134982413)
          ·
            refine ⟨28754404912312719800618405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76678413099500586134982413 28754404912312719800618405)
            ·
              refine ⟨5391450921058634962615951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28754404912312719800618405 5391450921058634962615951)
              ·
                refine ⟨8087176381587952443923927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391450921058634962615951 8087176381587952443923927)
                ·
                  refine ⟨12130764572381928665885891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8087176381587952443923927 12130764572381928665885891)
                  ·
                    refine ⟨18196146858572892998828837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12130764572381928665885891 18196146858572892998828837)
                    ·
                      refine ⟨3411777535982417437280407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18196146858572892998828837 3411777535982417437280407)
                      ·
                        rfl

theorem cell23_6644413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6644413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644413 prefixEnd_6644413 := by exact prefixLift 6644413
  have htrace : WordTrace (prefixWord ++ tailWord_6644413) baseStart_6644413 baseEnd_6644413 := by
    simpa [prefixWord, tailWord_6644413, baseEnd_6644413] using wordTrace_append hprefix tailTrace_6644413
  have hstable : (prefixWord ++ tailWord_6644413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644413).length < 2 ^ (prefixWord ++ tailWord_6644413).sum := by decide
  have hdescent : baseEnd_6644413 < baseStart_6644413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644430 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_6644430 : Nat := 118140960795 + 6644430 * 2 ^ 59
def prefixEnd_6644430 : Nat := 4983230072969 + 3 ^ 40 * 6644430 * 2
def baseEnd_6644430 : Nat := 3411786265153543870767829

theorem tailTrace_6644430 : CollatzResearch.WordTrace tailWord_6644430 prefixEnd_6644430 3411786265153543870767829 := by
  unfold tailWord_6644430
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292783914796545393099343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161561514212248242096529829 30292783914796545393099343)
  ·
    refine ⟨45439175872194818089649015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30292783914796545393099343 45439175872194818089649015)
    ·
      refine ⟨68158763808292227134473523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45439175872194818089649015 68158763808292227134473523)
      ·
        refine ⟨102238145712438340701710285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68158763808292227134473523 102238145712438340701710285)
        ·
          refine ⟨38339304642164377763141357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102238145712438340701710285 38339304642164377763141357)
          ·
            refine ⟨14377239240811641661178009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38339304642164377763141357 14377239240811641661178009)
            ·
              refine ⟨10782929430608731245883507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14377239240811641661178009 10782929430608731245883507)
              ·
                refine ⟨16174394145913096868825261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10782929430608731245883507 16174394145913096868825261)
                ·
                  refine ⟨6065397804717411325809473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16174394145913096868825261 6065397804717411325809473)
                  ·
                    refine ⟨4549048353538058494357105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065397804717411325809473 4549048353538058494357105)
                    ·
                      refine ⟨3411786265153543870767829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549048353538058494357105 3411786265153543870767829)
                      ·
                        rfl

theorem cell23_6644430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_6644430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644430 prefixEnd_6644430 := by exact prefixLift 6644430
  have htrace : WordTrace (prefixWord ++ tailWord_6644430) baseStart_6644430 baseEnd_6644430 := by
    simpa [prefixWord, tailWord_6644430, baseEnd_6644430] using wordTrace_append hprefix tailTrace_6644430
  have hstable : (prefixWord ++ tailWord_6644430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644430).length < 2 ^ (prefixWord ++ tailWord_6644430).sum := by decide
  have hdescent : baseEnd_6644430 < baseStart_6644430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644499 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_6644499 : Nat := 118140960795 + 6644499 * 2 ^ 59
def prefixEnd_6644499 : Nat := 4983230072969 + 3 ^ 40 * 6644499 * 2
def baseEnd_6644499 : Nat := 3411821695318704100805011

theorem tailTrace_6644499 : CollatzResearch.WordTrace tailWord_6644499 prefixEnd_6644499 3411821695318704100805011 := by
  unfold tailWord_6644499
  simp only [CollatzResearch.WordTrace]
  refine ⟨242344787955122387929056551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161563191970081591952704367 242344787955122387929056551)
  ·
    refine ⟨363517181932683581893584827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242344787955122387929056551 363517181932683581893584827)
    ·
      refine ⟨545275772899025372840377241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363517181932683581893584827 545275772899025372840377241)
      ·
        refine ⟨408956829674269029630282931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545275772899025372840377241 408956829674269029630282931)
        ·
          refine ⟨613435244511403544445424397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408956829674269029630282931 613435244511403544445424397)
          ·
            refine ⟨230038216691776329167034149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613435244511403544445424397 230038216691776329167034149)
            ·
              refine ⟨43132165629708061718818903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230038216691776329167034149 43132165629708061718818903)
              ·
                refine ⟨64698248444562092578228355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43132165629708061718818903 64698248444562092578228355)
                ·
                  refine ⟨97047372666843138867342533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64698248444562092578228355 97047372666843138867342533)
                  ·
                    refine ⟨18196382375033088537626725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97047372666843138867342533 18196382375033088537626725)
                    ·
                      refine ⟨3411821695318704100805011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18196382375033088537626725 3411821695318704100805011)
                      ·
                        rfl

theorem cell23_6644499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_6644499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644499 prefixEnd_6644499 := by exact prefixLift 6644499
  have htrace : WordTrace (prefixWord ++ tailWord_6644499) baseStart_6644499 baseEnd_6644499 := by
    simpa [prefixWord, tailWord_6644499, baseEnd_6644499] using wordTrace_append hprefix tailTrace_6644499
  have hstable : (prefixWord ++ tailWord_6644499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644499).length < 2 ^ (prefixWord ++ tailWord_6644499).sum := by decide
  have hdescent : baseEnd_6644499 < baseStart_6644499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644536 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_6644536 : Nat := 118140960795 + 6644536 * 2 ^ 59
def prefixEnd_6644536 : Nat := 4983230072969 + 3 ^ 40 * 6644536 * 2
def baseEnd_6644536 : Nat := 3411840694102920456042341

theorem tailTrace_6644536 : CollatzResearch.WordTrace tailWord_6644536 prefixEnd_6644536 3411840694102920456042341 := by
  unfold tailWord_6644536
  simp only [CollatzResearch.WordTrace]
  refine ⟨121173068727994171624076731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161564091637325562165435641 121173068727994171624076731)
  ·
    refine ⟨181759603091991257436115097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121173068727994171624076731 181759603091991257436115097)
    ·
      refine ⟨136319702318993443077086323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181759603091991257436115097 136319702318993443077086323)
      ·
        refine ⟨204479553478490164615629485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136319702318993443077086323 204479553478490164615629485)
        ·
          refine ⟨76679832554433811730861057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204479553478490164615629485 76679832554433811730861057)
          ·
            refine ⟨57509874415825358798145793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76679832554433811730861057 57509874415825358798145793)
            ·
              refine ⟨43132405811869019098609345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57509874415825358798145793 43132405811869019098609345)
              ·
                refine ⟨32349304358901764323957009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43132405811869019098609345 32349304358901764323957009)
                ·
                  refine ⟨24261978269176323242967757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32349304358901764323957009 24261978269176323242967757)
                  ·
                    refine ⟨9098241850941121216112909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24261978269176323242967757 9098241850941121216112909)
                    ·
                      refine ⟨3411840694102920456042341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098241850941121216112909 3411840694102920456042341)
                      ·
                        rfl

theorem cell23_6644536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_6644536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644536 prefixEnd_6644536 := by exact prefixLift 6644536
  have htrace : WordTrace (prefixWord ++ tailWord_6644536) baseStart_6644536 baseEnd_6644536 := by
    simpa [prefixWord, tailWord_6644536, baseEnd_6644536] using wordTrace_append hprefix tailTrace_6644536
  have hstable : (prefixWord ++ tailWord_6644536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644536).length < 2 ^ (prefixWord ++ tailWord_6644536).sum := by decide
  have hdescent : baseEnd_6644536 < baseStart_6644536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644543 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 5]
def baseStart_6644543 : Nat := 118140960795 + 6644543 * 2 ^ 59
def prefixEnd_6644543 : Nat := 4983230072969 + 3 ^ 40 * 6644543 * 2
def baseEnd_6644543 : Nat := 379093809829722436517201

theorem tailTrace_6644543 : CollatzResearch.WordTrace tailWord_6644543 prefixEnd_6644543 379093809829722436517201 := by
  unfold tailWord_6644543
  simp only [CollatzResearch.WordTrace]
  refine ⟨242346392766962983443658283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161564261844641988962438855 242346392766962983443658283)
  ·
    refine ⟨363519589150444475165487425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242346392766962983443658283 363519589150444475165487425)
    ·
      refine ⟨272639691862833356374115569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363519589150444475165487425 272639691862833356374115569)
      ·
        refine ⟨204479768897125017280586677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272639691862833356374115569 204479768897125017280586677)
        ·
          refine ⟨19169978334105470370055001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204479768897125017280586677 19169978334105470370055001)
          ·
            refine ⟨14377483750579102777541251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19169978334105470370055001 14377483750579102777541251)
            ·
              refine ⟨21566225625868654166311877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377483750579102777541251 21566225625868654166311877)
              ·
                refine ⟨4043667304850372656183477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21566225625868654166311877 4043667304850372656183477)
                ·
                  refine ⟨379093809829722436517201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4043667304850372656183477 379093809829722436517201)
                  ·
                    rfl

theorem cell23_6644543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 5].length) (baseStart_6644543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644543 prefixEnd_6644543 := by exact prefixLift 6644543
  have htrace : WordTrace (prefixWord ++ tailWord_6644543) baseStart_6644543 baseEnd_6644543 := by
    simpa [prefixWord, tailWord_6644543, baseEnd_6644543] using wordTrace_append hprefix tailTrace_6644543
  have hstable : (prefixWord ++ tailWord_6644543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644543).length < 2 ^ (prefixWord ++ tailWord_6644543).sum := by decide
  have hdescent : baseEnd_6644543 < baseStart_6644543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644549 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_6644549 : Nat := 118140960795 + 6644549 * 2 ^ 59
def prefixEnd_6644549 : Nat := 4983230072969 + 3 ^ 40 * 6644549 * 2
def baseEnd_6644549 : Nat := 3411847369351428905179781

theorem tailTrace_6644549 : CollatzResearch.WordTrace tailWord_6644549 prefixEnd_6644549 3411847369351428905179781 := by
  unfold tailWord_6644549
  simp only [CollatzResearch.WordTrace]
  refine ⟨242346611604941246468376701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161564407736627497645584467 242346611604941246468376701)
  ·
    refine ⟨90879979351852967425641263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242346611604941246468376701 90879979351852967425641263)
    ·
      refine ⟨136319969027779451138461895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90879979351852967425641263 136319969027779451138461895)
      ·
        refine ⟨204479953541669176707692843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136319969027779451138461895 204479953541669176707692843)
        ·
          refine ⟨306719930312503765061539265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204479953541669176707692843 306719930312503765061539265)
          ·
            refine ⟨230039947734377823796154449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306719930312503765061539265 230039947734377823796154449)
            ·
              refine ⟨172529960800783367847115837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230039947734377823796154449 172529960800783367847115837)
              ·
                refine ⟨64698735300293762942668439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172529960800783367847115837 64698735300293762942668439)
                ·
                  refine ⟨97048102950440644414002659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64698735300293762942668439 97048102950440644414002659)
                  ·
                    refine ⟨145572154425660966621003989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97048102950440644414002659 145572154425660966621003989)
                    ·
                      refine ⟨3411847369351428905179781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145572154425660966621003989 3411847369351428905179781)
                      ·
                        rfl

theorem cell23_6644549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_6644549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644549 prefixEnd_6644549 := by exact prefixLift 6644549
  have htrace : WordTrace (prefixWord ++ tailWord_6644549) baseStart_6644549 baseEnd_6644549 := by
    simpa [prefixWord, tailWord_6644549, baseEnd_6644549] using wordTrace_append hprefix tailTrace_6644549
  have hstable : (prefixWord ++ tailWord_6644549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644549).length < 2 ^ (prefixWord ++ tailWord_6644549).sum := by decide
  have hdescent : baseEnd_6644549 < baseStart_6644549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644576 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_6644576 : Nat := 118140960795 + 6644576 * 2 ^ 59
def prefixEnd_6644576 : Nat := 4983230072969 + 3 ^ 40 * 6644576 * 2
def baseEnd_6644576 : Nat := 3411861233329100299542157

theorem tailTrace_6644576 : CollatzResearch.WordTrace tailWord_6644576 prefixEnd_6644576 3411861233329100299542157 := by
  unfold tailWord_6644576
  simp only [CollatzResearch.WordTrace]
  refine ⟨121173798187921715039804791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161565064250562286719739721 121173798187921715039804791)
  ·
    refine ⟨181760697281882572559707187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121173798187921715039804791 181760697281882572559707187)
    ·
      refine ⟨272641045922823858839560781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181760697281882572559707187 272641045922823858839560781)
      ·
        refine ⟨102240392221058947064835293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272641045922823858839560781 102240392221058947064835293)
        ·
          refine ⟨38340147082897105149313235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102240392221058947064835293 38340147082897105149313235)
          ·
            refine ⟨57510220624345657723969853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38340147082897105149313235 57510220624345657723969853)
            ·
              refine ⟨21566332734129621646488695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57510220624345657723969853 21566332734129621646488695)
              ·
                refine ⟨32349499101194432469733043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21566332734129621646488695 32349499101194432469733043)
                ·
                  refine ⟨48524248651791648704599565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32349499101194432469733043 48524248651791648704599565)
                  ·
                    refine ⟨18196593244421868264224837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48524248651791648704599565 18196593244421868264224837)
                    ·
                      refine ⟨3411861233329100299542157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18196593244421868264224837 3411861233329100299542157)
                      ·
                        rfl

theorem cell23_6644576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_6644576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644576 prefixEnd_6644576 := by exact prefixLift 6644576
  have htrace : WordTrace (prefixWord ++ tailWord_6644576) baseStart_6644576 baseEnd_6644576 := by
    simpa [prefixWord, tailWord_6644576, baseEnd_6644576] using wordTrace_append hprefix tailTrace_6644576
  have hstable : (prefixWord ++ tailWord_6644576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644576).length < 2 ^ (prefixWord ++ tailWord_6644576).sum := by decide
  have hdescent : baseEnd_6644576 < baseStart_6644576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644593 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_6644593 : Nat := 118140960795 + 6644593 * 2 ^ 59
def prefixEnd_6644593 : Nat := 4983230072969 + 3 ^ 40 * 6644593 * 2
def baseEnd_6644593 : Nat := 3411869962500226733029579

theorem tailTrace_6644593 : CollatzResearch.WordTrace tailWord_6644593 prefixEnd_6644593 3411869962500226733029579 := by
  unfold tailWord_6644593
  simp only [CollatzResearch.WordTrace]
  refine ⟨242348216416781841982978433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161565477611187894655318955 242348216416781841982978433)
  ·
    refine ⟨181761162312586381487233825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242348216416781841982978433 181761162312586381487233825)
    ·
      refine ⟨136320871734439786115425369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181761162312586381487233825 136320871734439786115425369)
      ·
        refine ⟨102240653800829839586569027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136320871734439786115425369 102240653800829839586569027)
        ·
          refine ⟨153360980701244759379853541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102240653800829839586569027 153360980701244759379853541)
          ·
            refine ⟨28755183881483392383722539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153360980701244759379853541 28755183881483392383722539)
            ·
              refine ⟨43132775822225088575583809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28755183881483392383722539 43132775822225088575583809)
              ·
                refine ⟨32349581866668816431687857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43132775822225088575583809 32349581866668816431687857)
                ·
                  refine ⟨24262186400001612323765893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32349581866668816431687857 24262186400001612323765893)
                  ·
                    refine ⟨4549159950000302310706105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24262186400001612323765893 4549159950000302310706105)
                    ·
                      refine ⟨3411869962500226733029579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549159950000302310706105 3411869962500226733029579)
                      ·
                        rfl

theorem cell23_6644593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_6644593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644593 prefixEnd_6644593 := by exact prefixLift 6644593
  have htrace : WordTrace (prefixWord ++ tailWord_6644593) baseStart_6644593 baseEnd_6644593 := by
    simpa [prefixWord, tailWord_6644593, baseEnd_6644593] using wordTrace_append hprefix tailTrace_6644593
  have hstable : (prefixWord ++ tailWord_6644593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644593).length < 2 ^ (prefixWord ++ tailWord_6644593).sum := by decide
  have hdescent : baseEnd_6644593 < baseStart_6644593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644643 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 3]
def baseStart_6644643 : Nat := 118140960795 + 6644643 * 2 ^ 59
def prefixEnd_6644643 : Nat := 4983230072969 + 3 ^ 40 * 6644643 * 2
def baseEnd_6644643 : Nat := 3411895636532951537404349

theorem tailTrace_6644643 : CollatzResearch.WordTrace tailWord_6644643 prefixEnd_6644643 3411895636532951537404349 := by
  unfold tailWord_6644643
  simp only [CollatzResearch.WordTrace]
  refine ⟨242350040066600700522298583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161566693377733800348199055 242350040066600700522298583)
  ·
    refine ⟨363525060099901050783447875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242350040066600700522298583 363525060099901050783447875)
    ·
      refine ⟨545287590149851576175171813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363525060099901050783447875 545287590149851576175171813)
      ·
        refine ⟨102241423153097170532844715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545287590149851576175171813 102241423153097170532844715)
        ·
          refine ⟨153362134729645755799267073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102241423153097170532844715 153362134729645755799267073)
          ·
            refine ⟨115021601047234316849450305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153362134729645755799267073 115021601047234316849450305)
            ·
              refine ⟨86266200785425737637087729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115021601047234316849450305 86266200785425737637087729)
              ·
                refine ⟨64699650589069303227815797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86266200785425737637087729 64699650589069303227815797)
                ·
                  refine ⟨6065592242725247177607731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64699650589069303227815797 6065592242725247177607731)
                  ·
                    refine ⟨9098388364087870766411597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065592242725247177607731 9098388364087870766411597)
                    ·
                      refine ⟨3411895636532951537404349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098388364087870766411597 3411895636532951537404349)
                      ·
                        rfl

theorem cell23_6644643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_6644643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644643 prefixEnd_6644643 := by exact prefixLift 6644643
  have htrace : WordTrace (prefixWord ++ tailWord_6644643) baseStart_6644643 baseEnd_6644643 := by
    simpa [prefixWord, tailWord_6644643, baseEnd_6644643] using wordTrace_append hprefix tailTrace_6644643
  have hstable : (prefixWord ++ tailWord_6644643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644643).length < 2 ^ (prefixWord ++ tailWord_6644643).sum := by decide
  have hdescent : baseEnd_6644643 < baseStart_6644643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644670 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_6644670 : Nat := 118140960795 + 6644670 * 2 ^ 59
def prefixEnd_6644670 : Nat := 4983230072969 + 3 ^ 40 * 6644670 * 2
def baseEnd_6644670 : Nat := 3411909500510622931766725

theorem tailTrace_6644670 : CollatzResearch.WordTrace tailWord_6644670 prefixEnd_6644670 3411909500510622931766725 := by
  unfold tailWord_6644670
  simp only [CollatzResearch.WordTrace]
  refine ⟨30293878104687860516691433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161567349891668589422354309 30293878104687860516691433)
  ·
    refine ⟨22720408578515895387518575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30293878104687860516691433 22720408578515895387518575)
    ·
      refine ⟨34080612867773843081277863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22720408578515895387518575 34080612867773843081277863)
      ·
        refine ⟨51120919301660764621916795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34080612867773843081277863 51120919301660764621916795)
        ·
          refine ⟨76681378952491146932875193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51120919301660764621916795 76681378952491146932875193)
          ·
            refine ⟨57511034214368360199656395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76681378952491146932875193 57511034214368360199656395)
            ·
              refine ⟨86266551321552540299484593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57511034214368360199656395 86266551321552540299484593)
              ·
                refine ⟨64699913491164405224613445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86266551321552540299484593 64699913491164405224613445)
                ·
                  refine ⟨12131233779593325979615021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64699913491164405224613445 12131233779593325979615021)
                  ·
                    refine ⟨4549212667347497242355633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12131233779593325979615021 4549212667347497242355633)
                    ·
                      refine ⟨3411909500510622931766725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549212667347497242355633 3411909500510622931766725)
                      ·
                        rfl

theorem cell23_6644670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_6644670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644670 prefixEnd_6644670 := by exact prefixLift 6644670
  have htrace : WordTrace (prefixWord ++ tailWord_6644670) baseStart_6644670 baseEnd_6644670 := by
    simpa [prefixWord, tailWord_6644670, baseEnd_6644670] using wordTrace_append hprefix tailTrace_6644670
  have hstable : (prefixWord ++ tailWord_6644670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644670).length < 2 ^ (prefixWord ++ tailWord_6644670).sum := by decide
  have hdescent : baseEnd_6644670 < baseStart_6644670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644683 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4]
def baseStart_6644683 : Nat := 118140960795 + 6644683 * 2 ^ 59
def prefixEnd_6644683 : Nat := 4983230072969 + 3 ^ 40 * 6644683 * 2
def baseEnd_6644683 : Nat := 3411916175759131380904165

theorem tailTrace_6644683 : CollatzResearch.WordTrace tailWord_6644683 prefixEnd_6644683 3411916175759131380904165 := by
  unfold tailWord_6644683
  simp only [CollatzResearch.WordTrace]
  refine ⟨242351498986455787353754703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161567665990970524902503135 242351498986455787353754703)
  ·
    refine ⟨363527248479683681030632055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242351498986455787353754703 363527248479683681030632055)
    ·
      refine ⟨545290872719525521545948083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363527248479683681030632055 545290872719525521545948083)
      ·
        refine ⟨817936309079288282318922125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545290872719525521545948083 817936309079288282318922125)
        ·
          refine ⟨306726115904733105869595797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 817936309079288282318922125 306726115904733105869595797)
          ·
            refine ⟨14377786683034364337637303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 306726115904733105869595797 14377786683034364337637303)
            ·
              refine ⟨21566680024551546506455955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377786683034364337637303 21566680024551546506455955)
              ·
                refine ⟨32350020036827319759683933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21566680024551546506455955 32350020036827319759683933)
                ·
                  refine ⟨12131257513810244909881475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32350020036827319759683933 12131257513810244909881475)
                  ·
                    refine ⟨18196886270715367364822213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12131257513810244909881475 18196886270715367364822213)
                    ·
                      refine ⟨3411916175759131380904165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18196886270715367364822213 3411916175759131380904165)
                      ·
                        rfl

theorem cell23_6644683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 4].length) (baseStart_6644683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644683 prefixEnd_6644683 := by exact prefixLift 6644683
  have htrace : WordTrace (prefixWord ++ tailWord_6644683) baseStart_6644683 baseEnd_6644683 := by
    simpa [prefixWord, tailWord_6644683, baseEnd_6644683] using wordTrace_append hprefix tailTrace_6644683
  have hstable : (prefixWord ++ tailWord_6644683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644683).length < 2 ^ (prefixWord ++ tailWord_6644683).sum := by decide
  have hdescent : baseEnd_6644683 < baseStart_6644683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644711 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6644711 : Nat := 118140960795 + 6644711 * 2 ^ 59
def prefixEnd_6644711 : Nat := 4983230072969 + 3 ^ 40 * 6644711 * 2
def baseEnd_6644711 : Nat := 3411930553217457271354037

theorem tailTrace_6644711 : CollatzResearch.WordTrace tailWord_6644711 prefixEnd_6644711 3411930553217457271354037 := by
  unfold tailWord_6644711
  simp only [CollatzResearch.WordTrace]
  refine ⟨242352520230354348135773987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161568346820236232090515991 242352520230354348135773987)
  ·
    refine ⟨363528780345531522203660981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242352520230354348135773987 363528780345531522203660981)
    ·
      refine ⟨34080823157393580206593217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 363528780345531522203660981 34080823157393580206593217)
      ·
        refine ⟨25560617368045185154944913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34080823157393580206593217 25560617368045185154944913)
        ·
          refine ⟨19170463026033888866208685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25560617368045185154944913 19170463026033888866208685)
          ·
            refine ⟨7188923634762708324828257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19170463026033888866208685 7188923634762708324828257)
            ·
              refine ⟨5391692726072031243621193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188923634762708324828257 5391692726072031243621193)
              ·
                refine ⟨4043769544554023432715895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5391692726072031243621193 4043769544554023432715895)
                ·
                  refine ⟨6065654316831035149073843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043769544554023432715895 6065654316831035149073843)
                  ·
                    refine ⟨9098481475246552723610765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065654316831035149073843 9098481475246552723610765)
                    ·
                      refine ⟨3411930553217457271354037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098481475246552723610765 3411930553217457271354037)
                      ·
                        rfl

theorem cell23_6644711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6644711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644711 prefixEnd_6644711 := by exact prefixLift 6644711
  have htrace : WordTrace (prefixWord ++ tailWord_6644711) baseStart_6644711 baseEnd_6644711 := by
    simpa [prefixWord, tailWord_6644711, baseEnd_6644711] using wordTrace_append hprefix tailTrace_6644711
  have hstable : (prefixWord ++ tailWord_6644711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644711).length < 2 ^ (prefixWord ++ tailWord_6644711).sum := by decide
  have hdescent : baseEnd_6644711 < baseStart_6644711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644738 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6644738 : Nat := 118140960795 + 6644738 * 2 ^ 59
def prefixEnd_6644738 : Nat := 4983230072969 + 3 ^ 40 * 6644738 * 2
def baseEnd_6644738 : Nat := 3411944417195128665716413

theorem tailTrace_6644738 : CollatzResearch.WordTrace tailWord_6644738 prefixEnd_6644738 3411944417195128665716413 := by
  unfold tailWord_6644738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60588376250314132936751717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161569003334171021164671245 60588376250314132936751717)
  ·
    refine ⟨11360320546933899925640947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60588376250314132936751717 11360320546933899925640947)
    ·
      refine ⟨17040480820400849888461421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11360320546933899925640947 17040480820400849888461421)
      ·
        refine ⟨6390180307650318708173033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17040480820400849888461421 6390180307650318708173033)
        ·
          refine ⟨4792635230737739031129775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390180307650318708173033 4792635230737739031129775)
          ·
            refine ⟨7188952846106608546694663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792635230737739031129775 7188952846106608546694663)
            ·
              refine ⟨10783429269159912820041995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188952846106608546694663 10783429269159912820041995)
              ·
                refine ⟨16175143903739869230062993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10783429269159912820041995 16175143903739869230062993)
                ·
                  refine ⟨12131357927804901922547245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16175143903739869230062993 12131357927804901922547245)
                  ·
                    refine ⟨4549259222926838220955217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12131357927804901922547245 4549259222926838220955217)
                    ·
                      refine ⟨3411944417195128665716413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549259222926838220955217 3411944417195128665716413)
                      ·
                        rfl

theorem cell23_6644738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6644738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644738 prefixEnd_6644738 := by exact prefixLift 6644738
  have htrace : WordTrace (prefixWord ++ tailWord_6644738) baseStart_6644738 baseEnd_6644738 := by
    simpa [prefixWord, tailWord_6644738, baseEnd_6644738] using wordTrace_append hprefix tailTrace_6644738
  have hstable : (prefixWord ++ tailWord_6644738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644738).length < 2 ^ (prefixWord ++ tailWord_6644738).sum := by decide
  have hdescent : baseEnd_6644738 < baseStart_6644738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644750 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6644750 : Nat := 118140960795 + 6644750 * 2 ^ 59
def prefixEnd_6644750 : Nat := 4983230072969 + 3 ^ 40 * 6644750 * 2
def baseEnd_6644750 : Nat := 3411950578962982618766357

theorem tailTrace_6644750 : CollatzResearch.WordTrace tailWord_6644750 prefixEnd_6644750 3411950578962982618766357 := by
  unfold tailWord_6644750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30294242834651632224555463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161569295118142038530962469 30294242834651632224555463)
  ·
    refine ⟨45441364251977448336833195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30294242834651632224555463 45441364251977448336833195)
    ·
      refine ⟨68162046377966172505249793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45441364251977448336833195 68162046377966172505249793)
      ·
        refine ⟨51121534783474629378937345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68162046377966172505249793 51121534783474629378937345)
        ·
          refine ⟨38341151087605972034203009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51121534783474629378937345 38341151087605972034203009)
          ·
            refine ⟨28755863315704479025652257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38341151087605972034203009 28755863315704479025652257)
            ·
              refine ⟨21566897486778359269239193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28755863315704479025652257 21566897486778359269239193)
              ·
                refine ⟨16175173115083769451929395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21566897486778359269239193 16175173115083769451929395)
                ·
                  refine ⟨24262759672625654177894093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16175173115083769451929395 24262759672625654177894093)
                  ·
                    refine ⟨9098534877234620316710285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24262759672625654177894093 9098534877234620316710285)
                    ·
                      refine ⟨3411950578962982618766357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098534877234620316710285 3411950578962982618766357)
                      ·
                        rfl

theorem cell23_6644750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6644750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644750 prefixEnd_6644750 := by exact prefixLift 6644750
  have htrace : WordTrace (prefixWord ++ tailWord_6644750) baseStart_6644750 baseEnd_6644750 := by
    simpa [prefixWord, tailWord_6644750, baseEnd_6644750] using wordTrace_append hprefix tailTrace_6644750
  have hstable : (prefixWord ++ tailWord_6644750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644750).length < 2 ^ (prefixWord ++ tailWord_6644750).sum := by decide
  have hdescent : baseEnd_6644750 < baseStart_6644750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644767 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 3]
def baseStart_6644767 : Nat := 118140960795 + 6644767 * 2 ^ 59
def prefixEnd_6644767 : Nat := 4983230072969 + 3 ^ 40 * 6644767 * 2
def baseEnd_6644767 : Nat := 3411959308134109052253779

theorem tailTrace_6644767 : CollatzResearch.WordTrace tailWord_6644767 prefixEnd_6644767 3411959308134109052253779 := by
  unfold tailWord_6644767
  simp only [CollatzResearch.WordTrace]
  refine ⟨242354562718151469699812555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161569708478767646466541703 242354562718151469699812555)
  ·
    refine ⟨363531844077227204549718833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242354562718151469699812555 363531844077227204549718833)
    ·
      refine ⟨272648883057920403412289125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363531844077227204549718833 272648883057920403412289125)
      ·
        refine ⟨51121665573360075639804211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272648883057920403412289125 51121665573360075639804211)
        ·
          refine ⟨76682498360040113459706317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51121665573360075639804211 76682498360040113459706317)
          ·
            refine ⟨28755936885015042547389869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76682498360040113459706317 28755936885015042547389869)
            ·
              refine ⟨10783476331880640955271201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28755936885015042547389869 10783476331880640955271201)
              ·
                refine ⟨8087607248910480716453401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10783476331880640955271201 8087607248910480716453401)
                ·
                  refine ⟨6065705436682860537340051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087607248910480716453401 6065705436682860537340051)
                  ·
                    refine ⟨9098558155024290806010077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065705436682860537340051 9098558155024290806010077)
                    ·
                      refine ⟨3411959308134109052253779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098558155024290806010077 3411959308134109052253779)
                      ·
                        rfl

theorem cell23_6644767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_6644767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644767 prefixEnd_6644767 := by exact prefixLift 6644767
  have htrace : WordTrace (prefixWord ++ tailWord_6644767) baseStart_6644767 baseEnd_6644767 := by
    simpa [prefixWord, tailWord_6644767, baseEnd_6644767] using wordTrace_append hprefix tailTrace_6644767
  have hstable : (prefixWord ++ tailWord_6644767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644767).length < 2 ^ (prefixWord ++ tailWord_6644767).sum := by decide
  have hdescent : baseEnd_6644767 < baseStart_6644767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644807 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_6644807 : Nat := 118140960795 + 6644807 * 2 ^ 59
def prefixEnd_6644807 : Nat := 4983230072969 + 3 ^ 40 * 6644807 * 2
def baseEnd_6644807 : Nat := 3411979847360288895753595

theorem tailTrace_6644807 : CollatzResearch.WordTrace tailWord_6644807 prefixEnd_6644807 3411979847360288895753595 := by
  unfold tailWord_6644807
  simp only [CollatzResearch.WordTrace]
  refine ⟨242356021638006556531268675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161570681092004371020845783 242356021638006556531268675)
  ·
    refine ⟨363534032457009834796903013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242356021638006556531268675 363534032457009834796903013)
    ·
      refine ⟨68162631085689344024419315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 363534032457009834796903013 68162631085689344024419315)
      ·
        refine ⟨102243946628534016036628973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68162631085689344024419315 102243946628534016036628973)
        ·
          refine ⟨38341479985700256013735865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102243946628534016036628973 38341479985700256013735865)
          ·
            refine ⟨28756109989275192010301899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38341479985700256013735865 28756109989275192010301899)
            ·
              refine ⟨43134164983912788015452849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28756109989275192010301899 43134164983912788015452849)
              ·
                refine ⟨32350623737934591011589637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43134164983912788015452849 32350623737934591011589637)
                ·
                  refine ⟨6065741950862735814673057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32350623737934591011589637 6065741950862735814673057)
                  ·
                    refine ⟨4549306463147051861004793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065741950862735814673057 4549306463147051861004793)
                    ·
                      refine ⟨3411979847360288895753595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549306463147051861004793 3411979847360288895753595)
                      ·
                        rfl

theorem cell23_6644807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_6644807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644807 prefixEnd_6644807 := by exact prefixLift 6644807
  have htrace : WordTrace (prefixWord ++ tailWord_6644807) baseStart_6644807 baseEnd_6644807 := by
    simpa [prefixWord, tailWord_6644807, baseEnd_6644807] using wordTrace_append hprefix tailTrace_6644807
  have hstable : (prefixWord ++ tailWord_6644807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644807).length < 2 ^ (prefixWord ++ tailWord_6644807).sum := by decide
  have hdescent : baseEnd_6644807 < baseStart_6644807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644841 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 2, 2, 2]
def baseStart_6644841 : Nat := 118140960795 + 6644841 * 2 ^ 59
def prefixEnd_6644841 : Nat := 4983230072969 + 3 ^ 40 * 6644841 * 2
def baseEnd_6644841 : Nat := 3411997305702541762728439

theorem tailTrace_6644841 : CollatzResearch.WordTrace tailWord_6644841 prefixEnd_6644841 3411997305702541762728439 := by
  unfold tailWord_6644841
  simp only [CollatzResearch.WordTrace]
  refine ⟨242357261719883380338006377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161571507813255586892004251 242357261719883380338006377)
  ·
    refine ⟨181767946289912535253504783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242357261719883380338006377 181767946289912535253504783)
    ·
      refine ⟨272651919434868802880257175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181767946289912535253504783 272651919434868802880257175)
      ·
        refine ⟨408977879152303204320385763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272651919434868802880257175 408977879152303204320385763)
        ·
          refine ⟨613466818728454806480578645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408977879152303204320385763 613466818728454806480578645)
          ·
            refine ⟨7189064281974079763444281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 613466818728454806480578645 7189064281974079763444281)
            ·
              refine ⟨5391798211480559822583211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7189064281974079763444281 5391798211480559822583211)
              ·
                refine ⟨8087697317220839733874817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391798211480559822583211 8087697317220839733874817)
                ·
                  refine ⟨6065772987915629800406113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087697317220839733874817 6065772987915629800406113)
                  ·
                    refine ⟨4549329740936722350304585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065772987915629800406113 4549329740936722350304585)
                    ·
                      refine ⟨3411997305702541762728439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549329740936722350304585 3411997305702541762728439)
                      ·
                        rfl

theorem cell23_6644841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 2, 2].length) (baseStart_6644841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644841 prefixEnd_6644841 := by exact prefixLift 6644841
  have htrace : WordTrace (prefixWord ++ tailWord_6644841) baseStart_6644841 baseEnd_6644841 := by
    simpa [prefixWord, tailWord_6644841, baseEnd_6644841] using wordTrace_append hprefix tailTrace_6644841
  have hstable : (prefixWord ++ tailWord_6644841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644841).length < 2 ^ (prefixWord ++ tailWord_6644841).sum := by decide
  have hdescent : baseEnd_6644841 < baseStart_6644841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644860 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_6644860 : Nat := 118140960795 + 6644860 * 2 ^ 59
def prefixEnd_6644860 : Nat := 4983230072969 + 3 ^ 40 * 6644860 * 2
def baseEnd_6644860 : Nat := 1137335687278325729463617

theorem tailTrace_6644860 : CollatzResearch.WordTrace tailWord_6644860 prefixEnd_6644860 1137335687278325729463617 := by
  unfold tailWord_6644860
  simp only [CollatzResearch.WordTrace]
  refine ⟨121178977353407273291474017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161571969804543031055298689 121178977353407273291474017)
  ·
    refine ⟨90884233015055454968605513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121178977353407273291474017 90884233015055454968605513)
    ·
      refine ⟨68163174761291591226454135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90884233015055454968605513 68163174761291591226454135)
      ·
        refine ⟨102244762141937386839681203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68163174761291591226454135 102244762141937386839681203)
        ·
          refine ⟨153367143212906080259521805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102244762141937386839681203 153367143212906080259521805)
          ·
            refine ⟨57512678704839780097320677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153367143212906080259521805 57512678704839780097320677)
            ·
              refine ⟨10783627257157458768247627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57512678704839780097320677 10783627257157458768247627)
              ·
                refine ⟨16175440885736188152371441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10783627257157458768247627 16175440885736188152371441)
                ·
                  refine ⟨12131580664302141114278581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16175440885736188152371441 12131580664302141114278581)
                  ·
                    refine ⟨1137335687278325729463617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12131580664302141114278581 1137335687278325729463617)
                    ·
                      rfl

theorem cell23_6644860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_6644860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644860 prefixEnd_6644860 := by exact prefixLift 6644860
  have htrace : WordTrace (prefixWord ++ tailWord_6644860) baseStart_6644860 baseEnd_6644860 := by
    simpa [prefixWord, tailWord_6644860, baseEnd_6644860] using wordTrace_append hprefix tailTrace_6644860
  have hstable : (prefixWord ++ tailWord_6644860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644860).length < 2 ^ (prefixWord ++ tailWord_6644860).sum := by decide
  have hdescent : baseEnd_6644860 < baseStart_6644860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644897 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6644897 : Nat := 118140960795 + 6644897 * 2 ^ 59
def prefixEnd_6644897 : Nat := 4983230072969 + 3 ^ 40 * 6644897 * 2
def baseEnd_6644897 : Nat := 3412026060619193543628181

theorem tailTrace_6644897 : CollatzResearch.WordTrace tailWord_6644897 prefixEnd_6644897 3412026060619193543628181 := by
  unfold tailWord_6644897
  simp only [CollatzResearch.WordTrace]
  refine ⟨242359304207680501902044945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161572869471787001268029963 242359304207680501902044945)
  ·
    refine ⟨181769478155760376426533709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242359304207680501902044945 181769478155760376426533709)
    ·
      refine ⟨68163554308410141159950141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181769478155760376426533709 68163554308410141159950141)
      ·
        refine ⟨25561332865653802934981303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68163554308410141159950141 25561332865653802934981303)
        ·
          refine ⟨38341999298480704402471955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25561332865653802934981303 38341999298480704402471955)
          ·
            refine ⟨57512998947721056603707933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38341999298480704402471955 57512998947721056603707933)
            ·
              refine ⟨21567374605395396226390475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57512998947721056603707933 21567374605395396226390475)
              ·
                refine ⟨32351061908093094339585713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21567374605395396226390475 32351061908093094339585713)
                ·
                  refine ⟨24263296431069820754689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32351061908093094339585713 24263296431069820754689285)
                  ·
                    refine ⟨4549368080825591391504241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24263296431069820754689285 4549368080825591391504241)
                    ·
                      refine ⟨3412026060619193543628181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549368080825591391504241 3412026060619193543628181)
                      ·
                        rfl

theorem cell23_6644897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6644897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644897 prefixEnd_6644897 := by exact prefixLift 6644897
  have htrace : WordTrace (prefixWord ++ tailWord_6644897) baseStart_6644897 baseEnd_6644897 := by
    simpa [prefixWord, tailWord_6644897, baseEnd_6644897] using wordTrace_append hprefix tailTrace_6644897
  have hstable : (prefixWord ++ tailWord_6644897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644897).length < 2 ^ (prefixWord ++ tailWord_6644897).sum := by decide
  have hdescent : baseEnd_6644897 < baseStart_6644897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644924 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_6644924 : Nat := 118140960795 + 6644924 * 2 ^ 59
def prefixEnd_6644924 : Nat := 4983230072969 + 3 ^ 40 * 6644924 * 2
def baseEnd_6644924 : Nat := 1137346641532288312663519

theorem tailTrace_6644924 : CollatzResearch.WordTrace tailWord_6644924 prefixEnd_6644924 1137346641532288312663519 := by
  unfold tailWord_6644924
  simp only [CollatzResearch.WordTrace]
  refine ⟨121180144489291342756638913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161573525985721790342185217 121180144489291342756638913)
  ·
    refine ⟨90885108366968507067479185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121180144489291342756638913 90885108366968507067479185)
    ·
      refine ⟨68163831275226380300609389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90885108366968507067479185 68163831275226380300609389)
      ·
        refine ⟨25561436728209892612728521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68163831275226380300609389 25561436728209892612728521)
        ·
          refine ⟨19171077546157419459546391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25561436728209892612728521 19171077546157419459546391)
          ·
            refine ⟨28756616319236129189319587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19171077546157419459546391 28756616319236129189319587)
            ·
              refine ⟨43134924478854193783979381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28756616319236129189319587 43134924478854193783979381)
              ·
                refine ⟨4043899169892580667248067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43134924478854193783979381 4043899169892580667248067)
                ·
                  refine ⟨6065848754838871000872101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043899169892580667248067 6065848754838871000872101)
                  ·
                    refine ⟨1137346641532288312663519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065848754838871000872101 1137346641532288312663519)
                    ·
                      rfl

theorem cell23_6644924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_6644924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644924 prefixEnd_6644924 := by exact prefixLift 6644924
  have htrace : WordTrace (prefixWord ++ tailWord_6644924) baseStart_6644924 baseEnd_6644924 := by
    simpa [prefixWord, tailWord_6644924, baseEnd_6644924] using wordTrace_append hprefix tailTrace_6644924
  have hstable : (prefixWord ++ tailWord_6644924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644924).length < 2 ^ (prefixWord ++ tailWord_6644924).sum := by decide
  have hdescent : baseEnd_6644924 < baseStart_6644924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644943 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_6644943 : Nat := 118140960795 + 6644943 * 2 ^ 59
def prefixEnd_6644943 : Nat := 4983230072969 + 3 ^ 40 * 6644943 * 2
def baseEnd_6644943 : Nat := 3412049680729300363652969

theorem tailTrace_6644943 : CollatzResearch.WordTrace tailWord_6644943 prefixEnd_6644943 3412049680729300363652969 := by
  unfold tailWord_6644943
  simp only [CollatzResearch.WordTrace]
  refine ⟨242360981965513851758219483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161573987977009234505479655 242360981965513851758219483)
  ·
    refine ⟨363541472948270777637329225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242360981965513851758219483 363541472948270777637329225)
    ·
      refine ⟨272656104711203083227996919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363541472948270777637329225 272656104711203083227996919)
      ·
        refine ⟨408984157066804624841995379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272656104711203083227996919 408984157066804624841995379)
        ·
          refine ⟨613476235600206937262993069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408984157066804624841995379 613476235600206937262993069)
          ·
            refine ⟨230053588350077601473622401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613476235600206937262993069 230053588350077601473622401)
            ·
              refine ⟨172540191262558201105216801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230053588350077601473622401 172540191262558201105216801)
              ·
                refine ⟨129405143446918650828912601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172540191262558201105216801 129405143446918650828912601)
                ·
                  refine ⟨97053857585188988121684451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129405143446918650828912601 97053857585188988121684451)
                  ·
                    refine ⟨145580786377783482182526677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97053857585188988121684451 145580786377783482182526677)
                    ·
                      refine ⟨3412049680729300363652969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145580786377783482182526677 3412049680729300363652969)
                      ·
                        rfl

theorem cell23_6644943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_6644943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644943 prefixEnd_6644943 := by exact prefixLift 6644943
  have htrace : WordTrace (prefixWord ++ tailWord_6644943) baseStart_6644943 baseEnd_6644943 := by
    simpa [prefixWord, tailWord_6644943, baseEnd_6644943] using wordTrace_append hprefix tailTrace_6644943
  have hstable : (prefixWord ++ tailWord_6644943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644943).length < 2 ^ (prefixWord ++ tailWord_6644943).sum := by decide
  have hdescent : baseEnd_6644943 < baseStart_6644943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6644997 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_6644997 : Nat := 118140960795 + 6644997 * 2 ^ 59
def prefixEnd_6644997 : Nat := 4983230072969 + 3 ^ 40 * 6644997 * 2
def baseEnd_6644997 : Nat := 1137359136228214384125907

theorem tailTrace_6644997 : CollatzResearch.WordTrace tailWord_6644997 prefixEnd_6644997 1137359136228214384125907 := by
  unfold tailWord_6644997
  simp only [CollatzResearch.WordTrace]
  refine ⟨242362951507318218980685245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161575301004878812653790163 242362951507318218980685245)
  ·
    refine ⟨90886106815244332117756967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242362951507318218980685245 90886106815244332117756967)
    ·
      refine ⟨136329160222866498176635451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90886106815244332117756967 136329160222866498176635451)
      ·
        refine ⟨204493740334299747264953177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136329160222866498176635451 204493740334299747264953177)
        ·
          refine ⟨153370305250724810448714883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204493740334299747264953177 153370305250724810448714883)
          ·
            refine ⟨230055457876087215673072325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153370305250724810448714883 230055457876087215673072325)
            ·
              refine ⟨43135398351766352938701061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230055457876087215673072325 43135398351766352938701061)
              ·
                refine ⟨8087887190956191176006449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43135398351766352938701061 8087887190956191176006449)
                ·
                  refine ⟨6065915393217143382004837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087887190956191176006449 6065915393217143382004837)
                  ·
                    refine ⟨1137359136228214384125907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6065915393217143382004837 1137359136228214384125907)
                    ·
                      rfl

theorem cell23_6644997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_6644997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6644997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6644997 prefixEnd_6644997 := by exact prefixLift 6644997
  have htrace : WordTrace (prefixWord ++ tailWord_6644997) baseStart_6644997 baseEnd_6644997 := by
    simpa [prefixWord, tailWord_6644997, baseEnd_6644997] using wordTrace_append hprefix tailTrace_6644997
  have hstable : (prefixWord ++ tailWord_6644997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6644997).length < 2 ^ (prefixWord ++ tailWord_6644997).sum := by decide
  have hdescent : baseEnd_6644997 < baseStart_6644997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6644997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645021 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6645021 : Nat := 118140960795 + 6645021 * 2 ^ 59
def prefixEnd_6645021 : Nat := 4983230072969 + 3 ^ 40 * 6645021 * 2
def baseEnd_6645021 : Nat := 3412089732220351058477611

theorem tailTrace_6645021 : CollatzResearch.WordTrace tailWord_6645021 prefixEnd_6645021 3412089732220351058477611 := by
  unfold tailWord_6645021
  simp only [CollatzResearch.WordTrace]
  refine ⟨242363826859231271079558917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161575884572820847386372611 242363826859231271079558917)
  ·
    refine ⟨45443217536105863327417297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242363826859231271079558917 45443217536105863327417297)
    ·
      refine ⟨34082413152079397495562973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45443217536105863327417297 34082413152079397495562973)
      ·
        refine ⟨12780904932029774060836115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34082413152079397495562973 12780904932029774060836115)
        ·
          refine ⟨19171357398044661091254173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780904932029774060836115 19171357398044661091254173)
          ·
            refine ⟨7189259024266747909220315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19171357398044661091254173 7189259024266747909220315)
            ·
              refine ⟨10783888536400121863830473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189259024266747909220315 10783888536400121863830473)
              ·
                refine ⟨8087916402300091397872855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10783888536400121863830473 8087916402300091397872855)
                ·
                  refine ⟨12131874603450137096809283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8087916402300091397872855 12131874603450137096809283)
                  ·
                    refine ⟨18197811905175205645213925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12131874603450137096809283 18197811905175205645213925)
                    ·
                      refine ⟨3412089732220351058477611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18197811905175205645213925 3412089732220351058477611)
                      ·
                        rfl

theorem cell23_6645021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6645021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645021 prefixEnd_6645021 := by exact prefixLift 6645021
  have htrace : WordTrace (prefixWord ++ tailWord_6645021) baseStart_6645021 baseEnd_6645021 := by
    simpa [prefixWord, tailWord_6645021, baseEnd_6645021] using wordTrace_append hprefix tailTrace_6645021
  have hstable : (prefixWord ++ tailWord_6645021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645021).length < 2 ^ (prefixWord ++ tailWord_6645021).sum := by decide
  have hdescent : baseEnd_6645021 < baseStart_6645021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645024 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6645024 : Nat := 118140960795 + 6645024 * 2 ^ 59
def prefixEnd_6645024 : Nat := 4983230072969 + 3 ^ 40 * 6645024 * 2
def baseEnd_6645024 : Nat := 3412091272662314546740097

theorem tailTrace_6645024 : CollatzResearch.WordTrace tailWord_6645024 prefixEnd_6645024 3412091272662314546740097 := by
  unfold tailWord_6645024
  simp only [CollatzResearch.WordTrace]
  refine ⟨121181968139110201295959063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161575957518813601727945417 121181968139110201295959063)
  ·
    refine ⟨181772952208665301943938595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121181968139110201295959063 181772952208665301943938595)
    ·
      refine ⟨272659428312997952915907893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181772952208665301943938595 272659428312997952915907893)
      ·
        refine ⟨25561821404343558085866365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272659428312997952915907893 25561821404343558085866365)
        ·
          refine ⟨9585683026628834282199887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25561821404343558085866365 9585683026628834282199887)
          ·
            refine ⟨14378524539943251423299831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9585683026628834282199887 14378524539943251423299831)
            ·
              refine ⟨21567786809914877134949747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378524539943251423299831 21567786809914877134949747)
              ·
                refine ⟨32351680214872315702424621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21567786809914877134949747 32351680214872315702424621)
                ·
                  refine ⟨12131880080577118388409233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32351680214872315702424621 12131880080577118388409233)
                  ·
                    refine ⟨9098910060432838791306925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12131880080577118388409233 9098910060432838791306925)
                    ·
                      refine ⟨3412091272662314546740097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098910060432838791306925 3412091272662314546740097)
                      ·
                        rfl

theorem cell23_6645024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6645024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645024 prefixEnd_6645024 := by exact prefixLift 6645024
  have htrace : WordTrace (prefixWord ++ tailWord_6645024) baseStart_6645024 baseEnd_6645024 := by
    simpa [prefixWord, tailWord_6645024, baseEnd_6645024] using wordTrace_append hprefix tailTrace_6645024
  have hstable : (prefixWord ++ tailWord_6645024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645024).length < 2 ^ (prefixWord ++ tailWord_6645024).sum := by decide
  have hdescent : baseEnd_6645024 < baseStart_6645024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645034 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6645034 : Nat := 118140960795 + 6645034 * 2 ^ 59
def prefixEnd_6645034 : Nat := 4983230072969 + 3 ^ 40 * 6645034 * 2
def baseEnd_6645034 : Nat := 3412096407468859507615051

theorem tailTrace_6645034 : CollatzResearch.WordTrace tailWord_6645034 prefixEnd_6645034 3412096407468859507615051 := by
  unfold tailWord_6645034
  simp only [CollatzResearch.WordTrace]
  refine ⟨60591075252046043574945539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161576200672122782866521437 60591075252046043574945539)
  ·
    refine ⟨90886612878069065362418309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60591075252046043574945539 90886612878069065362418309)
    ·
      refine ⟨17041239914637949755453433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90886612878069065362418309 17041239914637949755453433)
      ·
        refine ⟨12780929935978462316590075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17041239914637949755453433 12780929935978462316590075)
        ·
          refine ⟨19171394903967693474885113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780929935978462316590075 19171394903967693474885113)
          ·
            refine ⟨14378546177975770106163835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171394903967693474885113 14378546177975770106163835)
            ·
              refine ⟨21567819266963655159245753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378546177975770106163835 21567819266963655159245753)
              ·
                refine ⟨16175864450222741369434315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21567819266963655159245753 16175864450222741369434315)
                ·
                  refine ⟨24263796675334112054151473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16175864450222741369434315 24263796675334112054151473)
                  ·
                    refine ⟨18197847506500584040613605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24263796675334112054151473 18197847506500584040613605)
                    ·
                      refine ⟨3412096407468859507615051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18197847506500584040613605 3412096407468859507615051)
                      ·
                        rfl

theorem cell23_6645034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6645034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645034 prefixEnd_6645034 := by exact prefixLift 6645034
  have htrace : WordTrace (prefixWord ++ tailWord_6645034) baseStart_6645034 baseEnd_6645034 := by
    simpa [prefixWord, tailWord_6645034, baseEnd_6645034] using wordTrace_append hprefix tailTrace_6645034
  have hstable : (prefixWord ++ tailWord_6645034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645034).length < 2 ^ (prefixWord ++ tailWord_6645034).sum := by decide
  have hdescent : baseEnd_6645034 < baseStart_6645034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645041 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 1, 2, 3]
def baseStart_6645041 : Nat := 118140960795 + 6645041 * 2 ^ 59
def prefixEnd_6645041 : Nat := 4983230072969 + 3 ^ 40 * 6645041 * 2
def baseEnd_6645041 : Nat := 3412100001833440980227519

theorem tailTrace_6645041 : CollatzResearch.WordTrace tailWord_6645041 prefixEnd_6645041 3412100001833440980227519 := by
  unfold tailWord_6645041
  simp only [CollatzResearch.WordTrace]
  refine ⟨242364556319158814495286977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161576370879439209663524651 242364556319158814495286977)
  ·
    refine ⟨181773417239369110871465233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242364556319158814495286977 181773417239369110871465233)
    ·
      refine ⟨136330062929526833153598925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181773417239369110871465233 136330062929526833153598925)
      ·
        refine ⟨51123773598572562432599597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136330062929526833153598925 51123773598572562432599597)
        ·
          refine ⟨19171415099464710912224849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51123773598572562432599597 19171415099464710912224849)
          ·
            refine ⟨14378561324598533184168637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171415099464710912224849 14378561324598533184168637)
            ·
              refine ⟨5391960496724449944063239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14378561324598533184168637 5391960496724449944063239)
              ·
                refine ⟨8087940745086674916094859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391960496724449944063239 8087940745086674916094859)
                ·
                  refine ⟨12131911117630012374142289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8087940745086674916094859 12131911117630012374142289)
                  ·
                    refine ⟨9098933338222509280606717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12131911117630012374142289 9098933338222509280606717)
                    ·
                      refine ⟨3412100001833440980227519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9098933338222509280606717 3412100001833440980227519)
                      ·
                        rfl

theorem cell23_6645041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_6645041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645041 prefixEnd_6645041 := by exact prefixLift 6645041
  have htrace : WordTrace (prefixWord ++ tailWord_6645041) baseStart_6645041 baseEnd_6645041 := by
    simpa [prefixWord, tailWord_6645041, baseEnd_6645041] using wordTrace_append hprefix tailTrace_6645041
  have hstable : (prefixWord ++ tailWord_6645041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645041).length < 2 ^ (prefixWord ++ tailWord_6645041).sum := by decide
  have hdescent : baseEnd_6645041 < baseStart_6645041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645055 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 1, 2, 2]
def baseStart_6645055 : Nat := 118140960795 + 6645055 * 2 ^ 59
def prefixEnd_6645055 : Nat := 4983230072969 + 3 ^ 40 * 6645055 * 2
def baseEnd_6645055 : Nat := 3412107190562603925452455

theorem tailTrace_6645055 : CollatzResearch.WordTrace tailWord_6645055 prefixEnd_6645055 3412107190562603925452455 := by
  unfold tailWord_6645055
  simp only [CollatzResearch.WordTrace]
  refine ⟨242365066941108094886296619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161576711294072063257531079 242365066941108094886296619)
  ·
    refine ⟨363547600411662142329444929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242365066941108094886296619 363547600411662142329444929)
    ·
      refine ⟨272660700308746606747083697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363547600411662142329444929 272660700308746606747083697)
      ·
        refine ⟨204495525231559955060312773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272660700308746606747083697 204495525231559955060312773)
        ·
          refine ⟨38342910980917491573808645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204495525231559955060312773 38342910980917491573808645)
          ·
            refine ⟨7189295808922029670089121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38342910980917491573808645 7189295808922029670089121)
            ·
              refine ⟨5391971856691522252566841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7189295808922029670089121 5391971856691522252566841)
              ·
                refine ⟨4043978892518641689425131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5391971856691522252566841 4043978892518641689425131)
                ·
                  refine ⟨6065968338777962534137697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043978892518641689425131 6065968338777962534137697)
                  ·
                    refine ⟨4549476254083471900603273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065968338777962534137697 4549476254083471900603273)
                    ·
                      refine ⟨3412107190562603925452455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549476254083471900603273 3412107190562603925452455)
                      ·
                        rfl

theorem cell23_6645055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_6645055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645055 prefixEnd_6645055 := by exact prefixLift 6645055
  have htrace : WordTrace (prefixWord ++ tailWord_6645055) baseStart_6645055 baseEnd_6645055 := by
    simpa [prefixWord, tailWord_6645055, baseEnd_6645055] using wordTrace_append hprefix tailTrace_6645055
  have hstable : (prefixWord ++ tailWord_6645055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645055).length < 2 ^ (prefixWord ++ tailWord_6645055).sum := by decide
  have hdescent : baseEnd_6645055 < baseStart_6645055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645057 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6645057 : Nat := 118140960795 + 6645057 * 2 ^ 59
def prefixEnd_6645057 : Nat := 4983230072969 + 3 ^ 40 * 6645057 * 2
def baseEnd_6645057 : Nat := 1137369405841304305875815

theorem tailTrace_6645057 : CollatzResearch.WordTrace tailWord_6645057 prefixEnd_6645057 1137369405841304305875815 := by
  unfold tailWord_6645057
  simp only [CollatzResearch.WordTrace]
  refine ⟨242365139887100849227869425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161576759924733899485246283 242365139887100849227869425)
  ·
    refine ⟨181773854915325636920902069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242365139887100849227869425 181773854915325636920902069)
    ·
      refine ⟨17041298898311778461334569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181773854915325636920902069 17041298898311778461334569)
      ·
        refine ⟨12780974173733833846000927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17041298898311778461334569 12780974173733833846000927)
        ·
          refine ⟨19171461260600750769001391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780974173733833846000927 19171461260600750769001391)
          ·
            refine ⟨28757191890901126153502087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19171461260600750769001391 28757191890901126153502087)
            ·
              refine ⟨43135787836351689230253131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28757191890901126153502087 43135787836351689230253131)
              ·
                refine ⟨64703681754527533845379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43135787836351689230253131 64703681754527533845379697)
                ·
                  refine ⟨48527761315895650384034773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64703681754527533845379697 48527761315895650384034773)
                  ·
                    refine ⟨1137369405841304305875815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48527761315895650384034773 1137369405841304305875815)
                    ·
                      rfl

theorem cell23_6645057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6645057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645057 prefixEnd_6645057 := by exact prefixLift 6645057
  have htrace : WordTrace (prefixWord ++ tailWord_6645057) baseStart_6645057 baseEnd_6645057 := by
    simpa [prefixWord, tailWord_6645057, baseEnd_6645057] using wordTrace_append hprefix tailTrace_6645057
  have hstable : (prefixWord ++ tailWord_6645057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645057).length < 2 ^ (prefixWord ++ tailWord_6645057).sum := by decide
  have hdescent : baseEnd_6645057 < baseStart_6645057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645098 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6645098 : Nat := 118140960795 + 6645098 * 2 ^ 59
def prefixEnd_6645098 : Nat := 4983230072969 + 3 ^ 40 * 6645098 * 2
def baseEnd_6645098 : Nat := 3412129270230747257214757

theorem tailTrace_6645098 : CollatzResearch.WordTrace tailWord_6645098 prefixEnd_6645098 3412129270230747257214757 := by
  unfold tailWord_6645098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60591658819988078307527987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161577756853301542153407965 60591658819988078307527987)
  ·
    refine ⟨90887488229982117461291981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60591658819988078307527987 90887488229982117461291981)
    ·
      refine ⟨34082808086243294047984493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90887488229982117461291981 34082808086243294047984493)
      ·
        refine ⟨12781053032341235267994185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34082808086243294047984493 12781053032341235267994185)
        ·
          refine ⟨9585789774255926450995639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12781053032341235267994185 9585789774255926450995639)
          ·
            refine ⟨14378684661383889676493459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9585789774255926450995639 14378684661383889676493459)
            ·
              refine ⟨21568026992075834514740189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378684661383889676493459 21568026992075834514740189)
              ·
                refine ⟨8088010122028437943027571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21568026992075834514740189 8088010122028437943027571)
                ·
                  refine ⟨12132015183042656914541357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8088010122028437943027571 12132015183042656914541357)
                  ·
                    refine ⟨4549505693640996342953009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12132015183042656914541357 4549505693640996342953009)
                    ·
                      refine ⟨3412129270230747257214757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549505693640996342953009 3412129270230747257214757)
                      ·
                        rfl

theorem cell23_6645098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6645098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645098 prefixEnd_6645098 := by exact prefixLift 6645098
  have htrace : WordTrace (prefixWord ++ tailWord_6645098) baseStart_6645098 baseEnd_6645098 := by
    simpa [prefixWord, tailWord_6645098, baseEnd_6645098] using wordTrace_append hprefix tailTrace_6645098
  have hstable : (prefixWord ++ tailWord_6645098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645098).length < 2 ^ (prefixWord ++ tailWord_6645098).sum := by decide
  have hdescent : baseEnd_6645098 < baseStart_6645098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645117 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 7]
def baseStart_6645117 : Nat := 118140960795 + 6645117 * 2 ^ 59
def prefixEnd_6645117 : Nat := 4983230072969 + 3 ^ 40 * 6645117 * 2
def baseEnd_6645117 : Nat := 379126558484798075875241

theorem tailTrace_6645117 : CollatzResearch.WordTrace tailWord_6645117 prefixEnd_6645117 379126558484798075875241 := by
  unfold tailWord_6645117
  simp only [CollatzResearch.WordTrace]
  refine ⟨242367328266883479475053605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161578218844588986316702403 242367328266883479475053605)
  ·
    refine ⟨45443874050040652401572551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242367328266883479475053605 45443874050040652401572551)
    ·
      refine ⟨68165811075060978602358827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45443874050040652401572551 68165811075060978602358827)
      ·
        refine ⟨102248716612591467903538241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68165811075060978602358827 102248716612591467903538241)
        ·
          refine ⟨76686537459443600927653681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102248716612591467903538241 76686537459443600927653681)
          ·
            refine ⟨57514903094582700695740261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76686537459443600927653681 57514903094582700695740261)
            ·
              refine ⟨10784044330234256380451299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57514903094582700695740261 10784044330234256380451299)
              ·
                refine ⟨16176066495351384570676949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784044330234256380451299 16176066495351384570676949)
                ·
                  refine ⟨379126558484798075875241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16176066495351384570676949 379126558484798075875241)
                  ·
                    rfl

theorem cell23_6645117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_6645117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645117 prefixEnd_6645117 := by exact prefixLift 6645117
  have htrace : WordTrace (prefixWord ++ tailWord_6645117) baseStart_6645117 baseEnd_6645117 := by
    simpa [prefixWord, tailWord_6645117, baseEnd_6645117] using wordTrace_append hprefix tailTrace_6645117
  have hstable : (prefixWord ++ tailWord_6645117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645117).length < 2 ^ (prefixWord ++ tailWord_6645117).sum := by decide
  have hdescent : baseEnd_6645117 < baseStart_6645117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645151 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 5]
def baseStart_6645151 : Nat := 118140960795 + 6645151 * 2 ^ 59
def prefixEnd_6645151 : Nat := 4983230072969 + 3 ^ 40 * 6645151 * 2
def baseEnd_6645151 : Nat := 379128498300603949983557

theorem tailTrace_6645151 : CollatzResearch.WordTrace tailWord_6645151 prefixEnd_6645151 379128498300603949983557 := by
  unfold tailWord_6645151
  simp only [CollatzResearch.WordTrace]
  refine ⟨242368568348760303281791307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161579045565840202187860871 242368568348760303281791307)
  ·
    refine ⟨363552852523140454922686961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242368568348760303281791307 363552852523140454922686961)
    ·
      refine ⟨272664639392355341192015221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363552852523140454922686961 272664639392355341192015221)
      ·
        refine ⟨25562309943033313236751427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272664639392355341192015221 25562309943033313236751427)
        ·
          refine ⟨38343464914549969855127141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25562309943033313236751427 38343464914549969855127141)
          ·
            refine ⟨7189399671478119347836339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38343464914549969855127141 7189399671478119347836339)
            ·
              refine ⟨10784099507217179021754509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189399671478119347836339 10784099507217179021754509)
              ·
                refine ⟨4044037315206442133157941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10784099507217179021754509 4044037315206442133157941)
                ·
                  refine ⟨379128498300603949983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4044037315206442133157941 379128498300603949983557)
                  ·
                    rfl

theorem cell23_6645151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 5].length) (baseStart_6645151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645151 prefixEnd_6645151 := by exact prefixLift 6645151
  have htrace : WordTrace (prefixWord ++ tailWord_6645151) baseStart_6645151 baseEnd_6645151 := by
    simpa [prefixWord, tailWord_6645151, baseEnd_6645151] using wordTrace_append hprefix tailTrace_6645151
  have hstable : (prefixWord ++ tailWord_6645151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645151).length < 2 ^ (prefixWord ++ tailWord_6645151).sum := by decide
  have hdescent : baseEnd_6645151 < baseStart_6645151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645184 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2]
def baseStart_6645184 : Nat := 118140960795 + 6645184 * 2 ^ 59
def prefixEnd_6645184 : Nat := 4983230072969 + 3 ^ 40 * 6645184 * 2
def baseEnd_6645184 : Nat := 3412173429567033920739361

theorem tailTrace_6645184 : CollatzResearch.WordTrace tailWord_6645184 prefixEnd_6645184 3412173429567033920739361 := by
  unfold tailWord_6645184
  simp only [CollatzResearch.WordTrace]
  refine ⟨121184885978820374958871303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161579847971760499945161737 121184885978820374958871303)
  ·
    refine ⟨181777328968230562438306955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121184885978820374958871303 181777328968230562438306955)
    ·
      refine ⟨272665993452345843657460433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181777328968230562438306955 272665993452345843657460433)
      ·
        refine ⟨204499495089259382743095325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272665993452345843657460433 204499495089259382743095325)
        ·
          refine ⟨76687310658472268528660747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204499495089259382743095325 76687310658472268528660747)
          ·
            refine ⟨115030965987708402792991121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76687310658472268528660747 115030965987708402792991121)
            ·
              refine ⟨86273224490781302094743341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115030965987708402792991121 86273224490781302094743341)
              ·
                refine ⟨32352459184042988285528753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86273224490781302094743341 32352459184042988285528753)
                ·
                  refine ⟨24264344388032241214146565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32352459184042988285528753 24264344388032241214146565)
                  ·
                    refine ⟨4549564572756045227652481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24264344388032241214146565 4549564572756045227652481)
                    ·
                      refine ⟨3412173429567033920739361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549564572756045227652481 3412173429567033920739361)
                      ·
                        rfl

theorem cell23_6645184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_6645184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645184 prefixEnd_6645184 := by exact prefixLift 6645184
  have htrace : WordTrace (prefixWord ++ tailWord_6645184) baseStart_6645184 baseEnd_6645184 := by
    simpa [prefixWord, tailWord_6645184, baseEnd_6645184] using wordTrace_append hprefix tailTrace_6645184
  have hstable : (prefixWord ++ tailWord_6645184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645184).length < 2 ^ (prefixWord ++ tailWord_6645184).sum := by decide
  have hdescent : baseEnd_6645184 < baseStart_6645184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645187 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3]
def baseStart_6645187 : Nat := 118140960795 + 6645187 * 2 ^ 59
def prefixEnd_6645187 : Nat := 4983230072969 + 3 ^ 40 * 6645187 * 2
def baseEnd_6645187 : Nat := 3412174970008997409001847

theorem tailTrace_6645187 : CollatzResearch.WordTrace tailWord_6645187 prefixEnd_6645187 3412174970008997409001847 := by
  unfold tailWord_6645187
  simp only [CollatzResearch.WordTrace]
  refine ⟨242369881376629881430101815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161579920917753254286734543 242369881376629881430101815)
  ·
    refine ⟨363554822064944822145152723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242369881376629881430101815 363554822064944822145152723)
    ·
      refine ⟨545332233097417233217729085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363554822064944822145152723 545332233097417233217729085)
      ·
        refine ⟨204499587411531462456648407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545332233097417233217729085 204499587411531462456648407)
        ·
          refine ⟨306749381117297193684972611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204499587411531462456648407 306749381117297193684972611)
          ·
            refine ⟨460124071675945790527458917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306749381117297193684972611 460124071675945790527458917)
            ·
              refine ⟨86273263439239835723898547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460124071675945790527458917 86273263439239835723898547)
              ·
                refine ⟨129409895158859753585847821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86273263439239835723898547 129409895158859753585847821)
                ·
                  refine ⟨48528710684572407594692933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129409895158859753585847821 48528710684572407594692933)
                  ·
                    refine ⟨9099133253357326424004925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48528710684572407594692933 9099133253357326424004925)
                    ·
                      refine ⟨3412174970008997409001847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099133253357326424004925 3412174970008997409001847)
                      ·
                        rfl

theorem cell23_6645187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_6645187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645187 prefixEnd_6645187 := by exact prefixLift 6645187
  have htrace : WordTrace (prefixWord ++ tailWord_6645187) baseStart_6645187 baseEnd_6645187 := by
    simpa [prefixWord, tailWord_6645187, baseEnd_6645187] using wordTrace_append hprefix tailTrace_6645187
  have hstable : (prefixWord ++ tailWord_6645187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645187).length < 2 ^ (prefixWord ++ tailWord_6645187).sum := by decide
  have hdescent : baseEnd_6645187 < baseStart_6645187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645221 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6645221 : Nat := 118140960795 + 6645221 * 2 ^ 59
def prefixEnd_6645221 : Nat := 4983230072969 + 3 ^ 40 * 6645221 * 2
def baseEnd_6645221 : Nat := 3412192428351250275976691

theorem tailTrace_6645221 : CollatzResearch.WordTrace tailWord_6645221 prefixEnd_6645221 3412192428351250275976691 := by
  unfold tailWord_6645221
  simp only [CollatzResearch.WordTrace]
  refine ⟨242371121458506705236839517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161580747639004470157893011 242371121458506705236839517)
  ·
    refine ⟨90889170546940014463814819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242371121458506705236839517 90889170546940014463814819)
    ·
      refine ⟨136333755820410021695722229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90889170546940014463814819 136333755820410021695722229)
      ·
        refine ⟨12781289608163439533973959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136333755820410021695722229 12781289608163439533973959)
        ·
          refine ⟨19171934412245159300960939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12781289608163439533973959 19171934412245159300960939)
          ·
            refine ⟨28757901618367738951441409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19171934412245159300960939 28757901618367738951441409)
            ·
              refine ⟨21568426213775804213581057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28757901618367738951441409 21568426213775804213581057)
              ·
                refine ⟨16176319660331853160185793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21568426213775804213581057 16176319660331853160185793)
                ·
                  refine ⟨12132239745248889870139345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16176319660331853160185793 12132239745248889870139345)
                  ·
                    refine ⟨9099179808936667402604509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12132239745248889870139345 9099179808936667402604509)
                    ·
                      refine ⟨3412192428351250275976691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099179808936667402604509 3412192428351250275976691)
                      ·
                        rfl

theorem cell23_6645221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6645221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645221 prefixEnd_6645221 := by exact prefixLift 6645221
  have htrace : WordTrace (prefixWord ++ tailWord_6645221) baseStart_6645221 baseEnd_6645221 := by
    simpa [prefixWord, tailWord_6645221, baseEnd_6645221] using wordTrace_append hprefix tailTrace_6645221
  have hstable : (prefixWord ++ tailWord_6645221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645221).length < 2 ^ (prefixWord ++ tailWord_6645221).sum := by decide
  have hdescent : baseEnd_6645221 < baseStart_6645221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645224 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 6]
def baseStart_6645224 : Nat := 118140960795 + 6645224 * 2 ^ 59
def prefixEnd_6645224 : Nat := 4983230072969 + 3 ^ 40 * 6645224 * 2
def baseEnd_6645224 : Nat := 379132663199245973804353

theorem tailTrace_6645224 : CollatzResearch.WordTrace tailWord_6645224 prefixEnd_6645224 379132663199245973804353 := by
  unfold tailWord_6645224
  simp only [CollatzResearch.WordTrace]
  refine ⟨121185615438747918374599363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161580820584997224499465817 121185615438747918374599363)
  ·
    refine ⟨181778423158121877561899045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121185615438747918374599363 181778423158121877561899045)
    ·
      refine ⟨34083454342147852042856071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181778423158121877561899045 34083454342147852042856071)
      ·
        refine ⟨51125181513221778064284107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34083454342147852042856071 51125181513221778064284107)
        ·
          refine ⟨76687772269832667096426161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51125181513221778064284107 76687772269832667096426161)
          ·
            refine ⟨57515829202374500322319621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76687772269832667096426161 57515829202374500322319621)
            ·
              refine ⟨10784217975445218810434929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57515829202374500322319621 10784217975445218810434929)
              ·
                refine ⟨8088163481583914107826197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10784217975445218810434929 8088163481583914107826197)
                ·
                  refine ⟨379132663199245973804353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8088163481583914107826197 379132663199245973804353)
                  ·
                    rfl

theorem cell23_6645224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_6645224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645224 prefixEnd_6645224 := by exact prefixLift 6645224
  have htrace : WordTrace (prefixWord ++ tailWord_6645224) baseStart_6645224 baseEnd_6645224 := by
    simpa [prefixWord, tailWord_6645224, baseEnd_6645224] using wordTrace_append hprefix tailTrace_6645224
  have hstable : (prefixWord ++ tailWord_6645224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645224).length < 2 ^ (prefixWord ++ tailWord_6645224).sum := by decide
  have hdescent : baseEnd_6645224 < baseStart_6645224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645297 : List Nat := [1, 2, 2, 3, 1, 1, 1, 12]
def baseStart_6645297 : Nat := 118140960795 + 6645297 * 2 ^ 59
def prefixEnd_6645297 : Nat := 4983230072969 + 3 ^ 40 * 6645297 * 2
def baseEnd_6645297 : Nat := 126378942699295999208383

theorem tailTrace_6645297 : CollatzResearch.WordTrace tailWord_6645297 prefixEnd_6645297 126378942699295999208383 := by
  unfold tailWord_6645297
  simp only [CollatzResearch.WordTrace]
  refine ⟨242373893406231370216606145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161582595604154246811070763 242373893406231370216606145)
  ·
    refine ⟨181780420054673527662454609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242373893406231370216606145 181780420054673527662454609)
    ·
      refine ⟨136335315041005145746840957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181780420054673527662454609 136335315041005145746840957)
      ·
        refine ⟨51125743140376929655065359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136335315041005145746840957 51125743140376929655065359)
        ·
          refine ⟨76688614710565394482598039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51125743140376929655065359 76688614710565394482598039)
          ·
            refine ⟨115032922065848091723897059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76688614710565394482598039 115032922065848091723897059)
            ·
              refine ⟨172549383098772137585845589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115032922065848091723897059 172549383098772137585845589)
              ·
                refine ⟨126378942699295999208383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 172549383098772137585845589 126378942699295999208383)
                ·
                  rfl

theorem cell23_6645297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 12].length) (baseStart_6645297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645297 prefixEnd_6645297 := by exact prefixLift 6645297
  have htrace : WordTrace (prefixWord ++ tailWord_6645297) baseStart_6645297 baseEnd_6645297 := by
    simpa [prefixWord, tailWord_6645297, baseEnd_6645297] using wordTrace_append hprefix tailTrace_6645297
  have hstable : (prefixWord ++ tailWord_6645297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645297).length < 2 ^ (prefixWord ++ tailWord_6645297).sum := by decide
  have hdescent : baseEnd_6645297 < baseStart_6645297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645301 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6645301 : Nat := 118140960795 + 6645301 * 2 ^ 59
def prefixEnd_6645301 : Nat := 4983230072969 + 3 ^ 40 * 6645301 * 2
def baseEnd_6645301 : Nat := 1137411168934536654325441

theorem tailTrace_6645301 : CollatzResearch.WordTrace tailWord_6645301 prefixEnd_6645301 1137411168934536654325441 := by
  unfold tailWord_6645301
  simp only [CollatzResearch.WordTrace]
  refine ⟨242374039298216878899751757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161582692865477919266501171 242374039298216878899751757)
  ·
    refine ⟨90890264736831329587406909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242374039298216878899751757 90890264736831329587406909)
    ·
      refine ⟨34083849276311748595277591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90890264736831329587406909 34083849276311748595277591)
      ·
        refine ⟨51125773914467622892916387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34083849276311748595277591 51125773914467622892916387)
        ·
          refine ⟨76688660871701434339374581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51125773914467622892916387 76688660871701434339374581)
          ·
            refine ⟨7189561956722009469316367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76688660871701434339374581 7189561956722009469316367)
            ·
              refine ⟨10784342935083014203974551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189561956722009469316367 10784342935083014203974551)
              ·
                refine ⟨16176514402624521305961827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784342935083014203974551 16176514402624521305961827)
                ·
                  refine ⟨24264771603936781958942741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16176514402624521305961827 24264771603936781958942741)
                  ·
                    refine ⟨1137411168934536654325441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24264771603936781958942741 1137411168934536654325441)
                    ·
                      rfl

theorem cell23_6645301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6645301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645301 prefixEnd_6645301 := by exact prefixLift 6645301
  have htrace : WordTrace (prefixWord ++ tailWord_6645301) baseStart_6645301 baseEnd_6645301 := by
    simpa [prefixWord, tailWord_6645301, baseEnd_6645301] using wordTrace_append hprefix tailTrace_6645301
  have hstable : (prefixWord ++ tailWord_6645301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645301).length < 2 ^ (prefixWord ++ tailWord_6645301).sum := by decide
  have hdescent : baseEnd_6645301 < baseStart_6645301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645304 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_6645304 : Nat := 118140960795 + 6645304 * 2 ^ 59
def prefixEnd_6645304 : Nat := 4983230072969 + 3 ^ 40 * 6645304 * 2
def baseEnd_6645304 : Nat := 3412235047245573451238809

theorem tailTrace_6645304 : CollatzResearch.WordTrace tailWord_6645304 prefixEnd_6645304 3412235047245573451238809 := by
  unfold tailWord_6645304
  simp only [CollatzResearch.WordTrace]
  refine ⟨121187074358603005206055483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161582765811470673608073977 121187074358603005206055483)
  ·
    refine ⟨181780611537904507809083225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121187074358603005206055483 181780611537904507809083225)
    ·
      refine ⟨136335458653428380856812419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181780611537904507809083225 136335458653428380856812419)
      ·
        refine ⟨204503187980142571285218629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136335458653428380856812419 204503187980142571285218629)
        ·
          refine ⟨38344347746276732115978493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204503187980142571285218629 38344347746276732115978493)
          ·
            refine ⟨14379130404853774543491935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38344347746276732115978493 14379130404853774543491935)
            ·
              refine ⟨21568695607280661815237903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14379130404853774543491935 21568695607280661815237903)
              ·
                refine ⟨32353043410920992722856855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21568695607280661815237903 32353043410920992722856855)
                ·
                  refine ⟨48529565116381489084285283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32353043410920992722856855 48529565116381489084285283)
                  ·
                    refine ⟨72794347674572233626427925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48529565116381489084285283 72794347674572233626427925)
                    ·
                      refine ⟨3412235047245573451238809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72794347674572233626427925 3412235047245573451238809)
                      ·
                        rfl

theorem cell23_6645304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_6645304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645304 prefixEnd_6645304 := by exact prefixLift 6645304
  have htrace : WordTrace (prefixWord ++ tailWord_6645304) baseStart_6645304 baseEnd_6645304 := by
    simpa [prefixWord, tailWord_6645304, baseEnd_6645304] using wordTrace_append hprefix tailTrace_6645304
  have hstable : (prefixWord ++ tailWord_6645304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645304).length < 2 ^ (prefixWord ++ tailWord_6645304).sum := by decide
  have hdescent : baseEnd_6645304 < baseStart_6645304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645308 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_6645308 : Nat := 118140960795 + 6645308 * 2 ^ 59
def prefixEnd_6645308 : Nat := 4983230072969 + 3 ^ 40 * 6645308 * 2
def baseEnd_6645308 : Nat := 3412237101168191435588791

theorem tailTrace_6645308 : CollatzResearch.WordTrace tailWord_6645308 prefixEnd_6645308 3412237101168191435588791 := by
  unfold tailWord_6645308
  simp only [CollatzResearch.WordTrace]
  refine ⟨121187147304595759547628289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161582863072794346063504385 121187147304595759547628289)
  ·
    refine ⟨90890360478446819660721217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121187147304595759547628289 90890360478446819660721217)
    ·
      refine ⟨68167770358835114745540913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90890360478446819660721217 68167770358835114745540913)
      ·
        refine ⟨51125827769126336059155685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68167770358835114745540913 51125827769126336059155685)
        ·
          refine ⟨9586092706711188011091691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51125827769126336059155685 9586092706711188011091691)
          ·
            refine ⟨14379139060066782016637537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9586092706711188011091691 14379139060066782016637537)
            ·
              refine ⟨10784354295050086512478153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14379139060066782016637537 10784354295050086512478153)
              ·
                refine ⟨8088265721287564884358615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10784354295050086512478153 8088265721287564884358615)
                ·
                  refine ⟨12132398581931347326537923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8088265721287564884358615 12132398581931347326537923)
                  ·
                    refine ⟨18198597872897020989806885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12132398581931347326537923 18198597872897020989806885)
                    ·
                      refine ⟨3412237101168191435588791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18198597872897020989806885 3412237101168191435588791)
                      ·
                        rfl

theorem cell23_6645308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_6645308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645308 prefixEnd_6645308 := by exact prefixLift 6645308
  have htrace : WordTrace (prefixWord ++ tailWord_6645308) baseStart_6645308 baseEnd_6645308 := by
    simpa [prefixWord, tailWord_6645308, baseEnd_6645308] using wordTrace_append hprefix tailTrace_6645308
  have hstable : (prefixWord ++ tailWord_6645308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645308).length < 2 ^ (prefixWord ++ tailWord_6645308).sum := by decide
  have hdescent : baseEnd_6645308 < baseStart_6645308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645311 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_6645311 : Nat := 118140960795 + 6645311 * 2 ^ 59
def prefixEnd_6645311 : Nat := 4983230072969 + 3 ^ 40 * 6645311 * 2
def baseEnd_6645311 : Nat := 3412238641610154923851277

theorem tailTrace_6645311 : CollatzResearch.WordTrace tailWord_6645311 prefixEnd_6645311 3412238641610154923851277 := by
  unfold tailWord_6645311
  simp only [CollatzResearch.WordTrace]
  refine ⟨242374404028180650607615787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161582936018787100405077191 242374404028180650607615787)
  ·
    refine ⟨363561606042270975911423681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242374404028180650607615787 363561606042270975911423681)
    ·
      refine ⟨272671204531703231933567761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363561606042270975911423681 272671204531703231933567761)
      ·
        refine ⟨204503403398777423950175821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272671204531703231933567761 204503403398777423950175821)
        ·
          refine ⟨76688776274541533981315933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204503403398777423950175821 76688776274541533981315933)
          ·
            refine ⟨28758291102953075242993475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76688776274541533981315933 28758291102953075242993475)
            ·
              refine ⟨43137436654429612864490213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28758291102953075242993475 43137436654429612864490213)
              ·
                refine ⟨8088269372705552412091915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43137436654429612864490213 8088269372705552412091915)
                ·
                  refine ⟨12132404059058328618137873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8088269372705552412091915 12132404059058328618137873)
                  ·
                    refine ⟨9099303044293746463603405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12132404059058328618137873 9099303044293746463603405)
                    ·
                      refine ⟨3412238641610154923851277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099303044293746463603405 3412238641610154923851277)
                      ·
                        rfl

theorem cell23_6645311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_6645311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645311 prefixEnd_6645311 := by exact prefixLift 6645311
  have htrace : WordTrace (prefixWord ++ tailWord_6645311) baseStart_6645311 baseEnd_6645311 := by
    simpa [prefixWord, tailWord_6645311, baseEnd_6645311] using wordTrace_append hprefix tailTrace_6645311
  have hstable : (prefixWord ++ tailWord_6645311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645311).length < 2 ^ (prefixWord ++ tailWord_6645311).sum := by decide
  have hdescent : baseEnd_6645311 < baseStart_6645311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645327 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 9]
def baseStart_6645327 : Nat := 118140960795 + 6645327 * 2 ^ 59
def prefixEnd_6645327 : Nat := 4983230072969 + 3 ^ 40 * 6645327 * 2
def baseEnd_6645327 : Nat := 1137415619100208953750401

theorem tailTrace_6645327 : CollatzResearch.WordTrace tailWord_6645327 prefixEnd_6645327 1137415619100208953750401 := by
  unfold tailWord_6645327
  simp only [CollatzResearch.WordTrace]
  refine ⟨242374987596122685340198235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161583325064081790226798823 242374987596122685340198235)
  ·
    refine ⟨363562481394184028010297353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242374987596122685340198235 363562481394184028010297353)
    ·
      refine ⟨272671861045638021007723015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363562481394184028010297353 272671861045638021007723015)
      ·
        refine ⟨409007791568457031511584523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272671861045638021007723015 409007791568457031511584523)
        ·
          refine ⟨613511687352685547267376785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409007791568457031511584523 613511687352685547267376785)
          ·
            refine ⟨460133765514514160450532589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613511687352685547267376785 460133765514514160450532589)
            ·
              refine ⟨172550162067942810168949721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460133765514514160450532589 172550162067942810168949721)
              ·
                refine ⟨129412621550957107626712291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172550162067942810168949721 129412621550957107626712291)
                ·
                  refine ⟨194118932326435661440068437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129412621550957107626712291 194118932326435661440068437)
                  ·
                    refine ⟨1137415619100208953750401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194118932326435661440068437 1137415619100208953750401)
                    ·
                      rfl

theorem cell23_6645327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_6645327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645327 prefixEnd_6645327 := by exact prefixLift 6645327
  have htrace : WordTrace (prefixWord ++ tailWord_6645327) baseStart_6645327 baseEnd_6645327 := by
    simpa [prefixWord, tailWord_6645327, baseEnd_6645327] using wordTrace_append hprefix tailTrace_6645327
  have hstable : (prefixWord ++ tailWord_6645327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645327).length < 2 ^ (prefixWord ++ tailWord_6645327).sum := by decide
  have hdescent : baseEnd_6645327 < baseStart_6645327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645421 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 7]
def baseStart_6645421 : Nat := 118140960795 + 6645421 * 2 ^ 59
def prefixEnd_6645421 : Nat := 4983230072969 + 3 ^ 40 * 6645421 * 2
def baseEnd_6645421 : Nat := 379143902720238832608419

theorem tailTrace_6645421 : CollatzResearch.WordTrace tailWord_6645421 prefixEnd_6645421 379143902720238832608419 := by
  unfold tailWord_6645421
  simp only [CollatzResearch.WordTrace]
  refine ⟨242378416057782139394120117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161585610705188092929413411 242378416057782139394120117)
  ·
    refine ⟨22722976505417075568198761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242378416057782139394120117 22722976505417075568198761)
    ·
      refine ⟨17042232379062806676149071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22722976505417075568198761 17042232379062806676149071)
      ·
        refine ⟨25563348568594210014223607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17042232379062806676149071 25563348568594210014223607)
        ·
          refine ⟨38345022852891315021335411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25563348568594210014223607 38345022852891315021335411)
          ·
            refine ⟨57517534279336972532003117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38345022852891315021335411 57517534279336972532003117)
            ·
              refine ⟨21569075354751364699501169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57517534279336972532003117 21569075354751364699501169)
              ·
                refine ⟨16176806516063523524625877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21569075354751364699501169 16176806516063523524625877)
                ·
                  refine ⟨379143902720238832608419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16176806516063523524625877 379143902720238832608419)
                  ·
                    rfl

theorem cell23_6645421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_6645421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645421 prefixEnd_6645421 := by exact prefixLift 6645421
  have htrace : WordTrace (prefixWord ++ tailWord_6645421) baseStart_6645421 baseEnd_6645421 := by
    simpa [prefixWord, tailWord_6645421, baseEnd_6645421] using wordTrace_append hprefix tailTrace_6645421
  have hstable : (prefixWord ++ tailWord_6645421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645421).length < 2 ^ (prefixWord ++ tailWord_6645421).sum := by decide
  have hdescent : baseEnd_6645421 < baseStart_6645421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645438 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_6645438 : Nat := 118140960795 + 6645438 * 2 ^ 59
def prefixEnd_6645438 : Nat := 4983230072969 + 3 ^ 40 * 6645438 * 2
def baseEnd_6645438 : Nat := 379144872628141769662577

theorem tailTrace_6645438 : CollatzResearch.WordTrace tailWord_6645438 prefixEnd_6645438 379144872628141769662577 := by
  unfold tailWord_6645438
  simp only [CollatzResearch.WordTrace]
  refine ⟨30297379512340068912186121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161586024065813700864992645 30297379512340068912186121)
  ·
    refine ⟨22723034634255051684139591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30297379512340068912186121 22723034634255051684139591)
    ·
      refine ⟨34084551951382577526209387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723034634255051684139591 34084551951382577526209387)
      ·
        refine ⟨51126827927073866289314081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34084551951382577526209387 51126827927073866289314081)
        ·
          refine ⟨38345120945305399716985561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51126827927073866289314081 38345120945305399716985561)
          ·
            refine ⟨28758840708979049787739171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38345120945305399716985561 28758840708979049787739171)
            ·
              refine ⟨43138261063468574681608757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28758840708979049787739171 43138261063468574681608757)
              ·
                refine ⟨4044211974700178876400821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43138261063468574681608757 4044211974700178876400821)
                ·
                  refine ⟨379144872628141769662577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4044211974700178876400821 379144872628141769662577)
                  ·
                    rfl

theorem cell23_6645438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_6645438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645438 prefixEnd_6645438 := by exact prefixLift 6645438
  have htrace : WordTrace (prefixWord ++ tailWord_6645438) baseStart_6645438 baseEnd_6645438 := by
    simpa [prefixWord, tailWord_6645438, baseEnd_6645438] using wordTrace_append hprefix tailTrace_6645438
  have hstable : (prefixWord ++ tailWord_6645438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645438).length < 2 ^ (prefixWord ++ tailWord_6645438).sum := by decide
  have hdescent : baseEnd_6645438 < baseStart_6645438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645491 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3]
def baseStart_6645491 : Nat := 118140960795 + 6645491 * 2 ^ 59
def prefixEnd_6645491 : Nat := 4983230072969 + 3 ^ 40 * 6645491 * 2
def baseEnd_6645491 : Nat := 3412331068127964219600449

theorem tailTrace_6645491 : CollatzResearch.WordTrace tailWord_6645491 prefixEnd_6645491 3412331068127964219600449 := by
  unfold tailWord_6645491
  simp only [CollatzResearch.WordTrace]
  refine ⟨242380969167528541349168327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161587312778352360899445551 242380969167528541349168327)
  ·
    refine ⟨363571453751292812023752491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242380969167528541349168327 363571453751292812023752491)
    ·
      refine ⟨545357180626939218035628737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363571453751292812023752491 545357180626939218035628737)
      ·
        refine ⟨409017885470204413526721553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545357180626939218035628737 409017885470204413526721553)
        ·
          refine ⟨306763414102653310145041165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409017885470204413526721553 306763414102653310145041165)
          ·
            refine ⟨115036280288494991304390437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306763414102653310145041165 115036280288494991304390437)
            ·
              refine ⟨21569302554092810869573207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115036280288494991304390437 21569302554092810869573207)
              ·
                refine ⟨32353953831139216304359811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21569302554092810869573207 32353953831139216304359811)
                ·
                  refine ⟨48530930746708824456539717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32353953831139216304359811 48530930746708824456539717)
                  ·
                    refine ⟨9099549515007904585601197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48530930746708824456539717 9099549515007904585601197)
                    ·
                      refine ⟨3412331068127964219600449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099549515007904585601197 3412331068127964219600449)
                      ·
                        rfl

theorem cell23_6645491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_6645491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645491 prefixEnd_6645491 := by exact prefixLift 6645491
  have htrace : WordTrace (prefixWord ++ tailWord_6645491) baseStart_6645491 baseEnd_6645491 := by
    simpa [prefixWord, tailWord_6645491, baseEnd_6645491] using wordTrace_append hprefix tailTrace_6645491
  have hstable : (prefixWord ++ tailWord_6645491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645491).length < 2 ^ (prefixWord ++ tailWord_6645491).sum := by decide
  have hdescent : baseEnd_6645491 < baseStart_6645491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645508 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6645508 : Nat := 118140960795 + 6645508 * 2 ^ 59
def prefixEnd_6645508 : Nat := 4983230072969 + 3 ^ 40 * 6645508 * 2
def baseEnd_6645508 : Nat := 3412339797299090653087871

theorem tailTrace_6645508 : CollatzResearch.WordTrace tailWord_6645508 prefixEnd_6645508 3412339797299090653087871 := by
  unfold tailWord_6645508
  simp only [CollatzResearch.WordTrace]
  refine ⟨121190794604233476626268589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161587726138977968835024785 121190794604233476626268589)
  ·
    refine ⟨45446547976587553734850721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121190794604233476626268589 45446547976587553734850721)
    ·
      refine ⟨34084910982440665301138041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45446547976587553734850721 34084910982440665301138041)
      ·
        refine ⟨25563683236830498975853531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34084910982440665301138041 25563683236830498975853531)
        ·
          refine ⟨38345524855245748463780297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25563683236830498975853531 38345524855245748463780297)
          ·
            refine ⟨28759143641434311347835223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38345524855245748463780297 28759143641434311347835223)
            ·
              refine ⟨43138715462151467021752835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28759143641434311347835223 43138715462151467021752835)
              ·
                refine ⟨64708073193227200532629253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43138715462151467021752835 64708073193227200532629253)
                ·
                  refine ⟨12132763723730100099867985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64708073193227200532629253 12132763723730100099867985)
                  ·
                    refine ⟨9099572792797575074900989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12132763723730100099867985 9099572792797575074900989)
                    ·
                      refine ⟨3412339797299090653087871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099572792797575074900989 3412339797299090653087871)
                      ·
                        rfl

theorem cell23_6645508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6645508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645508 prefixEnd_6645508 := by exact prefixLift 6645508
  have htrace : WordTrace (prefixWord ++ tailWord_6645508) baseStart_6645508 baseEnd_6645508 := by
    simpa [prefixWord, tailWord_6645508, baseEnd_6645508] using wordTrace_append hprefix tailTrace_6645508
  have hstable : (prefixWord ++ tailWord_6645508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645508).length < 2 ^ (prefixWord ++ tailWord_6645508).sum := by decide
  have hdescent : baseEnd_6645508 < baseStart_6645508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645517 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6645517 : Nat := 118140960795 + 6645517 * 2 ^ 59
def prefixEnd_6645517 : Nat := 4983230072969 + 3 ^ 40 * 6645517 * 2
def baseEnd_6645517 : Nat := 3412344418624981117875331

theorem tailTrace_6645517 : CollatzResearch.WordTrace tailWord_6645517 prefixEnd_6645517 3412344418624981117875331 := by
  unfold tailWord_6645517
  simp only [CollatzResearch.WordTrace]
  refine ⟨242381917465434347789614805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161587944976956231859743203 242381917465434347789614805)
  ·
    refine ⟨5680826190596117526319097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 242381917465434347789614805 5680826190596117526319097)
    ·
      refine ⟨4260619642947088144739323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680826190596117526319097 4260619642947088144739323)
      ·
        refine ⟨6390929464420632217108985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260619642947088144739323 6390929464420632217108985)
        ·
          refine ⟨4793197098315474162831739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390929464420632217108985 4793197098315474162831739)
          ·
            refine ⟨7189795647473211244247609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793197098315474162831739 7189795647473211244247609)
            ·
              refine ⟨5392346735604908433185707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7189795647473211244247609 5392346735604908433185707)
              ·
                refine ⟨8088520103407362649778561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392346735604908433185707 8088520103407362649778561)
                ·
                  refine ⟨6066390077555521987333921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8088520103407362649778561 6066390077555521987333921)
                  ·
                    refine ⟨4549792558166641490500441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066390077555521987333921 4549792558166641490500441)
                    ·
                      refine ⟨3412344418624981117875331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549792558166641490500441 3412344418624981117875331)
                      ·
                        rfl

theorem cell23_6645517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6645517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645517 prefixEnd_6645517 := by exact prefixLift 6645517
  have htrace : WordTrace (prefixWord ++ tailWord_6645517) baseStart_6645517 baseEnd_6645517 := by
    simpa [prefixWord, tailWord_6645517, baseEnd_6645517] using wordTrace_append hprefix tailTrace_6645517
  have hstable : (prefixWord ++ tailWord_6645517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645517).length < 2 ^ (prefixWord ++ tailWord_6645517).sum := by decide
  have hdescent : baseEnd_6645517 < baseStart_6645517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645528 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 6]
def baseStart_6645528 : Nat := 118140960795 + 6645528 * 2 ^ 59
def prefixEnd_6645528 : Nat := 4983230072969 + 3 ^ 40 * 6645528 * 2
def baseEnd_6645528 : Nat := 379150007434686730537531

theorem tailTrace_6645528 : CollatzResearch.WordTrace tailWord_6645528 prefixEnd_6645528 379150007434686730537531 := by
  unfold tailWord_6645528
  simp only [CollatzResearch.WordTrace]
  refine ⟨121191159334197248334132619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161588212445596331112176825 121191159334197248334132619)
  ·
    refine ⟨181786739001295872501198929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121191159334197248334132619 181786739001295872501198929)
    ·
      refine ⟨136340054250971904375899197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181786739001295872501198929 136340054250971904375899197)
      ·
        refine ⟨51127520344114464140962199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136340054250971904375899197 51127520344114464140962199)
        ·
          refine ⟨76691280516171696211443299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51127520344114464140962199 76691280516171696211443299)
          ·
            refine ⟨115036920774257544317164949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76691280516171696211443299 115036920774257544317164949)
            ·
              refine ⟨5392355661293322389867107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115036920774257544317164949 5392355661293322389867107)
              ·
                refine ⟨8088533491939983584800661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392355661293322389867107 8088533491939983584800661)
                ·
                  refine ⟨379150007434686730537531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8088533491939983584800661 379150007434686730537531)
                  ·
                    rfl

theorem cell23_6645528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 6].length) (baseStart_6645528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645528 prefixEnd_6645528 := by exact prefixLift 6645528
  have htrace : WordTrace (prefixWord ++ tailWord_6645528) baseStart_6645528 baseEnd_6645528 := by
    simpa [prefixWord, tailWord_6645528, baseEnd_6645528] using wordTrace_append hprefix tailTrace_6645528
  have hstable : (prefixWord ++ tailWord_6645528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645528).length < 2 ^ (prefixWord ++ tailWord_6645528).sum := by decide
  have hdescent : baseEnd_6645528 < baseStart_6645528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645588 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_6645588 : Nat := 118140960795 + 6645588 * 2 ^ 59
def prefixEnd_6645588 : Nat := 4983230072969 + 3 ^ 40 * 6645588 * 2
def baseEnd_6645588 : Nat := 1137460291917150113362501

theorem tailTrace_6645588 : CollatzResearch.WordTrace tailWord_6645588 prefixEnd_6645588 1137460291917150113362501 := by
  unfold tailWord_6645588
  simp only [CollatzResearch.WordTrace]
  refine ⟨121192253524088563457724709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161589671365451417943632945 121192253524088563457724709)
  ·
    refine ⟨22723547535766605648323383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121192253524088563457724709 22723547535766605648323383)
    ·
      refine ⟨34085321303649908472485075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723547535766605648323383 34085321303649908472485075)
      ·
        refine ⟨51127981955474862708727613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34085321303649908472485075 51127981955474862708727613)
        ·
          refine ⟨19172993233303073515772855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51127981955474862708727613 19172993233303073515772855)
          ·
            refine ⟨28759489849954610273659283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19172993233303073515772855 28759489849954610273659283)
            ·
              refine ⟨43139234774931915410488925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28759489849954610273659283 43139234774931915410488925)
              ·
                refine ⟨16177213040599468278933347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43139234774931915410488925 16177213040599468278933347)
                ·
                  refine ⟨24265819560899202418400021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16177213040599468278933347 24265819560899202418400021)
                  ·
                    refine ⟨1137460291917150113362501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24265819560899202418400021 1137460291917150113362501)
                    ·
                      rfl

theorem cell23_6645588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_6645588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645588 prefixEnd_6645588 := by exact prefixLift 6645588
  have htrace : WordTrace (prefixWord ++ tailWord_6645588) baseStart_6645588 baseEnd_6645588 := by
    simpa [prefixWord, tailWord_6645588, baseEnd_6645588] using wordTrace_append hprefix tailTrace_6645588
  have hstable : (prefixWord ++ tailWord_6645588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645588).length < 2 ^ (prefixWord ++ tailWord_6645588).sum := by decide
  have hdescent : baseEnd_6645588 < baseStart_6645588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645608 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6645608 : Nat := 118140960795 + 6645608 * 2 ^ 59
def prefixEnd_6645608 : Nat := 4983230072969 + 3 ^ 40 * 6645608 * 2
def baseEnd_6645608 : Nat := 3412391145364540261837411

theorem tailTrace_6645608 : CollatzResearch.WordTrace tailWord_6645608 prefixEnd_6645608 3412391145364540261837411 := by
  unfold tailWord_6645608
  simp only [CollatzResearch.WordTrace]
  refine ⟨121192618254052335165588739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161590157672069780220784985 121192618254052335165588739)
  ·
    refine ⟨181788927381078502748383109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121192618254052335165588739 181788927381078502748383109)
    ·
      refine ⟨34085423883952219265321833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181788927381078502748383109 34085423883952219265321833)
      ·
        refine ⟨25564067912964164448991375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34085423883952219265321833 25564067912964164448991375)
        ·
          refine ⟨38346101869446246673487063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25564067912964164448991375 38346101869446246673487063)
          ·
            refine ⟨57519152804169370010230595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38346101869446246673487063 57519152804169370010230595)
            ·
              refine ⟨86278729206254055015345893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57519152804169370010230595 86278729206254055015345893)
              ·
                refine ⟨16177261726172635315377355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86278729206254055015345893 16177261726172635315377355)
                ·
                  refine ⟨24265892589258952973066033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16177261726172635315377355 24265892589258952973066033)
                  ·
                    refine ⟨18199419441944214729799525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24265892589258952973066033 18199419441944214729799525)
                    ·
                      refine ⟨3412391145364540261837411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18199419441944214729799525 3412391145364540261837411)
                      ·
                        rfl

theorem cell23_6645608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6645608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645608 prefixEnd_6645608 := by exact prefixLift 6645608
  have htrace : WordTrace (prefixWord ++ tailWord_6645608) baseStart_6645608 baseEnd_6645608 := by
    simpa [prefixWord, tailWord_6645608, baseEnd_6645608] using wordTrace_append hprefix tailTrace_6645608
  have hstable : (prefixWord ++ tailWord_6645608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645608).length < 2 ^ (prefixWord ++ tailWord_6645608).sum := by decide
  have hdescent : baseEnd_6645608 < baseStart_6645608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645612 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_6645612 : Nat := 118140960795 + 6645612 * 2 ^ 59
def prefixEnd_6645612 : Nat := 4983230072969 + 3 ^ 40 * 6645612 * 2
def baseEnd_6645612 : Nat := 3412393199287158246187393

theorem tailTrace_6645612 : CollatzResearch.WordTrace tailWord_6645612 prefixEnd_6645612 3412393199287158246187393 := by
  unfold tailWord_6645612
  simp only [CollatzResearch.WordTrace]
  refine ⟨121192691200045089507161545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161590254933393452676215393 121192691200045089507161545)
  ·
    refine ⟨90894518400033817130371159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121192691200045089507161545 90894518400033817130371159)
    ·
      refine ⟨136341777600050725695556739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90894518400033817130371159 136341777600050725695556739)
      ·
        refine ⟨204512666400076088543335109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136341777600050725695556739 204512666400076088543335109)
        ·
          refine ⟨38346124950014266601875333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204512666400076088543335109 38346124950014266601875333)
          ·
            refine ⟨7189898428127674987851625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38346124950014266601875333 7189898428127674987851625)
            ·
              refine ⟨5392423821095756240888719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7189898428127674987851625 5392423821095756240888719)
              ·
                refine ⟨8088635731643634361333079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392423821095756240888719 8088635731643634361333079)
                ·
                  refine ⟨12132953597465451541999619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8088635731643634361333079 12132953597465451541999619)
                  ·
                    refine ⟨18199430396198177312999429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12132953597465451541999619 18199430396198177312999429)
                    ·
                      refine ⟨3412393199287158246187393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18199430396198177312999429 3412393199287158246187393)
                      ·
                        rfl

theorem cell23_6645612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_6645612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645612 prefixEnd_6645612 := by exact prefixLift 6645612
  have htrace : WordTrace (prefixWord ++ tailWord_6645612) baseStart_6645612 baseEnd_6645612 := by
    simpa [prefixWord, tailWord_6645612, baseEnd_6645612] using wordTrace_append hprefix tailTrace_6645612
  have hstable : (prefixWord ++ tailWord_6645612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645612).length < 2 ^ (prefixWord ++ tailWord_6645612).sum := by decide
  have hdescent : baseEnd_6645612 < baseStart_6645612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645622 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_6645622 : Nat := 118140960795 + 6645622 * 2 ^ 59
def prefixEnd_6645622 : Nat := 4983230072969 + 3 ^ 40 * 6645622 * 2
def baseEnd_6645622 : Nat := 1137466111364567735687449

theorem tailTrace_6645622 : CollatzResearch.WordTrace tailWord_6645622 prefixEnd_6645622 1137466111364567735687449 := by
  unfold tailWord_6645622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149109195628371920136695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161590498086702633814791413 15149109195628371920136695)
  ·
    refine ⟨22723663793442557880205043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15149109195628371920136695 22723663793442557880205043)
    ·
      refine ⟨34085495690163836820307565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723663793442557880205043 34085495690163836820307565)
      ·
        refine ⟨12782060883811438807615337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34085495690163836820307565 12782060883811438807615337)
        ·
          refine ⟨9586545662858579105711503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12782060883811438807615337 9586545662858579105711503)
          ·
            refine ⟨14379818494287868658567255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9586545662858579105711503 14379818494287868658567255)
            ·
              refine ⟨21569727741431802987850883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14379818494287868658567255 21569727741431802987850883)
              ·
                refine ⟨32354591612147704481776325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21569727741431802987850883 32354591612147704481776325)
                ·
                  refine ⟨6066485927277694590333061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32354591612147704481776325 6066485927277694590333061)
                  ·
                    refine ⟨1137466111364567735687449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066485927277694590333061 1137466111364567735687449)
                    ·
                      rfl

theorem cell23_6645622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_6645622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645622 prefixEnd_6645622 := by exact prefixLift 6645622
  have htrace : WordTrace (prefixWord ++ tailWord_6645622) baseStart_6645622 baseEnd_6645622 := by
    simpa [prefixWord, tailWord_6645622, baseEnd_6645622] using wordTrace_append hprefix tailTrace_6645622
  have hstable : (prefixWord ++ tailWord_6645622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645622).length < 2 ^ (prefixWord ++ tailWord_6645622).sum := by decide
  have hdescent : baseEnd_6645622 < baseStart_6645622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645642 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6645642 : Nat := 118140960795 + 6645642 * 2 ^ 59
def prefixEnd_6645642 : Nat := 4983230072969 + 3 ^ 40 * 6645642 * 2
def baseEnd_6645642 : Nat := 3412408603706793128812255

theorem tailTrace_6645642 : CollatzResearch.WordTrace tailWord_6645642 prefixEnd_6645642 3412408603706793128812255 := by
  unfold tailWord_6645642
  simp only [CollatzResearch.WordTrace]
  refine ⟨60596619147495373534478795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161590984393320996091943453 60596619147495373534478795)
  ·
    refine ⟨90894928721243060301718193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60596619147495373534478795 90894928721243060301718193)
    ·
      refine ⟨68171196540932295226288645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90894928721243060301718193 68171196540932295226288645)
      ·
        refine ⟨12782099351424805354929121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68171196540932295226288645 12782099351424805354929121)
        ·
          refine ⟨9586574513568604016196841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12782099351424805354929121 9586574513568604016196841)
          ·
            refine ⟨7189930885176453012147631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9586574513568604016196841 7189930885176453012147631)
            ·
              refine ⟨10784896327764679518221447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189930885176453012147631 10784896327764679518221447)
              ·
                refine ⟨16177344491647019277332171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784896327764679518221447 16177344491647019277332171)
                ·
                  refine ⟨24266016737470528915998257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16177344491647019277332171 24266016737470528915998257)
                  ·
                    refine ⟨18199512553102896686998693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24266016737470528915998257 18199512553102896686998693)
                    ·
                      refine ⟨3412408603706793128812255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18199512553102896686998693 3412408603706793128812255)
                      ·
                        rfl

theorem cell23_6645642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6645642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645642 prefixEnd_6645642 := by exact prefixLift 6645642
  have htrace : WordTrace (prefixWord ++ tailWord_6645642) baseStart_6645642 baseEnd_6645642 := by
    simpa [prefixWord, tailWord_6645642, baseEnd_6645642] using wordTrace_append hprefix tailTrace_6645642
  have hstable : (prefixWord ++ tailWord_6645642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645642).length < 2 ^ (prefixWord ++ tailWord_6645642).sum := by decide
  have hdescent : baseEnd_6645642 < baseStart_6645642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645651 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_6645651 : Nat := 118140960795 + 6645651 * 2 ^ 59
def prefixEnd_6645651 : Nat := 4983230072969 + 3 ^ 40 * 6645651 * 2
def baseEnd_6645651 : Nat := 3412413225032683593599713

theorem tailTrace_6645651 : CollatzResearch.WordTrace tailWord_6645651 prefixEnd_6645651 3412413225032683593599713 := by
  unfold tailWord_6645651
  simp only [CollatzResearch.WordTrace]
  refine ⟨242386804846948888674992807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161591203231299259116661871 242386804846948888674992807)
  ·
    refine ⟨363580207270423333012489211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242386804846948888674992807 363580207270423333012489211)
    ·
      refine ⟨545370310905634999518733817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363580207270423333012489211 545370310905634999518733817)
      ·
        refine ⟨409027733179226249639050363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545370310905634999518733817 409027733179226249639050363)
        ·
          refine ⟨613541599768839374458575545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409027733179226249639050363 613541599768839374458575545)
          ·
            refine ⟨460156199826629530843931659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613541599768839374458575545 460156199826629530843931659)
            ·
              refine ⟨690234299739944296265897489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460156199826629530843931659 690234299739944296265897489)
              ·
                refine ⟨517675724804958222199423117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690234299739944296265897489 517675724804958222199423117)
                ·
                  refine ⟨194128396801859333324783669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517675724804958222199423117 194128396801859333324783669)
                  ·
                    refine ⟨18199537200174312499198469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194128396801859333324783669 18199537200174312499198469)
                    ·
                      refine ⟨3412413225032683593599713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18199537200174312499198469 3412413225032683593599713)
                      ·
                        rfl

theorem cell23_6645651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_6645651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645651 prefixEnd_6645651 := by exact prefixLift 6645651
  have htrace : WordTrace (prefixWord ++ tailWord_6645651) baseStart_6645651 baseEnd_6645651 := by
    simpa [prefixWord, tailWord_6645651, baseEnd_6645651] using wordTrace_append hprefix tailTrace_6645651
  have hstable : (prefixWord ++ tailWord_6645651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645651).length < 2 ^ (prefixWord ++ tailWord_6645651).sum := by decide
  have hdescent : baseEnd_6645651 < baseStart_6645651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645658 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6645658 : Nat := 118140960795 + 6645658 * 2 ^ 59
def prefixEnd_6645658 : Nat := 4983230072969 + 3 ^ 40 * 6645658 * 2
def baseEnd_6645658 : Nat := 3412416819397265066212181

theorem tailTrace_6645658 : CollatzResearch.WordTrace tailWord_6645658 prefixEnd_6645658 3412416819397265066212181 := by
  unfold tailWord_6645658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60596765039480882217624407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161591373438615685913665085 60596765039480882217624407)
  ·
    refine ⟨90895147559221323326436611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60596765039480882217624407 90895147559221323326436611)
    ·
      refine ⟨136342721338831984989654917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90895147559221323326436611 136342721338831984989654917)
      ·
        refine ⟨25564260251030997185560297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136342721338831984989654917 25564260251030997185560297)
        ·
          refine ⟨19173195188273247889170223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25564260251030997185560297 19173195188273247889170223)
          ·
            refine ⟨28759792782409871833755335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19173195188273247889170223 28759792782409871833755335)
            ·
              refine ⟨43139689173614807750633003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28759792782409871833755335 43139689173614807750633003)
              ·
                refine ⟨64709533760422211625949505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43139689173614807750633003 64709533760422211625949505)
                ·
                  refine ⟨48532150320316658719462129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64709533760422211625949505 48532150320316658719462129)
                  ·
                    refine ⟨36399112740237494039596597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48532150320316658719462129 36399112740237494039596597)
                    ·
                      refine ⟨3412416819397265066212181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36399112740237494039596597 3412416819397265066212181)
                      ·
                        rfl

theorem cell23_6645658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6645658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645658 prefixEnd_6645658 := by exact prefixLift 6645658
  have htrace : WordTrace (prefixWord ++ tailWord_6645658) baseStart_6645658 baseEnd_6645658 := by
    simpa [prefixWord, tailWord_6645658, baseEnd_6645658] using wordTrace_append hprefix tailTrace_6645658
  have hstable : (prefixWord ++ tailWord_6645658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645658).length < 2 ^ (prefixWord ++ tailWord_6645658).sum := by decide
  have hdescent : baseEnd_6645658 < baseStart_6645658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645663 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 1, 2, 2]
def baseStart_6645663 : Nat := 118140960795 + 6645663 * 2 ^ 59
def prefixEnd_6645663 : Nat := 4983230072969 + 3 ^ 40 * 6645663 * 2
def baseEnd_6645663 : Nat := 3412419386800537546649659

theorem tailTrace_6645663 : CollatzResearch.WordTrace tailWord_6645663 prefixEnd_6645663 3412419386800537546649659 := by
  unfold tailWord_6645663
  simp only [CollatzResearch.WordTrace]
  refine ⟨242387242522905414724429643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161591495015270276482953095 242387242522905414724429643)
  ·
    refine ⟨363580863784358122086644465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242387242522905414724429643 363580863784358122086644465)
    ·
      refine ⟨272685647838268591564983349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363580863784358122086644465 272685647838268591564983349)
      ·
        refine ⟨25564279484837680459217189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272685647838268591564983349 25564279484837680459217189)
        ·
          refine ⟨4793302403407065086103223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25564279484837680459217189 4793302403407065086103223)
          ·
            refine ⟨7189953605110597629154835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793302403407065086103223 7189953605110597629154835)
            ·
              refine ⟨10784930407665896443732253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189953605110597629154835 10784930407665896443732253)
              ·
                refine ⟨4044348902874711166399595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10784930407665896443732253 4044348902874711166399595)
                ·
                  refine ⟨6066523354312066749599393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044348902874711166399595 6066523354312066749599393)
                  ·
                    refine ⟨4549892515734050062199545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066523354312066749599393 4549892515734050062199545)
                    ·
                      refine ⟨3412419386800537546649659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4549892515734050062199545 3412419386800537546649659)
                      ·
                        rfl

theorem cell23_6645663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_6645663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645663 prefixEnd_6645663 := by exact prefixLift 6645663
  have htrace : WordTrace (prefixWord ++ tailWord_6645663) baseStart_6645663 baseEnd_6645663 := by
    simpa [prefixWord, tailWord_6645663, baseEnd_6645663] using wordTrace_append hprefix tailTrace_6645663
  have hstable : (prefixWord ++ tailWord_6645663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645663).length < 2 ^ (prefixWord ++ tailWord_6645663).sum := by decide
  have hdescent : baseEnd_6645663 < baseStart_6645663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645688 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_6645688 : Nat := 118140960795 + 6645688 * 2 ^ 59
def prefixEnd_6645688 : Nat := 4983230072969 + 3 ^ 40 * 6645688 * 2
def baseEnd_6645688 : Nat := 3412432223816899948837043

theorem tailTrace_6645688 : CollatzResearch.WordTrace tailWord_6645688 prefixEnd_6645688 3412432223816899948837043 := by
  unfold tailWord_6645688
  simp only [CollatzResearch.WordTrace]
  refine ⟨121194077173907421997044859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161592102898543229329393145 121194077173907421997044859)
  ·
    refine ⟨181791115760861132995567289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121194077173907421997044859 181791115760861132995567289)
    ·
      refine ⟨136343336820645849746675467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181791115760861132995567289 136343336820645849746675467)
      ·
        refine ⟨204515005230968774620013201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136343336820645849746675467 204515005230968774620013201)
        ·
          refine ⟨153386253923226580965009901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204515005230968774620013201 153386253923226580965009901)
          ·
            refine ⟨57519845221209967861878713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153386253923226580965009901 57519845221209967861878713)
            ·
              refine ⟨43139883915907475896409035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57519845221209967861878713 43139883915907475896409035)
              ·
                refine ⟨64709825873861213844613553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43139883915907475896409035 64709825873861213844613553)
                ·
                  refine ⟨48532369405395910383460165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64709825873861213844613553 48532369405395910383460165)
                  ·
                    refine ⟨9099819263511733196898781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48532369405395910383460165 9099819263511733196898781)
                    ·
                      refine ⟨3412432223816899948837043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099819263511733196898781 3412432223816899948837043)
                      ·
                        rfl

theorem cell23_6645688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_6645688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645688 prefixEnd_6645688 := by exact prefixLift 6645688
  have htrace : WordTrace (prefixWord ++ tailWord_6645688) baseStart_6645688 baseEnd_6645688 := by
    simpa [prefixWord, tailWord_6645688, baseEnd_6645688] using wordTrace_append hprefix tailTrace_6645688
  have hstable : (prefixWord ++ tailWord_6645688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645688).length < 2 ^ (prefixWord ++ tailWord_6645688).sum := by decide
  have hdescent : baseEnd_6645688 < baseStart_6645688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645742 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_6645742 : Nat := 118140960795 + 6645742 * 2 ^ 59
def prefixEnd_6645742 : Nat := 4983230072969 + 3 ^ 40 * 6645742 * 2
def baseEnd_6645742 : Nat := 379162216863582526395755

theorem tailTrace_6645742 : CollatzResearch.WordTrace tailWord_6645742 prefixEnd_6645742 379162216863582526395755 := by
  unfold tailWord_6645742
  simp only [CollatzResearch.WordTrace]
  refine ⟨30298765486202401402069435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161593415926412807477703653 30298765486202401402069435)
  ·
    refine ⟨45448148229303602103104153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30298765486202401402069435 45448148229303602103104153)
    ·
      refine ⟨34086111171977701577328115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45448148229303602103104153 34086111171977701577328115)
      ·
        refine ⟨51129166757966552365992173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34086111171977701577328115 51129166757966552365992173)
        ·
          refine ⟨19173437534237457137247065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51129166757966552365992173 19173437534237457137247065)
          ·
            refine ⟨14380078150678092852935299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19173437534237457137247065 14380078150678092852935299)
            ·
              refine ⟨21570117226017139279402949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14380078150678092852935299 21570117226017139279402949)
              ·
                refine ⟨4044396979878213614888053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21570117226017139279402949 4044396979878213614888053)
                ·
                  refine ⟨379162216863582526395755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4044396979878213614888053 379162216863582526395755)
                  ·
                    rfl

theorem cell23_6645742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_6645742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645742 prefixEnd_6645742 := by exact prefixLift 6645742
  have htrace : WordTrace (prefixWord ++ tailWord_6645742) baseStart_6645742 baseEnd_6645742 := by
    simpa [prefixWord, tailWord_6645742, baseEnd_6645742] using wordTrace_append hprefix tailTrace_6645742
  have hstable : (prefixWord ++ tailWord_6645742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645742).length < 2 ^ (prefixWord ++ tailWord_6645742).sum := by decide
  have hdescent : baseEnd_6645742 < baseStart_6645742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645795 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3]
def baseStart_6645795 : Nat := 118140960795 + 6645795 * 2 ^ 59
def prefixEnd_6645795 : Nat := 4983230072969 + 3 ^ 40 * 6645795 * 2
def baseEnd_6645795 : Nat := 3412487166246931030199051

theorem tailTrace_6645795 : CollatzResearch.WordTrace tailWord_6645795 prefixEnd_6645795 3412487166246931030199051 := by
  unfold tailWord_6645795
  simp only [CollatzResearch.WordTrace]
  refine ⟨242392056958427201268234839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161594704638951467512156559 242392056958427201268234839)
  ·
    refine ⟨363588085437640801902352259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242392056958427201268234839 363588085437640801902352259)
    ·
      refine ⟨545382128156461202853528389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363588085437640801902352259 545382128156461202853528389)
      ·
        refine ⟨102259149029336475535036573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545382128156461202853528389 102259149029336475535036573)
        ·
          refine ⟨38347180886001178325638715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102259149029336475535036573 38347180886001178325638715)
          ·
            refine ⟨57520771329001767488458073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38347180886001178325638715 57520771329001767488458073)
            ·
              refine ⟨43140578496751325616343555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57520771329001767488458073 43140578496751325616343555)
              ·
                refine ⟨64710867745126988424515333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43140578496751325616343555 64710867745126988424515333)
                ·
                  refine ⟨12133287702211310329596625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64710867745126988424515333 12133287702211310329596625)
                  ·
                    refine ⟨9099965776658482747197469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12133287702211310329596625 9099965776658482747197469)
                    ·
                      refine ⟨3412487166246931030199051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9099965776658482747197469 3412487166246931030199051)
                      ·
                        rfl

theorem cell23_6645795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_6645795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645795 prefixEnd_6645795 := by exact prefixLift 6645795
  have htrace : WordTrace (prefixWord ++ tailWord_6645795) baseStart_6645795 baseEnd_6645795 := by
    simpa [prefixWord, tailWord_6645795, baseEnd_6645795] using wordTrace_append hprefix tailTrace_6645795
  have hstable : (prefixWord ++ tailWord_6645795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645795).length < 2 ^ (prefixWord ++ tailWord_6645795).sum := by decide
  have hdescent : baseEnd_6645795 < baseStart_6645795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645802 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_6645802 : Nat := 118140960795 + 6645802 * 2 ^ 59
def prefixEnd_6645802 : Nat := 4983230072969 + 3 ^ 40 * 6645802 * 2
def baseEnd_6645802 : Nat := 1137496920203837500937173

theorem tailTrace_6645802 : CollatzResearch.WordTrace tailWord_6645802 prefixEnd_6645802 1137496920203837500937173 := by
  unfold tailWord_6645802
  simp only [CollatzResearch.WordTrace]
  refine ⟨60598078067350460365934915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161594874846267894309159773 60598078067350460365934915)
  ·
    refine ⟨90897117101025690548902373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60598078067350460365934915 90897117101025690548902373)
    ·
      refine ⟨17043209456442316977919195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90897117101025690548902373 17043209456442316977919195)
      ·
        refine ⟨25564814184663475466878793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17043209456442316977919195 25564814184663475466878793)
        ·
          refine ⟨19173610638497606600159095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25564814184663475466878793 19173610638497606600159095)
          ·
            refine ⟨28760415957746409900238643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19173610638497606600159095 28760415957746409900238643)
            ·
              refine ⟨43140623936619614850357965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28760415957746409900238643 43140623936619614850357965)
              ·
                refine ⟨16177733976232355568884237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43140623936619614850357965 16177733976232355568884237)
                ·
                  refine ⟨6066650241087133338331589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16177733976232355568884237 6066650241087133338331589)
                  ·
                    refine ⟨1137496920203837500937173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066650241087133338331589 1137496920203837500937173)
                    ·
                      rfl

theorem cell23_6645802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_6645802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645802 prefixEnd_6645802 := by exact prefixLift 6645802
  have htrace : WordTrace (prefixWord ++ tailWord_6645802) baseStart_6645802 baseEnd_6645802 := by
    simpa [prefixWord, tailWord_6645802, baseEnd_6645802] using wordTrace_append hprefix tailTrace_6645802
  have hstable : (prefixWord ++ tailWord_6645802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645802).length < 2 ^ (prefixWord ++ tailWord_6645802).sum := by decide
  have hdescent : baseEnd_6645802 < baseStart_6645802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645818 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_6645818 : Nat := 118140960795 + 6645818 * 2 ^ 59
def prefixEnd_6645818 : Nat := 4983230072969 + 3 ^ 40 * 6645818 * 2
def baseEnd_6645818 : Nat := 3412498976301984440211445

theorem tailTrace_6645818 : CollatzResearch.WordTrace tailWord_6645818 prefixEnd_6645818 3412498976301984440211445 := by
  unfold tailWord_6645818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60598223959335969049080527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161595263891562584130881405 60598223959335969049080527)
  ·
    refine ⟨90897335939003953573620791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60598223959335969049080527 90897335939003953573620791)
    ·
      refine ⟨136346003908505930360431187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90897335939003953573620791 136346003908505930360431187)
      ·
        refine ⟨204519005862758895540646781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136346003908505930360431187 204519005862758895540646781)
        ·
          refine ⟨76694627198534585827742543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204519005862758895540646781 76694627198534585827742543)
          ·
            refine ⟨115041940797801878741613815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76694627198534585827742543 115041940797801878741613815)
            ·
              refine ⟨172562911196702818112420723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115041940797801878741613815 172562911196702818112420723)
              ·
                refine ⟨258844366795054227168631085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172562911196702818112420723 258844366795054227168631085)
                ·
                  refine ⟨97066637548145335188236657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258844366795054227168631085 97066637548145335188236657)
                  ·
                    refine ⟨72799978161109001391177493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97066637548145335188236657 72799978161109001391177493)
                    ·
                      refine ⟨3412498976301984440211445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72799978161109001391177493 3412498976301984440211445)
                      ·
                        rfl

theorem cell23_6645818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_6645818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645818 prefixEnd_6645818 := by exact prefixLift 6645818
  have htrace : WordTrace (prefixWord ++ tailWord_6645818) baseStart_6645818 baseEnd_6645818 := by
    simpa [prefixWord, tailWord_6645818, baseEnd_6645818] using wordTrace_append hprefix tailTrace_6645818
  have hstable : (prefixWord ++ tailWord_6645818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645818).length < 2 ^ (prefixWord ++ tailWord_6645818).sum := by decide
  have hdescent : baseEnd_6645818 < baseStart_6645818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645846 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6645846 : Nat := 118140960795 + 6645846 * 2 ^ 59
def prefixEnd_6645846 : Nat := 4983230072969 + 3 ^ 40 * 6645846 * 2
def baseEnd_6645846 : Nat := 3412513353760310330661317

theorem tailTrace_6645846 : CollatzResearch.WordTrace tailWord_6645846 prefixEnd_6645846 3412513353760310330661317 := by
  unfold tailWord_6645846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149619817577652311146337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161595944720828291318894261 15149619817577652311146337)
  ·
    refine ⟨11362214863183239233359753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15149619817577652311146337 11362214863183239233359753)
    ·
      refine ⟨8521661147387429425019815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11362214863183239233359753 8521661147387429425019815)
      ·
        refine ⟨12782491721081144137529723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521661147387429425019815 12782491721081144137529723)
        ·
          refine ⟨19173737581621716206294585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12782491721081144137529723 19173737581621716206294585)
          ·
            refine ⟨14380303186216287154720939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19173737581621716206294585 14380303186216287154720939)
            ·
              refine ⟨21570454779324430732081409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14380303186216287154720939 21570454779324430732081409)
              ·
                refine ⟨16177841084493323049061057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21570454779324430732081409 16177841084493323049061057)
                ·
                  refine ⟨12133380813369992286795793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16177841084493323049061057 12133380813369992286795793)
                  ·
                    refine ⟨9100035610027494215096845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12133380813369992286795793 9100035610027494215096845)
                    ·
                      refine ⟨3412513353760310330661317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100035610027494215096845 3412513353760310330661317)
                      ·
                        rfl

theorem cell23_6645846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6645846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645846 prefixEnd_6645846 := by exact prefixLift 6645846
  have htrace : WordTrace (prefixWord ++ tailWord_6645846) baseStart_6645846 baseEnd_6645846 := by
    simpa [prefixWord, tailWord_6645846, baseEnd_6645846] using wordTrace_append hprefix tailTrace_6645846
  have hstable : (prefixWord ++ tailWord_6645846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645846).length < 2 ^ (prefixWord ++ tailWord_6645846).sum := by decide
  have hdescent : baseEnd_6645846 < baseStart_6645846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645853 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6645853 : Nat := 118140960795 + 6645853 * 2 ^ 59
def prefixEnd_6645853 : Nat := 4983230072969 + 3 ^ 40 * 6645853 * 2
def baseEnd_6645853 : Nat := 1137505649374963934424595

theorem tailTrace_6645853 : CollatzResearch.WordTrace tailWord_6645853 prefixEnd_6645853 1137505649374963934424595 := by
  unfold tailWord_6645853
  simp only [CollatzResearch.WordTrace]
  refine ⟨242394172392217077173846213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161596114928144718115897475 242394172392217077173846213)
  ·
    refine ⟨45448907323540701970096165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242394172392217077173846213 45448907323540701970096165)
    ·
      refine ⟨8521670123163881619393031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45448907323540701970096165 8521670123163881619393031)
      ·
        refine ⟨12782505184745822429089547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521670123163881619393031 12782505184745822429089547)
        ·
          refine ⟨19173757777118733643634321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12782505184745822429089547 19173757777118733643634321)
          ·
            refine ⟨14380318332839050232725741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19173757777118733643634321 14380318332839050232725741)
            ·
              refine ⟨5392619374814643837272153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14380318332839050232725741 5392619374814643837272153)
              ·
                refine ⟨4044464531110982877954115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392619374814643837272153 4044464531110982877954115)
                ·
                  refine ⟨6066696796666474316931173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044464531110982877954115 6066696796666474316931173)
                  ·
                    refine ⟨1137505649374963934424595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6066696796666474316931173 1137505649374963934424595)
                    ·
                      rfl

theorem cell23_6645853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6645853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645853 prefixEnd_6645853 := by exact prefixLift 6645853
  have htrace : WordTrace (prefixWord ++ tailWord_6645853) baseStart_6645853 baseEnd_6645853 := by
    simpa [prefixWord, tailWord_6645853, baseEnd_6645853] using wordTrace_append hprefix tailTrace_6645853
  have hstable : (prefixWord ++ tailWord_6645853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645853).length < 2 ^ (prefixWord ++ tailWord_6645853).sum := by decide
  have hdescent : baseEnd_6645853 < baseStart_6645853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645859 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 1, 1, 3]
def baseStart_6645859 : Nat := 118140960795 + 6645859 * 2 ^ 59
def prefixEnd_6645859 : Nat := 4983230072969 + 3 ^ 40 * 6645859 * 2
def baseEnd_6645859 : Nat := 3412520029008818779798757

theorem tailTrace_6645859 : CollatzResearch.WordTrace tailWord_6645859 prefixEnd_6645859 3412520029008818779798757 := by
  unfold tailWord_6645859
  simp only [CollatzResearch.WordTrace]
  refine ⟨242394391230195340198564631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161596260820130226799043087 242394391230195340198564631)
  ·
    refine ⟨363591586845293010297846947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242394391230195340198564631 363591586845293010297846947)
    ·
      refine ⟨545387380267939515446770421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363591586845293010297846947 545387380267939515446770421)
      ·
        refine ⟨51130066900119329573134727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 545387380267939515446770421 51130066900119329573134727)
        ·
          refine ⟨76695100350178994359702091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51130066900119329573134727 76695100350178994359702091)
          ·
            refine ⟨115042650525268491539553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76695100350178994359702091 115042650525268491539553137)
            ·
              refine ⟨86281987893951368654664853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115042650525268491539553137 86281987893951368654664853)
              ·
                refine ⟨4044468182528970405687415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86281987893951368654664853 4044468182528970405687415)
                ·
                  refine ⟨6066702273793455608531123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044468182528970405687415 6066702273793455608531123)
                  ·
                    refine ⟨9100053410690183412796685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6066702273793455608531123 9100053410690183412796685)
                    ·
                      refine ⟨3412520029008818779798757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9100053410690183412796685 3412520029008818779798757)
                      ·
                        rfl

theorem cell23_6645859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_6645859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645859 prefixEnd_6645859 := by exact prefixLift 6645859
  have htrace : WordTrace (prefixWord ++ tailWord_6645859) baseStart_6645859 baseEnd_6645859 := by
    simpa [prefixWord, tailWord_6645859, baseEnd_6645859] using wordTrace_append hprefix tailTrace_6645859
  have hstable : (prefixWord ++ tailWord_6645859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645859).length < 2 ^ (prefixWord ++ tailWord_6645859).sum := by decide
  have hdescent : baseEnd_6645859 < baseStart_6645859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645865 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_6645865 : Nat := 118140960795 + 6645865 * 2 ^ 59
def prefixEnd_6645865 : Nat := 4983230072969 + 3 ^ 40 * 6645865 * 2
def baseEnd_6645865 : Nat := 3412523109892745756323729

theorem tailTrace_6645865 : CollatzResearch.WordTrace tailWord_6645865 prefixEnd_6645865 3412523109892745756323729 := by
  unfold tailWord_6645865
  simp only [CollatzResearch.WordTrace]
  refine ⟨242394610068173603223283049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161596406712115735482188699 242394610068173603223283049)
  ·
    refine ⟨181795957551130202417462287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242394610068173603223283049 181795957551130202417462287)
    ·
      refine ⟨272693936326695303626193431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181795957551130202417462287 272693936326695303626193431)
      ·
        refine ⟨409040904490042955439290147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272693936326695303626193431 409040904490042955439290147)
        ·
          refine ⟨613561356735064433158935221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409040904490042955439290147 613561356735064433158935221)
          ·
            refine ⟨57521377193912290608650177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613561356735064433158935221 57521377193912290608650177)
            ·
              refine ⟨43141032895434217956487633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57521377193912290608650177 43141032895434217956487633)
              ·
                refine ⟨32355774671575663467365725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43141032895434217956487633 32355774671575663467365725)
                ·
                  refine ⟨12133415501840873800262147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32355774671575663467365725 12133415501840873800262147)
                  ·
                    refine ⟨18200123252761310700393221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12133415501840873800262147 18200123252761310700393221)
                    ·
                      refine ⟨3412523109892745756323729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18200123252761310700393221 3412523109892745756323729)
                      ·
                        rfl

theorem cell23_6645865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_6645865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645865 prefixEnd_6645865 := by exact prefixLift 6645865
  have htrace : WordTrace (prefixWord ++ tailWord_6645865) baseStart_6645865 baseEnd_6645865 := by
    simpa [prefixWord, tailWord_6645865, baseEnd_6645865] using wordTrace_append hprefix tailTrace_6645865
  have hstable : (prefixWord ++ tailWord_6645865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645865).length < 2 ^ (prefixWord ++ tailWord_6645865).sum := by decide
  have hdescent : baseEnd_6645865 < baseStart_6645865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6645866 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_6645866 : Nat := 118140960795 + 6645866 * 2 ^ 59
def prefixEnd_6645866 : Nat := 4983230072969 + 3 ^ 40 * 6645866 * 2
def baseEnd_6645866 : Nat := 379169291485933361379025

theorem tailTrace_6645866 : CollatzResearch.WordTrace tailWord_6645866 prefixEnd_6645866 379169291485933361379025 := by
  unfold tailWord_6645866
  simp only [CollatzResearch.WordTrace]
  refine ⟨60598661635292495098517363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161596431027446653596046301 60598661635292495098517363)
  ·
    refine ⟨90897992452938742647776045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60598661635292495098517363 90897992452938742647776045)
    ·
      refine ⟨34086747169852028492916017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90897992452938742647776045 34086747169852028492916017)
      ·
        refine ⟨25565060377389021369687013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34086747169852028492916017 25565060377389021369687013)
        ·
          refine ⟨4793448820760441506816315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25565060377389021369687013 4793448820760441506816315)
          ·
            refine ⟨7190173231140662260224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793448820760441506816315 7190173231140662260224473)
            ·
              refine ⟨5392629923355496695168355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190173231140662260224473 5392629923355496695168355)
              ·
                refine ⟨8088944885033245042752533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392629923355496695168355 8088944885033245042752533)
                ·
                  refine ⟨379169291485933361379025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8088944885033245042752533 379169291485933361379025)
                  ·
                    rfl

theorem cell23_6645866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_6645866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6645866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6645866 prefixEnd_6645866 := by exact prefixLift 6645866
  have htrace : WordTrace (prefixWord ++ tailWord_6645866) baseStart_6645866 baseEnd_6645866 := by
    simpa [prefixWord, tailWord_6645866, baseEnd_6645866] using wordTrace_append hprefix tailTrace_6645866
  have hstable : (prefixWord ++ tailWord_6645866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6645866).length < 2 ^ (prefixWord ++ tailWord_6645866).sum := by decide
  have hdescent : baseEnd_6645866 < baseStart_6645866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6645866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
